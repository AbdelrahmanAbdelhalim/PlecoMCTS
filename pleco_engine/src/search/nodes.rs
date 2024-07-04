use pleco::board::movegen::{MoveGen, PseudoLegal};
use pleco::core::mono_traits::QuietChecksGenType;
use pleco::core::score::*;
use pleco::helper::prelude::*;
use pleco::tools::pleco_arc::Arc;
use pleco::tools::tt::*;
use pleco::tools::PreFetchable;
use pleco::MoveList;
use pleco::{board, core::*};
use pleco::{BitMove, Board, SQ};
use std::cell::{RefCell, UnsafeCell};
use std::cmp::{max, min};
use std::collections::HashMap;
use std::fmt::{Debug, Error, Formatter};
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::rc::{Rc, Weak};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::{default, mem};

use consts::*;
use movepick::MovePicker;
use rand::Rng;
use root_moves::root_moves_list::RootMoveList;
use root_moves::RootMove;
use sync::{GuardedBool, LockLatch};
use tables::material::Material;
use tables::pawn_table::PawnTable;
use tables::prelude::*;
use threadpool::threadpool;
use time::time_management::TimeManager;
use {MAX_PLY, THREAD_STACK_SIZE};

use time::uci_timer::*;

struct MctsSearcher {
    // search data
    pub board: Board,
    pub nodes: AtomicU64,
    pub root_node: RefCell<Node>,
    pub side_played: Player,
    // pub nof_iterations: usize,
}

impl MctsSearcher {
    fn new(side_played: Player) -> Self {
        MctsSearcher {
            board: Board::start_pos(),
            nodes: AtomicU64::new(0),
            root_node: RefCell::new(Node::new_root()),
            side_played: side_played,
        }
    }

    fn search(&mut self) {
        //always start at root node.
        let transposition_table = TranspositionTable::new_num_entries(40000);
        self.root_node.borrow_mut().increment_visits();
        if !self.root_node.borrow().edges_created {
            self.root_node.borrow_mut().create_edges(Weak::new());
            // root_node.children = RefCell::new(vec![root_node.edges.borrow().len()]);
        }

        //Selection
        let uct = &UCT::new(2f32.sqrt());
        let mut biggest_ucb: f32 = 0.0;
        let mut selected_edge_index: usize = 0;
        (biggest_ucb, selected_edge_index) = self.root_node.borrow().select_child_uct(&uct);
        self.root_node
            .borrow_mut()
            .solidify_child(selected_edge_index);
        self.root_node
            .borrow_mut()
            .push_new_child(selected_edge_index);
        let reward = self
            .root_node
            .borrow_mut()
            .simulate(selected_edge_index, &self.side_played);

        //otherwise recurse
        dbg!(self.root_node.borrow());
    }

    fn set_edge_to_solid(&self, selected_edge_index: usize) {
        self.root_node.borrow().edges.borrow_mut()[selected_edge_index]
            .borrow_mut()
            .solid_child = true;
    }
}

enum TreePolicy {
    UCT(UCT),
    Thompson(Thompson),
}

#[derive(Debug)]
struct UCT {
    uct_constant: f32,
}

impl UCT {
    pub fn new(uct_constant: f32) -> Self {
        Self {
            uct_constant: uct_constant,
        }
    }
    fn calc_uct_for_node(&self, qsa: f32, ns: u16, nsa: u16) -> f32 {
        qsa + (self.uct_constant * (f32::ln(ns as f32) / (1.0 + nsa as f32)))
    }
}

struct Thompson {}

#[derive(PartialEq, Debug)]
#[repr(u8)]
enum TerminalType {
    NONTERMINAL = 0,
    ENDOGFAME = 1,
    LEAF = 2,
}

#[derive(Debug)]
struct Node {
    pub state: Board,
    pub visits: u16,
    pub wins: f32,
    pub is_root: bool,
    pub ply: u16,
    pub terminal_type: TerminalType,
    pub edges: RefCell<Vec<Rc<RefCell<Edge>>>>,
    pub edges_created: bool,
    // pub edge_index: usize,
    pub children: RefCell<Vec<Rc<RefCell<Node>>>>,
    pub parent: RefCell<Weak<Node>>,
}

impl Node {
    fn new(as_root: bool) -> Self {
        Node {
            state: Board::default(),
            visits: 0,
            wins: 0.0,
            is_root: as_root,
            ply: 0,
            terminal_type: TerminalType::NONTERMINAL,
            edges: RefCell::new(Vec::new()),
            edges_created: false,
            // edge_index: 0,
            children: RefCell::new(Vec::new()),
            parent: RefCell::new(Weak::new()),
        }
    }

    fn new_root() -> Self {
        Node {
            state: Board::default(),
            visits: 0,
            wins: 0.0,
            is_root: true,
            ply: 0,
            terminal_type: TerminalType::LEAF,
            edges: RefCell::new(Vec::new()),
            edges_created: false,
            // edge_index: 0,
            children: RefCell::new(Vec::new()),
            parent: RefCell::new(Weak::new()),
        }
    }

//    fn new_child(self) {
//         let mut new_child = Node::new(false);
//         *new_child.parent.borrow_mut() = Rc::downgrade(&Rc::new(self));
//         self.children.borrow_mut().push(new_child);
//    }

    fn create_edges(&mut self, parent: Weak<Node>) {
        let movelist = self.state.generate_moves();
        let edges = Edge::from_move_list(movelist, parent);
        self.edges = RefCell::new(edges);
        self.edges_created = true;
    }

    fn increment_visits(&mut self) {
        self.visits += 1;
    }

    fn is_leaf(&self) -> bool {
        self.terminal_type == TerminalType::LEAF
    }

    fn create_children_arr(&mut self, n: usize) {
        self.children = RefCell::new(Vec::with_capacity(n));
    }

    fn solidify_child(&mut self, selected_index: usize) {
        let new_node = Node::new(false);
        self.children
            .borrow_mut()
            .push(Rc::new(RefCell::new(new_node)));
        self.edges.borrow_mut()[selected_index]
            .borrow_mut()
            .child_index = self.children.borrow().len();
    }

    fn push_new_child(&mut self, selected_index: usize) {
        self.children
            .borrow_mut()
            .push(Rc::new(RefCell::new(Node::new(false))));
        self.children.borrow_mut()[0]
            .borrow_mut()
            .state
            .apply_move(self.edges.borrow()[selected_index].borrow()._move);
    }

    fn simulate(&mut self, child_index: usize, side_played: &Player) -> f32 {
        //simulation
        let kids = self.children.borrow_mut();
        let board_pos = &mut kids[child_index].borrow_mut().state;
        let mut prng = rand::thread_rng();
        let mut simulation_depth = 0;
        let mut result: f32 = 0.0;
        while !board_pos.checkmate()
            && !board_pos.fifty_move_rule()
            && !board_pos.stalemate()
            && !board_pos.threefold_repetition()
        {
            board_pos.pretty_print();
            let moves = board_pos.generate_moves();
            let random_index = prng.gen_range(0..moves.len());
            let random_move = moves[random_index];
            simulation_depth += 1;
            board_pos.apply_move(random_move);
        }
        while simulation_depth > 0 {
            board_pos.undo_move();
            simulation_depth -= 1;
        }
        if board_pos.checkmate() {
            if *side_played == board_pos.turn() {
                result = 0.0;
            }
        } else if board_pos.stalemate()
            || board_pos.fifty_move_rule()
            || board_pos.threefold_repetition()
        {
            result = 0.5;
        } else {
            result = 1.0;
        }
        //backpropagation
        self.wins += result;
        return result;
    }

    fn select_child_uct(&self, uct: &UCT) -> (f32, usize) {
        let mut biggest_ucb = 0.0;
        let mut selected_edge_index = 0;
        if self.is_leaf() {
            for (i, edge) in self.edges.borrow().iter().enumerate() {
                let edge = edge.borrow();
                if !edge.solid_child {
                    let qsa = 0.0;
                    let nsa = self.visits;
                    let ns = 1;
                    let uct_for_node = uct.calc_uct_for_node(qsa, ns, nsa);
                    if uct_for_node > biggest_ucb {
                        selected_edge_index = i;
                        biggest_ucb = uct_for_node;
                    }
                } else {
                    let c = &self.children.borrow()[i];
                    let child = c.borrow();
                    // Use the `child` variable instead of the borrowed value directly
                    let ns = self.visits;
                    let nsa = edge.passes;
                    let qsa: f32 = (child.wins / nsa as f32) as f32;
                    let uct_for_node = uct.calc_uct_for_node(qsa, ns, nsa);
                    if uct_for_node > biggest_ucb {
                        selected_edge_index = i;
                        biggest_ucb = uct_for_node;
                    }
                }
            }
        }
        (biggest_ucb, selected_edge_index)
    }
}

#[derive(Debug)]
struct Edge {
    pub _move: BitMove,
    pub passes: u16,
    pub solid_child: bool,
    pub child_index: usize,
}

impl Edge {
    fn new(_move: BitMove, parent: Weak<Node>) -> Self {
        Self {
            _move: _move,
            passes: 0,
            solid_child: false,
            child_index: 0,
        }
    }

    fn from_move_list(movelist: MoveList, parent: Weak<Node>) -> Vec<Rc<RefCell<Edge>>> {
        let mut list: Vec<Rc<RefCell<Self>>> = vec![];
        for _move in movelist.into_iter() {
            list.push(Rc::new(RefCell::new(Self::new(_move, parent.clone()))));
        }
        list
    }
}

mod tests {
    use super::*;
    #[test]
    fn create_child() {
        let mut searcher = MctsSearcher::new(Player::White);
        searcher.search();
    }
}
