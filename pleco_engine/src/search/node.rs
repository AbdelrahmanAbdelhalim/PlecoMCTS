use consts::*;
use movepick::MovePicker;
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
use rand::Rng;
use root_moves::root_moves_list::RootMoveList;
use root_moves::RootMove;
use std::borrow::Borrow;
use std::cell::{Ref, RefCell, UnsafeCell};
use std::cmp::{max, min};
use std::collections::HashMap;
use std::fmt;
use std::fmt::{Debug, Error, Formatter};
use std::mem::drop;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::rc::{Rc, Weak};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread::current;
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
    board: Board,
    nodes: AtomicU64,
    root_node: Rc<RefCell<Node>>,
    side_played: Player,
    all_nodes_visit_counts: i32,
    // nof_iterations: usize,
}

impl MctsSearcher {
    fn new(side_played: Player) -> Self {
        MctsSearcher {
            board: Board::start_pos(),
            // board: Board::from_fen("3k4/8/8/8/8/4Q3/3K4/8 w - - 0 1").unwrap(),
            nodes: AtomicU64::new(0),
            // root_node: Rc::new(RefCell::new(Node::new_root())),
            root_node: Rc::new(RefCell::new(Node::new_root())),
            side_played: side_played,
            all_nodes_visit_counts: 0,
        }
    }

    fn new_from_fen(side_played: Player, fen: &str) -> Self {
        MctsSearcher {
            board: Board::start_pos(),
            // board: Board::from_fen("3k4/8/8/8/8/4Q3/3K4/8 w - - 0 1").unwrap(),
            nodes: AtomicU64::new(0),
            // root_node: Rc::new(RefCell::new(Node::new_root())),
            root_node: Rc::new(RefCell::new(Node::new_from_fen(fen))),
            side_played: side_played,
            all_nodes_visit_counts: 0,
        }
    }
    fn search(&mut self) {
        //always start at root node.
        let _transposition_table = TranspositionTable::new_num_entries(40000);
        let uct = &UCT::new(2f32.sqrt());
        let mut bigg = 0;
        //Main loop for x iterations
        for _ in 0..1000 {
            let mut current_node = self.root_node.clone();
            let mut _biggest_ucb: f32 = 0.0;
            let mut selected_edge_index: usize = 0;
            let mut final_leaf_ready = false;
            let mut stack: Vec<Rc<RefCell<Node>>> = vec![];

            //start selection until reaching a leaf node according to policy
            while !current_node.as_ref().borrow().is_leaf() || !final_leaf_ready {
                stack.push(Rc::clone(&current_node));

                //let binding to help with code compactness
                let mut current_node_ref = current_node.as_ref().borrow_mut();

                //check if node is terminal and set it to terminal and break
                if current_node_ref.check_is_terminal() {
                    current_node_ref.set_node_to_terminal();
                    break;
                }

                if current_node_ref.is_leaf() {
                    final_leaf_ready = true;
                }
                if !current_node_ref.edges_created {
                    current_node_ref.create_edges(Weak::new());
                }

                //selection
                (_biggest_ucb, selected_edge_index) = current_node_ref.select_child_uct(&uct);
                if current_node_ref.child_corresponding_to_edge_exists(selected_edge_index) {
                    let child_index =
                        current_node_ref.get_child_index_from_edge_index(selected_edge_index);
                    let c = current_node_ref.get_child(child_index);

                    //drop let binding
                    drop(current_node_ref);
                    current_node = c;
                    continue;
                } else {
                    break;
                }
            } //end of finding node

            //add one more node to the tree if the node is non terminal
            if !(current_node.as_ref().borrow().terminal_type == TerminalType::ENDOGFAME) {
                let new_child = current_node
                    .as_ref()
                    .borrow_mut()
                    .push_new_child(selected_edge_index);
                //add new child to the update stack
                stack.push(Rc::clone(&new_child));
                current_node = new_child;
            }

            //simulate
            let reward = current_node.borrow_mut().simulate(&self.side_played);
            //backprobagate
            for node in stack.into_iter() {
                node.as_ref().borrow_mut().wins += reward;
                node.as_ref().borrow_mut().increment_visits();
            }
            let mut biggest_visits = 0;
            let mut total_visits = 0;
            for (i, child) in self
                .root_node
                .as_ref()
                .borrow()
                .children
                .borrow()
                .iter()
                .enumerate()
            {
                let child = child.as_ref().borrow();
                if child.visits > biggest_visits {
                    biggest_visits = child.visits;
                    bigg = i;
                }
                total_visits += child.visits;
                print!("{} ", child.visits);
            }
            println!("end of iteration. total visits: {}", total_visits);
            total_visits = 0;
        }
        for edge in self.root_node.as_ref().borrow().edges.borrow().iter() {
            let edge = edge.as_ref().borrow();
            // println!("{}", edge._move);
            // dbg!(&edge);
            if edge.child_index == bigg {
                println!("top move: {}", edge._move);
            }
        }
    }

    fn set_edge_to_solid(&self, selected_edge_index: usize) {
        self.root_node.as_ref().borrow().edges.borrow_mut()[selected_edge_index]
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
    fn calc_uct_for_node(&self, child_wins: f32, child_visits: u16, parent_visits: u16) -> f32 {
        let avg_reward = child_wins as f32 / child_visits as f32;
        let exploration_term = (f32::ln(parent_visits as f32) / (child_visits as f32)).sqrt();
        let uct = avg_reward + self.uct_constant * exploration_term;
        return uct;
    }
}

struct Thompson {}

#[derive(PartialEq, Debug, Clone)]
#[repr(u8)]
enum TerminalType {
    NONTERMINAL = 0,
    ENDOGFAME = 1,
    LEAF = 2,
}

#[derive(Clone)]
struct Node {
    pub state: Board,
    pub visits: u16,
    pub wins: f32,
    pub is_root: bool,
    pub ply: u16,
    pub terminal_type: TerminalType,
    pub edges: RefCell<Vec<Rc<RefCell<Edge>>>>,
    pub edges_created: bool,
    // edge_index: usize,
    pub children: RefCell<Vec<Rc<RefCell<Node>>>>,
    pub parent: RefCell<Weak<Node>>,
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            // .field("state", &self.state)
            .field("children", &self.children)
            // .field("turn", &self.state.turn())
            .field("wins", &self.wins)
            .finish()
    }
}

impl Node {
    fn new(as_root: bool, terminal_type: TerminalType) -> Self {
        Node {
            state: Board::default(),
            visits: 0,
            wins: 0.0,
            is_root: as_root,
            ply: 0,
            terminal_type: terminal_type,
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

    fn new_from_fen(fen: &str) -> Self {
        Node {
            state: Board::from_fen(fen).unwrap(),
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

    fn create_edges(&mut self, parent: Weak<Node>) {
        let movelist = self.state.generate_moves();
        let edges = Edge::from_move_list(movelist, parent);
        self.edges = RefCell::new(edges);
        self.edges_created = true;
    }

    fn increment_visits(&mut self) {
        self.visits += 1;
    }

    fn set_node_to_terminal(&mut self) {
        self.terminal_type = TerminalType::ENDOGFAME;
    }

    fn is_leaf(&self) -> bool {
        self.terminal_type == TerminalType::LEAF
    }

    fn create_children_arr(&mut self, n: usize) {
        // self.children = RefCell::new(Vec::with_capacity(n));
    }

    fn child_corresponding_to_edge_exists(&self, selected_edge_index: usize) -> bool {
        return self
            .edges
            .borrow()
            .get(selected_edge_index)
            .unwrap()
            .as_ref()
            .borrow()
            .solid_child;
    }

    fn check_is_terminal(&mut self) -> bool {
        let movelist = self.state.generate_moves();
        if movelist.len() == 0 {
            return true;
        }
        return false;
    }

    fn get_child(&self, child_index: usize) -> Rc<RefCell<Node>> {
        Rc::clone(self.borrow().children.borrow().get(child_index).unwrap())
    }

    fn get_child_index_from_edge_index(&self, selected_edge_index: usize) -> usize {
        let child_index = self
            .edges
            .borrow()
            .get(selected_edge_index)
            .unwrap()
            .as_ref()
            .borrow()
            .child_index;
        child_index
    }
    fn push_new_child(&mut self, selected_index: usize) -> Rc<RefCell<Node>> {
        let edge = self.edges.borrow();
        let edge = edge.get(selected_index).unwrap().as_ref();
        let mv = edge.borrow()._move;
        edge.borrow_mut().solid_child = true;

        let mut children = self.children.borrow_mut();
        children.push(Rc::new(RefCell::new(Node::new(false, TerminalType::LEAF))));
        let mut new_child = children.last().unwrap().borrow_mut();
        new_child.state = self.state.clone();
        new_child.state.apply_move(mv);

        edge.borrow_mut().child_index = children.len() - 1;
        self.terminal_type = TerminalType::NONTERMINAL;

        return Rc::clone(children.last().unwrap());
    }

    fn simulate(&mut self, side_played: &Player) -> f32 {
        //simulation
        // let board_pos = &mut kids.get(child_index).unwrap().borrow_mut().state;
        let board_pos = &mut self.state;
        let mut prng = rand::thread_rng();
        let mut simulation_depth = 0;
        let mut reward: f32 = 0.0;

        //todo: Truncate search (first optimization)
        'simloop: loop {
            if board_pos.checkmate() {
                if *side_played == board_pos.turn() {
                    reward = 0.0;
                    break 'simloop;
                } else {
                    reward = 1.0;
                    break 'simloop;
                }
            } else if board_pos.stalemate()
                || board_pos.fifty_move_rule()
                || board_pos.threefold_repetition()
            {
                reward = 0.5;
                break 'simloop;
            }
            let moves = board_pos.generate_moves();
            let random_index = prng.gen_range(0..moves.len());
            let random_move = moves.get(random_index).unwrap();
            simulation_depth += 1;
            board_pos.apply_move(*random_move);
        }

        while simulation_depth > 0 {
            board_pos.undo_move();
            simulation_depth -= 1;
        }
        return reward;
    }

    fn select_child_uct(&mut self, uct: &UCT) -> (f32, usize) {
        if !self.edges_created {
            self.create_edges(Weak::new());
        }
        let mut biggest_ucb = 0.0;
        let mut selected_edge_index = 0;
        for (i, edge) in self.edges.borrow().iter().enumerate() {
            let edge = edge.as_ref().borrow();
            if !edge.solid_child {
                let uct_for_node = 3.4028235e+38;
                if uct_for_node > biggest_ucb {
                    selected_edge_index = i;
                    biggest_ucb = uct_for_node;
                }
            } else {
                let c = self.children.borrow();
                let child_index = edge.child_index;
                let child = c.get(child_index).unwrap().as_ref().borrow();
                let parent_visits = self.visits;
                let child_visits = child.visits;
                let child_wins = child.wins;
                let uct_for_node = uct.calc_uct_for_node(child_wins, child_visits, parent_visits);
                if uct_for_node > biggest_ucb {
                    selected_edge_index = i;
                    biggest_ucb = uct_for_node;
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
        if movelist.is_empty() {
            panic!("Movelist is empty");
        }
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
