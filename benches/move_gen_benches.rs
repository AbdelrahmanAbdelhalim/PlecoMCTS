#![feature(test)]
extern crate pleco;
extern crate test;
extern crate rand;

#[macro_use]
extern crate lazy_static;

use pleco::board::Board;
use pleco::engine::Searcher;
use pleco::tools::gen_rand_legal_board;
use pleco::templates::GenTypes;

use test::{black_box, Bencher};

lazy_static! {
    pub static ref RAND_BOARDS_NON_CHECKS: Vec<Board> = {
        let mut vec = Vec::new();
        vec.push(Board::default());
        for x in 1..13 {
            let b = gen_rand_legal_board();
            if !b.in_check() {
                vec.push(b);
            }
        }
        vec
    };

    pub static ref RAND_BOARDS_CHECKS: Vec<Board> = {
        let mut vec = Vec::new();
        for x in 0..13 {
            let b = gen_rand_legal_board();
            if b.in_check() {
                vec.push(b);
            }
        }
        vec
    };
}


#[bench]
fn bench_movegen_legal_all(b: &mut Bencher) {
    b.iter(|| {
        for board in RAND_BOARDS_NON_CHECKS.iter() {
            black_box(board.generate_moves());
        }
    })
}

#[bench]
fn bench_movegen_legal_captures(b: &mut Bencher) {
    b.iter(|| {
        for board in RAND_BOARDS_NON_CHECKS.iter() {
            black_box(board.generate_moves_of_type(GenTypes::Captures));
        }
    })
}

#[bench]
fn bench_movegen_legal_quiets(b: &mut Bencher) {
    b.iter(|| {
        for board in RAND_BOARDS_NON_CHECKS.iter() {
            black_box(board.generate_moves_of_type(GenTypes::Quiets));
        }
    })
}

#[bench]
fn bench_movegen_legal_quiet_checks(b: &mut Bencher) {
    b.iter(|| {
        for board in RAND_BOARDS_NON_CHECKS.iter() {
            black_box(board.generate_moves_of_type(GenTypes::QuietChecks));
        }
    })
}

#[bench]
fn bench_movegen_pslegal_all(b: &mut Bencher) {
    b.iter(|| {
        for board in RAND_BOARDS_NON_CHECKS.iter() {
            black_box(board.generate_pseudolegal_moves());
        }
    })
}

#[bench]
fn bench_movegen_pslegal_captures(b: &mut Bencher) {
    b.iter(|| {
        for board in RAND_BOARDS_NON_CHECKS.iter() {
            black_box(board.generate_pseudolegal_moves_of_type(GenTypes::Captures));
        }
    })
}

#[bench]
fn bench_movegen_pslegal_quiets(b: &mut Bencher) {
    b.iter(|| {
        for board in RAND_BOARDS_NON_CHECKS.iter() {
            black_box(board.generate_pseudolegal_moves_of_type(GenTypes::Quiets));
        }
    })
}

#[bench]
fn bench_movegen_pslegal_quiet_checks(b: &mut Bencher) {
    b.iter(|| {
        for board in RAND_BOARDS_NON_CHECKS.iter() {
            black_box(board.generate_pseudolegal_moves_of_type(GenTypes::QuietChecks));
        }
    })
}

#[bench]
fn  bench_movegen_in_check_legal_evasions(b: &mut Bencher) {
    b.iter(|| {
        for board in RAND_BOARDS_NON_CHECKS.iter() {
            black_box(board.generate_pseudolegal_moves());
        }
    })
}


#[bench]
fn bench_movegen_in_check_pslegal_evasions(b: &mut Bencher) {
    b.iter(|| {
        for board in RAND_BOARDS_NON_CHECKS.iter() {
            black_box(board.generate_moves());
        }
    })
}






