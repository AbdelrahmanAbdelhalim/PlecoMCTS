extern crate csv;
extern crate pleco;
extern crate pleco_engine;
extern crate statrs;
use csv::{Reader, StringRecord, Writer};
use pleco::core::Player;
use pleco::BitMove;
use pleco::Board;
use pleco_engine::engine::PlecoSearcher;
use pleco_engine::search::node;
use std::fs::File;
fn main() {
    let path =
        "/Users/screbz/dev/dissertation/masters/PlecoMCTS/pleco_engine/src/mate_in_1_puzzles.csv";
    let mut reader = Reader::from_path(path).unwrap();
    let mut records: Vec<StringRecord> = vec![];

    for result in reader.records() {
        let record = result.unwrap();
        records.push(record.into_iter().collect());
    }

    for (i, record) in records.iter().take(1).enumerate() {
        //setup
        let position = record.get(0).unwrap();
        let mut moves = record.get(1).unwrap();
        let mut temp_board: Board = Board::from_fen(position).unwrap();
        let side_to_move = temp_board.turn();
        let mut searcher_side: Player = Player::White;
        if side_to_move == Player::White {
            searcher_side = Player::Black;
        }
        let mut it = moves.split_whitespace();
        let first_move = it.next().unwrap();
        let correct_move = it.next().unwrap();
        temp_board.apply_uci_move(first_move);

        //search

        let new_fen = temp_board.fen();
        let mut mc_searcher =
            node::MctsSearcher::new_from_fen(node::TreePolicy::Thompson, searcher_side, &new_fen);
        let (visits, edges) = mc_searcher.search();

        let file_path = format!("/Users/screbz/dev/dissertation/masters/PlecoMCTS/scripts/mate_in_1/results_analysis/results_thompson/csvs/{}.csv", i);
        let mut wtr = Writer::from_path(file_path).unwrap();

        // Writing the header
        let mut header: Vec<String> = edges.into_iter().collect();
        header.push(new_fen.to_string());
        header.push(correct_move.to_string());
        wtr.write_record(&header).unwrap();

        for visit in visits {
            let mut data = vec![];
            for v in visit {
                data.push(v.to_string());
            }
            data.push(String::from("NaN"));
            data.push(String::from("NaN"));
            wtr.write_record(&data).unwrap();
        }
    }
}

mod tests {
    use super::*;
    #[test]
    fn read_csv() {
        main();
    }
}
