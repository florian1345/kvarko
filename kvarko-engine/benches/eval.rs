use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkGroup};
use criterion::measurement::WallTime;

use kvarko_engine::{
    DEFAULT_QUIESCENCE_SEARCH_TTABLE_BITS,
    DEFAULT_TREE_SEARCH_TTABLE_BITS,
    KvarkoEngine,
    StateEvaluatingController,
    StateEvaluator
};
use kvarko_engine::depth::{Depth, IterativeDeepeningToDepth};

use kvarko_model::hash::ZobristHasher;
use kvarko_model::state::State;

type Kvarko =
    StateEvaluatingController<KvarkoEngine<ZobristHasher<u64>, IterativeDeepeningToDepth>>;

fn kvarko(depth: Depth) -> Kvarko {
    kvarko_engine::kvarko_engine_with_ttable_bits_and_depth_strategy(
        IterativeDeepeningToDepth::new(depth),
        None,
        DEFAULT_TREE_SEARCH_TTABLE_BITS,
        DEFAULT_QUIESCENCE_SEARCH_TTABLE_BITS)
}

fn bench_opening_with_depth(history: &str, depth: Depth,
        benchmark_group: &mut BenchmarkGroup<WallTime>) {
    let mut state = State::from_algebraic_history(history.split(' ')).unwrap();
    let mut kvarko = kvarko(depth);

    benchmark_group.bench_function(format!("depth {depth}"),
        |bencher| bencher.iter(|| kvarko.evaluate_state(&mut state)));
}

struct BenchmarkGroupData {
    id: &'static str,
    history: &'static str,
    depths: &'static [Depth]
}

const BENCHMARK_GROUP_DATAS: &[BenchmarkGroupData] = &[
    BenchmarkGroupData {
        id: "Spanish Opening",
        history: "e4 e5 Nf3 Nc6 Bb5",
        depths: &[5, 6, 7]
    },
    BenchmarkGroupData {
        id: "Queens Gambit Declined Main Line",
        history: "d4 d5 c4 e6 Nc3 Nf6 Bg5 Be7",
        depths: &[5, 6, 7]
    },
    BenchmarkGroupData {
        id: "Open Sicilian Knight Exchange",
        history: "e4 c5 Nf3 Nc6 d4 cxd4 Nxd4 Nxd4 Qxd4",
        depths: &[5, 6, 7]
    },
    BenchmarkGroupData {
        id: "Complicated Midgame",
        history: "e4 e5 Nf3 Nc6 Bc4 Bc5 c3 Nf6 d3 d6 O-O O-O Bg5 h6 Bh4 Bb6 Nbd2 g5 Bg3 a5 Bb3 Ba7 \
            Nc4 Bg4 h3 Bh5 Ba4 Rb8 Ne3 Bg6 Bc2 Qd7 Qd2 Rbe8 Rae1",
        depths: &[5, 6, 7]
    },
    BenchmarkGroupData {
        id: "Midgame Some Exchanges",
        history: "e4 c5 Nf3 d6 Nc3 a6 d4 cxd4 Nxd4 Nf6 f3 e6 a3 Nc6 Be3 d5 exd5 Nxd5 Nxd5 exd5 Qd2",
        depths: &[5, 6, 7]
    },
    BenchmarkGroupData {
        id: "Simplified Midgame",
        history: "e4 e5 d4 exd4 Nf3 Bb4+ Bd2 Bxd2+ Nbxd2 c5 c3 dxc3 bxc3 Ne7 Nc4 d5 Ne3 dxe4 Qxd8+ \
            Kxd8 Ng5 Rf8 Nxh7 Re8 Ng5 f5 O-O-O+ Kc7 g4 f4 Nc4 Bxg4 Bh3 Bxh3 Nxh3",
        depths: &[6, 7, 8]
    },
    BenchmarkGroupData {
        id: "Bishop And Rooks Endgame",
        history: "e4 d5 exd5 Qxd5 Nc3 Qa5 d4 c6 Bd2 Nf6 Bd3 Bg4 Ne4 Bxd1 Nxf6+ gxf6 Bxa5 Bh5 f4 e6 \
            f5 Na6 a3 b6 Bxa6 bxa5 Bb7 Rb8 Bxc6+ Ke7 Ne2 Bxe2 Kxe2 Rxb2 Ba4 Bh6",
        depths: &[6, 7, 8]
    },
    BenchmarkGroupData {
        id: "Knight And Bishop Endgame",
        history: "e4 e5 f4 exf4 Nf3 d6 d4 g5 Nc3 h6 Qd3 Bg7 Bd2 Nc6 O-O-O Nge7 h3 Ng6 Re1 O-O g3 \
            fxg3 Ne2 Qf6 Rg1 Re8 Rxg3 a5 a3 Bd7 Bg2 Qe6 Nc3 Nb4 axb4 axb4 Nb1 Ra1 b3 Qf6 Rf1 Qd8 \
            Nxg5 hxg5 Bxb4 Bh6 Qd2 Qa8 Bc3 Kg7 d5+ Re5 Bxa1 Qxa1 b4 f5 Ra3 Qxa3+ Nxa3 g4 exf5 \
            Bxd2+ Kxd2 Nh4 Nc4 Rxf5 Rxf5 Bxf5 hxg4 Bxg4",
        depths: &[8, 9, 10]
    },
    BenchmarkGroupData {
        id: "Queen Vs Rooks Endgame",
        history: "d4 Nf6 c4 e5 dxe5 Ng4 e4 Nxe5 f4 Nec6 Nc3 Bc5 Qg4 O-O f5 Re8 Nf3 d5 cxd5 Nd4 \
            Nxd4 Bxd4 Bd3 Nd7 Bg5 Nf6 Bxf6 Qxf6 O-O-O Bxc3 bxc3 Bd7 Kb2 Ba4 Rd2 b5 Re2 Re5 Bc2 \
            Bxc2 Kxc2 Qd6 Rd1 Rae8 Rd4 c6 dxc6 Qxc6 Re3 a5 Rg3 g6 fxg6 hxg6 Qd7 Qc5 Rf3 R8e7 \
            Qd8+ Kg7 Rd6 Rxe4 Rxg6+ fxg6 Qf8+ Kh7 Rh3+ Qh5 Rxh5+ gxh5",
        depths: &[7, 8, 9]
    }
];

fn criterion_benchmark(c: &mut Criterion) {
    for benchmark_group_data in BENCHMARK_GROUP_DATAS {
        let mut benchmark_group = c.benchmark_group(benchmark_group_data.id);
        benchmark_group
            .sample_size(10)
            .measurement_time(Duration::from_secs(20));

        for &depth in benchmark_group_data.depths {
            bench_opening_with_depth(benchmark_group_data.history, depth, &mut benchmark_group);
        }
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
