use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use lfu_cache::LfuMap;

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("insertion unbounded");
    for size in (1000..=10000).step_by(1000) {
        group.throughput(Throughput::Elements(size));
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            let mut cache = LfuMap::unbounded();
            b.iter(|| {
                for i in 0..size {
                    cache.insert(i, i);
                }
            });
        });
    }
    group.finish();

    let mut group = c.benchmark_group("insertion bounded");
    for size in (1000..=10000).step_by(1000) {
        group.throughput(Throughput::Elements(size));
        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
            let mut cache = LfuMap::with_capacity((size / 4) as usize);
            b.iter(|| {
                for i in 0..size {
                    cache.insert(i, i);
                }
            });
        });
    }
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
