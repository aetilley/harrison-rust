use std::collections::HashSet;
use std::time::{Duration, Instant};

pub fn slice_to_vec_of_owned(input: &[&str]) -> Vec<String> {
    input.iter().map(|x| x.to_string()).collect()
}

pub fn slice_to_set_of_owned(input: &[&str]) -> HashSet<String> {
    input.iter().map(|x| x.to_string()).collect()
}

// Benchmarking utils
//

pub fn run_and_time<F, R>(mut func: F) -> R
where
    F: FnMut() -> R,
    // Run `func` `num_iter` times and report average time.
{
    let now = Instant::now();

    let result = func();

    let elapsed: Duration = now.elapsed();

    println!("Run time is {elapsed:?}.\n");

    result
}

pub fn run_repeatedly_and_average<F>(mut func: F, num_iters: u32)
where
    F: FnMut(),
    // Run `func` `num_iter` times and report average time.
{
    let now = Instant::now();

    for _ in 0..num_iters {
        func();
    }

    let elapsed: Duration = now.elapsed();
    let average: Duration = elapsed / num_iters;

    println!("Average time over a total of {num_iters} runs is {average:?}.\n");
}
