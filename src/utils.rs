use std::collections::HashSet;

pub fn slice_to_vec_of_owned(input: &[&str]) -> Vec<String> {
    input.iter().map(|x| x.to_string()).collect()
}

pub fn slice_to_set_of_owned(input: &[&str]) -> HashSet<String> {
    input.iter().map(|x| x.to_string()).collect()
}
