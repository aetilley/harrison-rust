use std::collections::HashSet;

pub fn to_vec_of_owned(input: Vec<&str>) -> Vec<String> {
    input.iter().map(|x| x.to_string()).collect()
}

pub fn to_set_of_owned(input: Vec<&str>) -> HashSet<String> {
    input.iter().map(|x| x.to_string()).collect()
}
