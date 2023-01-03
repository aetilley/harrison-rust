
pub fn to_vec_of_owned(input: Vec<&str>) -> Vec<String> {
        input.iter().map(|x| x.to_string()).collect()
}

