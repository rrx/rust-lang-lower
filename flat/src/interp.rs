use crate::ICodeModule;

pub struct Interp {}

impl Interp {
    pub fn new() -> Self {
        Self {}
    }
}

pub fn interp<'c>(shared: &[String], m: &dyn ICodeModule, libpath: &str) -> i32 {
    let paths = shared
        .iter()
        .map(|s| {
            let mut path = format!("{}/{}.so", libpath, s);
            path.push('\0');
            path
        })
        .collect::<Vec<_>>();

    let shared = paths.iter().map(|p| p.as_str()).collect::<Vec<_>>();

    let mut result: i32 = -1;
    println!("exec: {}", result);
    result
}
