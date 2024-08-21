use argh::FromArgs;
use simple_logger::{set_up_color_terminal, SimpleLogger};
use std::error::Error;

use flat::NodeBuilder;
use parse::starlark::StarlarkParser;

#[derive(FromArgs, Debug)]
/// Compile Stuff
struct Config {
    /// verbose flag
    #[argh(switch, short = 'v')]
    verbose: bool,

    /// compile file
    #[argh(positional)]
    inputs: Vec<String>,
}

fn main() -> Result<(), Box<dyn Error>> {
    set_up_color_terminal();
    SimpleLogger::new().init().unwrap();
    let config: Config = argh::from_env();

    if config.verbose {
        log::set_max_level(log::LevelFilter::Trace);
    } else {
        log::set_max_level(log::LevelFilter::Warn);
    }

    log::debug!("config: {:?}", config);
    let mut p: StarlarkParser = StarlarkParser::new();
    let mut b: NodeBuilder = NodeBuilder::new();

    for filename in config.inputs {
        let result = p.flatten(&filename, &mut b, true);
        b.spans.diagnostics_dump();
        let _ = result?;
    }
    Ok(())
}
