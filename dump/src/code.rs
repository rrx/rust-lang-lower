use flat::{CodeOffset, ICodeModule, NodeBuilder, ValueId};

pub fn save_graph(blockify: &dyn ICodeModule, filename: &str, b: &NodeBuilder) {
    use petgraph::dot::{Config, Dot};
    let cfg = blockify.get_graph(ValueId::new(0), None, b);
    let s = format!(
        "{:?}",
        Dot::with_attr_getters(
            &cfg.g,
            &[Config::EdgeNoLabel, Config::NodeNoLabel],
            &|_, _er| String::new(),
            &|_, (_index, data)| {
                match data.code_offset {
                    CodeOffset::Value(value_id) => {
                        format!(
                            "label = \"V{}:{}\" shape={:?}",
                            value_id.index(),
                            &data.name,
                            &data.ty.to_string()
                        )
                    }
                    CodeOffset::Block(block_id) => {
                        format!(
                            "label = \"B{}:{}\" shape={:?}",
                            block_id.index(),
                            &data.name,
                            &data.ty.to_string()
                        )
                    }
                    _ => unimplemented!(),
                }
            }
        )
    );
    println!("saved graph {:?}", filename);
    //println!("{}", s);
    std::fs::write(filename, s).unwrap();
}
