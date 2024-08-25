use compile_core::Literal;
use flat::block_format::LCodeIterator;
use flat::{Blockify, CodeOffset, CodeRow, ICodeModule, LCode, NodeBuilder, ValueId};

fn format_html_header() -> String {
    let mut s = String::new();
    s.push_str("<thead><tr>");
    for row in CodeRow::header() {
        s.push_str(&format!("<td>{}</td>", row));
    }
    s
}

fn format_html_row(row: &CodeRow) -> String {
    let mut s = String::new();
    s.push_str(&format!("<tr class=\"s{}\">", row.span_id));
    s.push_str(&format!("<td>{}</td>", row.pos));
    //s.push_str(&format!("<td>{}</td>", row.next));
    //s.push_str(&format!("<td>{}</td>", row.prev));
    s.push_str(&format!("<td>{}</td>", row.value));
    s.push_str(&format!("<td>{}</td>", row.ty));
    s.push_str(&format!("<td>{}</td>", row.mem));
    s.push_str(&format!("<td>{}</td>", row.name));
    s.push_str(&format!("<td>{}</td>", row.span_id));
    s.push_str(&format!("<td>{}</td>", row.scope_id));
    s.push_str(&format!("<td>{}</td>", row.block_id));
    s.push_str(&format!("<td>{}</td>", row.term));
    s.push_str("</tr>");
    s
}

pub fn code_to_string(v: ValueId, blockify: &Blockify, b: &NodeBuilder) -> String {
    let code = blockify.get_code(v);
    match code {
        LCode::Declare => {
            let code_str = b.labels.r(blockify.get_name(v.into()).unwrap());
            format!("declare {}: {:?}", code_str, blockify.get_type(v.into()))
        }

        LCode::DeclareFunction(maybe_entry) => {
            let code_str = b.labels.r(blockify.get_name(v.into()).unwrap());
            if let Some(entry_id) = maybe_entry {
                format!("declare_function({},{:?})", code_str, entry_id)
            } else {
                format!("declare_function({})", code_str)
            }
        }

        LCode::Label(args, kwargs) => {
            if let Some(key) = blockify.get_name(v.into()) {
                format!("label({}, {}, {})", b.labels.r(key), args, kwargs,)
            } else {
                format!("label(-, {}, {})", args, kwargs,)
            }
        }

        //LCode::Goto(block_id) => {
        //format!("goto({})", b.labels.r((*block_id).into()))
        //}
        LCode::Jump(value_id, args) => {
            format!("jump({:?}, {})", value_id, args,)
        }

        LCode::Const(Literal::String(s)) => {
            format!("String({})", s)
        }

        LCode::Ternary(c, x, y) => {
            format!("Ternary({},{},{})", c.index(), x, y)
        }

        LCode::Branch(c, x, y) => {
            format!("Branch({:?},{},{})", c, x, y)
        }

        _ => {
            format!("{:?}", code)
        }
    }
}

pub fn get_code_rows(blockify: &Blockify, b: &NodeBuilder) -> Vec<CodeRow> {
    let mut out = vec![];
    let iter = LCodeIterator::new(blockify);
    for (_i, v) in iter.enumerate() {
        let row = blockify.get_code_row(v, b);
        let _code = blockify.get_code(v);
        out.push(row);
    }
    out
}

pub fn get_json(blockify: &Blockify, b: &NodeBuilder) -> String {
    let out = get_code_rows(blockify, b);
    serde_json::to_string(&out).unwrap()
}

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
    println!("{}", s);
    std::fs::write(filename, s).unwrap();
}
