use flat::block_format::{CodeRow, LCodeIterator};
use flat::graph::{Node, CFG};
use flat::{Blockify, CodeOffset, LCode, Successor, ValueId};
use lower::{Extra, Literal, NodeBuilder};
use std::collections::VecDeque;
use tabled::{
    settings::{object::Rows, Border, Style},
    Table,
    //Tabled,
};

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
    s.push_str(&format!("<td>{}</td>", row.next));
    s.push_str(&format!("<td>{}</td>", row.prev));
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

pub fn code_to_string<E: Extra>(v: ValueId, blockify: &Blockify<E>, b: &NodeBuilder<E>) -> String {
    let code = blockify.get_code(v);
    match code {
        LCode::Declare => {
            let code_str = b.resolve_label(blockify.get_name(v).unwrap());
            format!("declare {}: {:?}", code_str, blockify.get_type(v))
        }

        LCode::DeclareFunction(maybe_entry) => {
            let code_str = b.resolve_label(blockify.get_name(v).unwrap());
            if let Some(entry_id) = maybe_entry {
                format!("declare_function({},{})", code_str, entry_id.index())
            } else {
                format!("declare_function({})", code_str)
            }
        }

        LCode::Label(args, kwargs) => {
            if let Some(key) = blockify.get_name(v) {
                format!("label({}, {}, {})", b.resolve_label(key), args, kwargs,)
            } else {
                format!("label(-, {}, {})", args, kwargs,)
            }
        }

        LCode::Goto(block_id) => {
            format!("goto({})", b.r(*block_id))
        }

        LCode::Jump(value_id, args) => {
            format!("jump({:?}, {})", value_id, args,)
        }

        LCode::Const(Literal::String(s)) => {
            format!("String({})", s)
        }

        LCode::Ternary(c, x, y) => {
            format!("Ternary({},{},{})", c.index(), x.index(), y.index())
        }

        LCode::Branch(c, x, y) => {
            format!("Branch({},{},{})", c.index(), x.index(), y.index())
        }

        _ => {
            format!("{:?}", code)
        }
    }
}

fn get_code_row<E: Extra>(v: ValueId, blockify: &Blockify<E>, b: &NodeBuilder<E>) -> CodeRow {
    let code = blockify.get_code(v);
    let ty = blockify.get_type(v);
    let mem = blockify.get_mem(v);
    let next = blockify.get_next(v).unwrap_or(v).index();
    let prev = blockify.get_prev(v).unwrap_or(v).index();
    let scope_id = blockify.get_scope_id(v);
    let entry_id = blockify.get_entry_id(v);
    let block_id = blockify.env.block_map.get(&entry_id).unwrap();

    CodeRow {
        pos: v.index(),
        next,
        prev,
        value: code_to_string(v, blockify, b),
        ty,
        mem: format!("{:?}", mem),
        name: blockify
            .get_name(v)
            .map(|key| b.resolve_label(key))
            .unwrap_or("".to_string())
            .to_string(),
        span_id: blockify.get_span_id(v).index(),
        scope_id: scope_id.index(),
        entry_id: entry_id.index(),
        block_id: block_id.index(),
        term: code.is_term(),
    }
}

pub fn dump_codes_filter<E: Extra>(
    blockify: &Blockify<E>,
    b: &NodeBuilder<E>,
    filter_entry_id: ValueId,
) -> Vec<CodeRow> {
    let mut pos = 0;
    let mut out = vec![];
    loop {
        let v = ValueId::new(pos as u32);
        let row = get_code_row(v, blockify, b);
        let entry_id = blockify.get_entry_id(v);

        let mut display = true;
        if filter_entry_id != entry_id {
            display = false;
        }

        if display {
            out.push(row);
        }

        pos += 1;
        if pos == blockify.code_count() {
            break;
        }
    }
    out
}

pub fn get_code_rows<E: Extra>(blockify: &Blockify<E>, b: &NodeBuilder<E>) -> Vec<CodeRow> {
    let mut out = vec![];
    let iter = LCodeIterator::new(blockify);
    for (_i, v) in iter.enumerate() {
        let row = get_code_row(v, blockify, b);
        let _code = blockify.get_code(v);
        out.push(row);
    }
    out
}

pub fn get_json<E: Extra>(blockify: &Blockify<E>, b: &NodeBuilder<E>) -> String {
    let out = get_code_rows(blockify, b);
    serde_json::to_string(&out).unwrap()
}

pub fn dump_codes<E: Extra>(blockify: &Blockify<E>, b: &NodeBuilder<E>) -> String {
    let mut out = vec![];
    let mut labels = vec![];
    let iter = LCodeIterator::new(blockify);
    for (i, v) in iter.enumerate() {
        let row = get_code_row(v, blockify, b);
        let code = blockify.get_code(v);

        if code.is_start() {
            labels.push(i + 1);
        }

        out.push(row);
    }

    let mut t = Table::new(out);

    t.with(Style::sharp());

    for i in labels {
        let rows = Rows::single(i);
        t.modify(rows, Border::new().set_top('-'));
    }
    let s = t.to_string();
    println!("{}", s);
    s
}

pub fn save_graph<E: Extra>(blockify: &Blockify<E>, filename: &str, b: &NodeBuilder<E>) {
    use petgraph::dot::{Config, Dot};
    let cfg = get_graph(ValueId::new(0), blockify, None, b);
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
                }
            }
        )
    );
    println!("saved graph {:?}", filename);
    println!("{}", s);
    std::fs::write(filename, s).unwrap();
}

pub fn get_cfg<E: Extra>(entry_id: ValueId, blockify: &Blockify<E>, b: &NodeBuilder<E>) -> CFG {
    get_graph(entry_id, blockify, Some(Successor::BlockScope), b)
}

pub fn get_graph<E: Extra>(
    entry_id: ValueId,
    blockify: &Blockify<E>,
    scope: Option<Successor>,
    b: &NodeBuilder<E>,
) -> CFG {
    let mut cfg = CFG::new();

    let mut stack = VecDeque::new();
    stack.push_back(entry_id);

    loop {
        if let Some(entry_id) = stack.pop_front() {
            if cfg.ids.contains_key(&entry_id) {
                continue;
            }
            let name = code_to_string(entry_id, blockify, b);
            let c = cfg.g.add_node(Node::new_block(name, entry_id.into()));
            cfg.ids.insert(entry_id, c);

            let block = blockify.env.get_block(entry_id);
            for (succ_type, next_code_offset) in block.succ.iter() {
                let v = blockify.env.resolve_code_offset(*next_code_offset);
                if scope.is_none() || scope == Some(*succ_type) {
                    stack.push_back(v);
                }
            }
        } else {
            break;
        }
    }
    for entry_id in cfg.ids.keys() {
        let block = blockify.env.get_block(*entry_id);
        let id = cfg.ids.get(entry_id).unwrap();
        for (succ_type, next_code_offset) in block.succ.iter() {
            if let Successor::BlockScope = succ_type {
                let v = blockify.env.resolve_code_offset(*next_code_offset);
                let child_id = cfg.ids.get(&v).unwrap();
                cfg.g.add_edge(*id, *child_id, ());
            }
        }
    }
    cfg
}
