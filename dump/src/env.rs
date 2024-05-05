use flat::{Blockify, Environment};
use lower::{Extra, NodeBuilder};
use tabled::{
    settings::Style,
    Table,
    //Tabled,
};

pub fn dump(env: &Environment, b: &NodeBuilder) {
    println!("current scope: {:?}", env.current_scope());
    //println!("static block: {:?}", self.static_block_id());
    //println!("static scope: {:?}", self.static_scope_id());
    for block in env.blocks.iter() {
        //let block_id = BlockId(offset as u32);
        println!("block({:?}, {:?})", block.entry_id, block);
    }

    for (index, layer) in env.scopes.iter().enumerate() {
        println!("scope({},{:?})", index, layer.scope_type);
        for (key, data) in layer.names.iter() {
            println!("  name  {} = {:?}", b.r(*key), data);
        }
        for (key, data) in layer.labels.iter() {
            println!("  label {} = {:?}", b.resolve_label(*key), data);
        }
        for next_id in layer.next_block.iter() {
            println!("  next  {:?}", next_id);
        }
        for block_id in layer.blocks.iter() {
            println!("  block {:?}", block_id);
        }
        for (name, def) in layer.lambdas.iter() {
            println!("  def {:?}", (b.resolve_label(*name), def));
        }
    }
}

pub fn blockify_dump(blockify: &Blockify, b: &NodeBuilder) {
    //self.dump_codes(b, None);
    dump(&blockify.env, b);

    for block in blockify.env.blocks.iter() {
        println!("block({:?}, {:?})", block.entry_id, block);
        let rows = crate::code::dump_codes_filter(blockify, b, block.entry_id.unwrap());
        let s = Table::new(rows).with(Style::sharp()).to_string();
        println!("{}", s);
    }
    /*
    let rows = self.get_code_rows(b);

    if false {
        use minijinja::{context, Environment};
        use std::io::prelude::*;
        let mut env = Environment::new();
        env.add_template("template", include_str!("template.html"))
            .unwrap();
        let tmpl = env.get_template("template").unwrap();
        let html = tmpl
            .render(context!(header => CodeRow::header(), rows => rows))
            .unwrap();
        let mut file = std::fs::File::create("blocks.html").unwrap();
        file.write_all(html.as_bytes()).unwrap();
        println!(
            "{}",
            tmpl.render(context!(header => CodeRow::header(), rows => rows))
                .unwrap()
        );
    }
    */
}
