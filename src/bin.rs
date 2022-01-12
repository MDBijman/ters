mod interp;
mod parser;

extern crate aterms;
extern crate clap;
extern crate itertools;
use clap::{App, Arg};
use std::fs;
use std::io::prelude::*;

fn main() {
    let matches = App::new("ReWriter")
        .version("0.1")
        .author("Matthijs Bijman <matthijs@bijman.org>")
        .about("Term rewriter for language implementation")
        .arg(
            Arg::with_name("ters_file")
                .short("r")
                .long("ters")
                .value_name("TERS_FILE")
                .help("The input .rw file")
                .required(true),
        )
        .arg(
            Arg::with_name("input_file")
                .short("i")
                .long("input")
                .value_name("INPUT_FILE")
                .help("The input .term file")
                .required(true),
        )
        .arg(
            Arg::with_name("output_file")
                .short("o")
                .long("output")
                .value_name("OUTPUT_FILE")
                .help("The output .term file")
                .required(true),
        )
        .get_matches();

    let rw_name = matches.value_of("ters_file").unwrap();
    let term_name = matches.value_of("input_file").unwrap();
    let out_name = matches.value_of("output_file").unwrap();

    let input_term = aterms::base::parse_term_from_file(&String::from(term_name)).unwrap();
    let input_rewrite = parser::parser::parse_rw_file(&String::from(rw_name)).unwrap();
    let mut interpreter = interp::interp::Rewriter::new_with_prelude(input_rewrite);

    match interpreter.rewrite(input_term) {
        Ok(result) => {
            let mut o = fs::File::create(out_name).unwrap();
            o.write(format!("{}", result).as_bytes()).unwrap();
            o.sync_all().unwrap();
        }
        Err(err) => {
            eprintln!("Failure");
        }
    }
}
