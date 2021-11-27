extern crate nom;
use crate::parser::rwfile::*;
use aterms::extensible::*;
use aterms::shared::*;

use nom::sequence::separated_pair;
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_till1, take_while},
    character::complete::{char, multispace0},
    combinator::{cut, map, map_res, opt, verify},
    error::ErrorKind,
    error::ParseError,
    error::VerboseError,
    multi::{many0, separated_list0},
    number::complete::double,
    sequence::{delimited, pair, preceded, terminated, tuple},
    IResult, Parser,
};
use std::fs;

type ParseResult<'a, O> = IResult<&'a str, O, VerboseError<&'a str>>;

fn parse_name(input: &str) -> ParseResult<&str> {
    let (input, res) = take_till1(|c| !(char::is_alphanumeric(c) || c == '_'))(input)?;

    match res.parse::<f64>() {
        Ok(_) => {
            return Err(nom::Err::Error(VerboseError::from_error_kind(
                input,
                ErrorKind::Char,
            )))
        }
        Err(_) => {}
    };

    // Keywords
    if ["in"].contains(&res) {
        return Err(nom::Err::Error(VerboseError::from_error_kind(
            input,
            ErrorKind::Char,
        )));
    }

    Ok((input, res))
}

fn parse_function_name(input: &str) -> ParseResult<(FunctionReferenceType, &str)> {
    let (input, c) = alt((char('.'), char('!'))).parse(input)?;
    let reftype = match c {
        '.' => FunctionReferenceType::Try,
        '!' => FunctionReferenceType::Force,
        _ => panic!("Unexpected function name begin character"),
    };
    let (input, name) = parse_name(input)?;
    Ok((input, (reftype, name)))
}

fn parse_var_term_name(i: &str) -> ParseResult<&str> {
    preceded(tag("?"), parse_name)(i)
}

fn parse_ws(i: &str) -> ParseResult<&str> {
    multispace0(i)
}

fn parse_comment(i: &str) -> ParseResult<()> {
    let (i, _) = tuple((
        char('#'),
        is_not("\n\r"),
        take_while(|c| c == '\n' || c == '\r'),
    ))
    .parse(i)?;
    Ok((i, ()))
}

/*
* Matching
*/

fn parse_term_name_match(i: &str) -> ParseResult<Match> {
    alt((
        map(parse_var_term_name, |n| {
            Match::VariableMatcher(VariableMatcher {
                name: n.to_string(),
                annotations: vec![],
            })
        }),
        map(parse_name, |n| {
            Match::StringMatcher(StringMatcher {
                value: n.to_string(),
                annotations: vec![],
            })
        }),
    ))(i)
}

fn parse_variable_match(input: &str) -> ParseResult<Match> {
    let (input, res) = parse_name(input)?;
    let (input, a) = opt(delimited(
        char('{'),
        ws(separated_list0(ws(tag(",")), parse_match)),
        char('}'),
    ))(input)?;
    Ok((
        input,
        Match::VariableMatcher(VariableMatcher {
            name: res.to_string(),
            annotations: a.unwrap_or(Vec::new()),
        }),
    ))
}

fn parse_variadic_elem_match(i: &str) -> ParseResult<Match> {
    map(preceded(tag(".."), cut(parse_name)), |n| {
        Match::VariadicElementMatcher(VariadicElementMatcher {
            name: n.to_string(),
        })
    })(i)
}

fn parse_list_match(i: &str) -> ParseResult<Match> {
    map(
        delimited(
            ws(char('[')),
            separated_pair(parse_match, ws(char('|')), parse_match),
            ws(char(']')),
        ),
        |(head, tail)| {
            Match::ListConsMatcher(ListConsMatcher {
                head: Box::from(head),
                tail: Box::from(tail),
                annotations: vec![],
            })
        },
    )(i)
}

fn parse_match(i: &str) -> ParseResult<Match> {
    alt((
        parse_recursive_term(parse_term_name_match, parse_match, Match::from_recursive),
        parse_list_term(parse_match, Match::from_list),
        parse_list_match,
        verify(
            parse_tuple_term(parse_match, Match::from_tuple),
            |m| match m {
                Match::TupleMatcher(tm) => {
                    if tm.elems.len() == 0 {
                        return true;
                    }

                    let l = tm.elems.len() - 1;
                    for i in 0..l {
                        match &tm.elems[i] {
                            Match::VariadicElementMatcher(_) => {
                                panic!("Variadic element matcher must be at the end")
                            }
                            _ => {}
                        }
                    }
                    true
                }
                _ => false,
            },
        ),
        parse_string_term(parse_match, Match::from_string),
        parse_number_term(parse_match, Match::from_number),
        parse_variable_match,
        parse_variadic_elem_match,
    ))(i)
}

/*
* Expressions
*/

fn parse_function_ref(input: &str) -> ParseResult<Expr> {
    let (input, (ref_type, func_name)) = parse_function_name(input)?;
    let (input, meta) = parse_meta_args(input)?;
    Ok((
        input,
        Expr::FRef(FRef::from(&func_name.to_string(), &meta, ref_type)),
    ))
}

fn parse_meta_args(input: &str) -> ParseResult<Vec<Expr>> {
    let (input, meta) = opt(delimited(
        char('['),
        separated_list0(
            ws(char(',')),
            alt((
                map_res(parse_function_ref, |n| -> Result<Expr, String> { Ok(n) }),
                map_res(parse_expr, |e| -> Result<Expr, String> { Ok(e) }),
            )),
        ),
        ws(char(']')),
    ))(input)?;

    Ok((input, meta.unwrap_or(Vec::new())))
}

fn parse_value(i: &str) -> ParseResult<Expr> {
    map(ws(double), |n: f64| Expr::Number(Number { value: n }))(i)
}

fn parse_string(i: &str) -> ParseResult<Expr> {
    map(aterms::shared::parse_string_literal, |value| {
        Expr::Text(Text { value })
    })(i)
}

enum AnotType {
    Set,
    Add,
}

fn parse_anot_opener(i: &str) -> ParseResult<AnotType> {
    alt((
        map(tag("{+"), |_| AnotType::Add),
        map(tag("{"), |_| AnotType::Set),
    ))(i)
}

fn parse_unroll_variadic(i: &str) -> ParseResult<Expr> {
    map(preceded(tag(".."), cut(parse_name)), |n| {
        Expr::UnrollVariadic(Ref {
            name: n.to_string(),
        })
    })(i)
}

fn parse_rec_term(i: &str) -> ParseResult<Expr> {
    map_res(
        tuple((
            alt((
                map(parse_name, |n| {
                    Expr::Text(Text {
                        value: n.to_string(),
                    })
                }),
                map(parse_var_term_name, |n| {
                    Expr::Ref(Ref {
                        name: n.to_string(),
                    })
                }),
            )),
            pair(
                opt(delimited(
                    ws(char('(')),
                    cut(ws(separated_list0(ws(tag(",")), parse_expr))),
                    ws(char(')')),
                )),
                opt(terminated(
                    pair(
                        ws(parse_anot_opener),
                        ws(separated_list0(ws(tag(",")), parse_expr)),
                    ),
                    ws(char('}')),
                )),
            ),
        )),
        |(name, (opt_args, opt_annots))| {
            let inner = match opt_args {
                Some(args) => Expr::Term(Term {
                    constructor: Box::from(name),
                    terms: args,
                }),
                None => match name {
                    Expr::Text(t) => Expr::Ref(Ref { name: t.value }),
                    _ => return Err("Cannot have ?name expression outside of term building"),
                },
            };

            match opt_annots {
                Some((AnotType::Add, annot)) => Ok(Expr::AddAnnotation(Annotation {
                    inner: Box::from(inner),
                    annotations: annot,
                })),
                Some((AnotType::Set, annot)) => Ok(Expr::Annotation(Annotation {
                    inner: Box::from(inner),
                    annotations: annot,
                })),
                None => Ok(inner),
            }
        },
    )(i)
}

fn parse_tuple(i: &str) -> ParseResult<Expr> {
    alt((
        map(
            delimited(ws(char('(')), parse_expr, ws(char(')'))),
            |expr| -> Expr { expr },
        ),
        parse_tuple_term_no_annotations(parse_expr, |r| Expr::Tuple(Tuple { values: r })),
    ))(i)
}

fn parse_list(input: &str) -> ParseResult<Expr> {
    alt((
        // [ a, b, c ]
        parse_list_term_no_annotations(parse_expr, |r| Expr::List(List { values: r })),
        // [ h | t ]
        map(
            delimited(
                ws(char('[')),
                tuple((parse_expr, ws(char('|')), cut(parse_expr))),
                cut(ws(char(']'))),
            ),
            |t: (Expr, char, Expr)| {
                Expr::ListCons(ListCons {
                    head: Box::from(t.0),
                    tail: Box::from(t.2),
                })
            },
        ),
    ))(input)
}

fn parse_term(input: &str) -> ParseResult<Expr> {
    let (input, term) = alt((
        parse_tuple,
        parse_rec_term,
        parse_value,
        parse_string,
        parse_unroll_variadic,
        parse_list,
    ))(input)?;

    let (input, anot) = opt(delimited(
        ws(char('{')),
        cut(ws(separated_list0(ws(tag(",")), parse_expr))),
        cut(char('}')),
    ))(input)?;

    match anot {
        Some(annotation) => Ok((
            input,
            Expr::Annotation(Annotation {
                inner: Box::from(term),
                annotations: annotation,
            }),
        )),
        None => Ok((input, term)),
    }
}

fn parse_invocation(input: &str) -> ParseResult<Expr> {
    let (input, fref) = opt(parse_function_ref)(input)?;
    match fref {
        Some(Expr::FRef(fref)) => {
            let (input, arg) = opt(ws(parse_invocation))(input)?;
            match arg {
                Some(arg) => Ok((
                    input,
                    Expr::Invoke(Invocation {
                        name: fref,
                        arg: Box::from(arg),
                    }),
                )),
                None => Ok((
                    input,
                    Expr::Invoke(Invocation {
                        name: fref,
                        arg: Box::from(Expr::This),
                    }),
                )),
            }
        }
        Some(e) => Ok((input, e)),
        _ => parse_term(input),
    }
}

fn parse_let(i: &str) -> ParseResult<Expr> {
    alt((
        map(
            tuple((
                parse_match,
                ws(tag(":=")),
                cut(parse_expr),
                cut(ws(tag("in"))),
                cut(parse_expr),
            )),
            |(match_, _, val, _, body)| {
                Expr::Let(Let {
                    lhs: match_,
                    rhs: Box::from(val),
                    body: Box::from(body),
                })
            },
        ),
        parse_invocation,
    ))(i)
}

fn parse_catch(i: &str) -> ParseResult<Expr> {
    map(
        tuple((parse_let, opt(preceded(ws(tag("+")), cut(parse_sequence))))),
        |(left, right)| match right {
            None => left,
            Some(rhs) => Expr::Op(Op::Or(Box::from(left), Box::from(rhs))),
        },
    )(i)
}

fn parse_sequence(i: &str) -> ParseResult<Expr> {
    map(
        tuple((
            parse_catch,
            opt(preceded(ws(tag(">")), cut(parse_sequence))),
        )),
        |(left, right)| match right {
            None => left,
            Some(rhs) => Expr::Op(Op::And(Box::from(left), Box::from(rhs))),
        },
    )(i)
}

fn parse_choice(i: &str) -> ParseResult<Expr> {
    map(
        tuple((
            parse_sequence,
            opt(pair(
                preceded(ws(char('?')), cut(parse_choice)),
                cut(preceded(ws(char(':')), parse_expr)),
            )),
        )),
        |(e, maybe)| match maybe {
            None => e,
            Some((left, right)) => {
                Expr::Op(Op::Choice(Box::from(e), Box::from(left), Box::from(right)))
            }
        },
    )(i)
}

fn parse_expr(input: &str) -> ParseResult<Expr> {
    parse_choice(input)
}

fn parse_function(input: &str) -> ParseResult<Function> {
    let (input, _) = opt(many0(pair(parse_comment, opt(parse_ws))))(input)?;
    let (input, name) = parse_name(input)?;
    let (input, meta) = parse_meta_args(input)?;
    let (input, _) = ws(tag(":")).parse(input)?;
    let (input, matcher) = parse_match(input)?;
    let (input, _) = ws(tag("->")).parse(input)?;
    let (input, body) = parse_expr(input)?;
    let (input, _) = ws(tag(";")).parse(input)?;
    Ok((
        input,
        Function {
            name: name.to_string(),
            meta,
            matcher,
            body,
        },
    ))
}

pub fn parse_rw_string(input: &str) -> Result<File, String> {
    match many0(ws(parse_function))(input) {
        Ok((input, f)) => {
            if input.len() > 0 {
                panic!("Input left after parsing:\n{}", input);
            }

            Ok(File {
                functions: f,
                filename: None,
            })
        }
        Err(nom::Err::Error(e)) => panic!("Something went wrong: {}", e),
        Err(nom::Err::Failure(e)) => {
            panic!("Parse failure:\n{}", nom::error::convert_error(input, e))
        }
        Err(nom::Err::Incomplete(_)) => panic!("Parser reported incomplete input - aborting"),
    }
}

pub fn parse_rw_file(filename: &str) -> Result<File, String> {
    let f = fs::read_to_string(filename).unwrap();
    let mut rw_file = parse_rw_string(String::as_str(&f))?;
    rw_file.set_filename(filename);
    Ok(rw_file)
}
