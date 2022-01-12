use crate::parser::parser::parse_rw_string;
use crate::parser::rwfile::*;
use aterms as at;
use std::collections::HashMap;
use std::fmt;

#[cfg(feature = "bench-instrumentation")]
#[derive(Clone)]
pub struct BenchmarkMetrics {
    counters: HashMap<String, u64>,
}

#[cfg(feature = "bench-instrumentation")]
impl BenchmarkMetrics {
    pub fn new() -> BenchmarkMetrics {
        BenchmarkMetrics {
            counters: HashMap::new(),
        }
    }
}

#[derive(Clone)]
pub struct Rewriter {
    rules: File,
    newname_counts: HashMap<String, u64>,

    #[cfg(feature = "bench-instrumentation")]
    metrics: BenchmarkMetrics,
}

#[derive(Clone, Debug)]
pub struct Context {
    bound_variables: HashMap<String, at::base::Term>,
    bound_functions: HashMap<String, FRef>,
}

impl Context {
    pub fn new() -> Context {
        Context {
            bound_variables: HashMap::new(),
            bound_functions: HashMap::new(),
        }
    }

    pub fn bind_variable(&mut self, name: &str, term: at::base::Term) {
        self.bound_variables.insert(String::from(name), term);
    }

    pub fn merge_variable_bindings(&mut self, b: HashMap<String, at::base::Term>) {
        for (k, v) in b {
            self.bound_variables.insert(k, v);
        }
    }

    pub fn merge_function_bindings(&mut self, b: HashMap<String, FRef>) {
        for (k, v) in b {
            self.bound_functions.insert(k, v);
        }
    }

    pub fn merge(&mut self, other: Context) {
        self.merge_variable_bindings(other.bound_variables);
        self.merge_function_bindings(other.bound_functions);
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (k, v) in self.bound_variables.iter() {
            write!(f, "{}: {}\n", k, v)?;
        }
        for (k, v) in self.bound_functions.iter() {
            write!(f, "{}: {} [{:?}]\n", k, v.name, v.meta)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct Failure {
    error_message: String,
    callstack: Vec<String>,
    failure_context: Context,
    term: at::base::Term,
}

impl Failure {
    pub fn with_call(&mut self, call: String) {
        self.callstack.push(call);
    }
}

fn check_and_bind_annotations(
    matchers: &Vec<Match>,
    mut annots: at::base::Annotations,
) -> Option<Context> {
    let mut h: Context = Context::new();

    for matcher_idx in 0..matchers.len() {
        let matcher = &matchers[matcher_idx];
        match matcher {
            Match::VariadicElementMatcher(v) => {
                h.bound_variables.insert(
                    v.name.clone(),
                    at::base::Term::new_list_term(annots.elems),
                );
                assert!(matcher_idx == matchers.len() - 1);
                break;
            }
            _ => {
                let mut found_idx = None;

                for (idx, annot) in annots.elems.iter().enumerate() {
                    match check_and_bind_match(&matcher, annot) {
                        Some(m) => {
                            h.merge(m);
                            found_idx = Some(idx);
                            break;
                        }
                        None => {}
                    }
                }

                if let Some(idx) = found_idx {
                    annots.elems.remove(idx)
                } else {
                    return None;
                };
            }
        }
    }

    Some(h)
}

fn check_and_bind_match(m: &Match, t: &at::base::Term) -> Option<Context> {
    match (m, t) {
        (Match::VariadicElementMatcher(_), _) => panic!("Cannot match variadic element matcher"),
        (Match::AnyMatcher, _) => Some(Context::new()),
        (Match::TermMatcher(tm), at::base::Term::RTerm(rec_term)) => {
            let mut bindings: Context = Context::new();

            let head_binding = check_and_bind_match(
                &tm.constructor,
                &at::base::Term::new_string_term(&rec_term.constructor),
            );

            if head_binding.is_none() {
                return None;
            }

            bindings.merge(head_binding.unwrap());

            let mut i = 0;
            let mut matched_variadic = false;
            for m in tm.terms.iter() {
                match m {
                    Match::VariadicElementMatcher(v) => {
                        bindings.bound_variables.insert(
                            v.name.clone(),
                            at::base::Term::new_list_term(rec_term.terms[i..].to_vec()),
                        );

                        matched_variadic = true;

                        break;
                    }
                    _ => {
                        if i as i64 > (rec_term.terms.len() as i64) - 1 {
                            return None;
                        };

                        let sub_bindings = check_and_bind_match(m, &rec_term.terms[i])?;

                        bindings.merge(sub_bindings);
                    }
                }

                i += 1;
            }

            if !matched_variadic && i < rec_term.terms.len() {
                return None;
            }

            match check_and_bind_annotations(&tm.annotations, rec_term.annotations.clone()) {
                None => return None,
                Some(b) => bindings.merge(b),
            }

            Some(bindings)
        }
        (Match::VariableMatcher(vm), t) => {
            let mut bindings: Context = Context::new();
            bindings.bind_variable(vm.name.as_str(), t.clone());

            match check_and_bind_annotations(&vm.annotations, t.get_annotations().clone()) {
                None => return None,
                Some(b) => bindings.merge(b),
            }

            Some(bindings)
        }
        (Match::StringMatcher(sm), at::base::Term::STerm(s)) => match s.value == sm.value {
            true => Some(Context::new()),
            false => None,
        },
        (Match::NumberMatcher(nm), at::base::Term::NTerm(n)) => match n.value == nm.value {
            true => Some(Context::new()),
            false => None,
        },
        (Match::ListConsMatcher(lm), at::base::Term::LTerm(lt)) => {
            let mut bindings: Context = Context::new();

            // Match empty list against non-empty pattern
            if lt.terms.len() == 0 {
                return None;
            }

            let sub_bindings = check_and_bind_match(&*lm.head, &lt.terms[0])?;
            bindings.merge(sub_bindings);

            // Match multiple element list against multiple element pattern -> success
            let sub_bindings = check_and_bind_match(
                &*lm.tail,
                &at::base::Term::new_list_term(lt.terms[1..].to_vec()),
            )?;
            bindings.merge(sub_bindings);

            Some(bindings)
        }
        (
            Match::TupleMatcher(TupleMatcher {
                elems,
                annotations: anno_match,
            }),
            at::base::Term::TTerm(at::base::TTerm { terms, annotations }),
        )
        | (
            Match::ListMatcher(ListMatcher {
                elems,
                annotations: anno_match,
            }),
            at::base::Term::LTerm(at::base::LTerm { terms, annotations }),
        ) => {
            // 1 to 1 matching elements with matcher
            if elems.len() != terms.len() {
                return None;
            }

            let mut bindings: Context = Context::new();
            let mut i = 0;
            for m in elems.iter() {
                match m {
                    Match::VariadicElementMatcher(v) => {
                        bindings.bind_variable(
                            v.name.as_str(),
                            at::base::Term::new_list_term(terms[i..].to_vec()),
                        );
                        break;
                    }
                    _ => {
                        if i as i64 > (terms.len() as i64) - 1 {
                            return None;
                        };
                        let sub_bindings = check_and_bind_match(m, &terms[i])?;
                        bindings.merge(sub_bindings);
                    }
                }

                i += 1;
            }

            match check_and_bind_annotations(anno_match, annotations.clone()) {
                None => return None,
                Some(b) => bindings.merge(b),
            }

            Some(bindings)
        }
        _ => None,
    }
}

impl Rewriter {
    pub fn new(f: File) -> Rewriter {
        #[cfg(feature = "bench-instrumentation")]
        return Rewriter {
            rules: f,
            newname_counts: HashMap::new(),
            metrics: BenchmarkMetrics::new(),
        };

        #[cfg(not(feature = "bench-instrumentation"))]
        return Rewriter {
            rules: f,
            newname_counts: HashMap::new(),
        };
    }

    pub fn new_with_prelude(f: File) -> Rewriter {
        let prelude_code = include_str!("../../std/prelude.rw");
        let prelude = parse_rw_string(&prelude_code).unwrap();
        Rewriter::new(File::merge(prelude, f))
    }

    pub fn rewrite(&mut self, t: at::base::Term) -> Result<at::base::Term, String> {
        self.rewrite_with_rule(t, "main")
    }

    pub fn rewrite_with_rule(&mut self, t: at::base::Term, f: &str) -> Result<at::base::Term, String> {
        let result = self.interp_function(
            &Context::new(),
            &FRef::from(&String::from(f), &Vec::new(), FunctionReferenceType::Force),
            t,
        );

        #[cfg(feature = "bench-instrumentation")]
        {
            use std::fs;
            use std::io::Write;
            use std::path::Path;
            let rw_path_str = self.rules.filename.clone().unwrap();
            let rw_path = Path::new(&rw_path_str);
            let bench_path = Path::new("./tests/benchmarks/")
                .join(rw_path.file_name().unwrap())
                .with_extension("json");
            let mut o = fs::File::create(bench_path).unwrap();

            o.write("{\n".as_bytes()).unwrap();
            let mut res = self.metrics.counters.iter().collect::<Vec<_>>();
            res.sort_by(|x, y| x.0.cmp(&y.0));
            let mut iter = res.iter();
            let (k, v) = iter.next().unwrap();
            o.write(format!("\t\"{}\": {}", k, v).as_bytes()).unwrap();
            for (k, v) in iter {
                o.write(format!(",\n\t\"{}\": {}", k, v).as_bytes())
                    .unwrap();
            }
            o.write("\n}\n".as_bytes()).unwrap();
        }

        match result {
            Err(f) => {
                use std::fmt::Write;
                let mut error = String::new();
                write!(error, "{}\n", f.error_message).unwrap();

                let mut iter = f.callstack.iter();
                for call in iter.by_ref().take(5) {
                    write!(error, "in {}\n", call).unwrap();
                }

                if iter.len() > 0 {
                    write!(error, "... [omitted {} more]\n", iter.len()).unwrap();
                }

                if self.rules.filename.is_some() {
                    write!(
                        error,
                        "in source file {}",
                        self.rules.filename.as_ref().unwrap()
                    )
                    .unwrap();
                }

                write!(error, "\nVariable bindings:\n").unwrap();
                write!(error, "{}\n", f.failure_context).unwrap();
                write!(error, "Current term:\n").unwrap();
                write!(error, "{}\n", f.term).unwrap();
                Err(error)
            }
            Ok(t) => Ok(t.unwrap().to_term().unwrap()),
        }
    }

    pub fn get_newname_count(&mut self, n: &String) -> u64 {
        *self.newname_counts.entry(n.to_string()).or_insert(0)
    }

    pub fn gen_newname_count(&mut self, n: &String) -> u64 {
        let e = self.newname_counts.entry(n.to_string()).or_insert(0);
        let r = *e;
        *e += 1;
        r
    }

    pub fn reset_newname_count(&mut self, n: &String) {
        self.newname_counts.remove(n);
    }
    ///

    fn is_builtin(name: &str) -> bool {
        [
            "add",
            "mul",
            "div",
            "min",
            "max",
            "subterms",
            "with_subterms",
            "debug",
            "debug_context",
            "fail",
            "gen_name",
            "gen_num",
            "get_num",
            "reset_num",
            "eq",
            "concat_str",
            "to_str",
        ]
        .contains(&name)
    }

    pub fn try_run_builtin_function(
        &mut self,
        c: &Context,
        function: &FRef,
        t: &at::base::Term,
    ) -> Option<Expr> {
        self.bench_increment_count("fn:try_run_builtin_function");

        let meta = &function.meta;
        match (function.name.as_str(), t) {
            ("add", at::base::Term::TTerm(rt)) if rt.terms.len() == 2 => {
                match (rt.terms.get(0).unwrap(), rt.terms.get(1).unwrap()) {
                    (at::base::Term::NTerm(n1), at::base::Term::NTerm(n2)) => {
                        Some(Rewriter::term_to_expr(
                            &at::base::Term::new_number_term(n1.value + n2.value),
                        ))
                    }
                    _ => None,
                }
            }
            ("mul", at::base::Term::TTerm(rt)) if rt.terms.len() == 2 => {
                match (rt.terms.get(0).unwrap(), rt.terms.get(1).unwrap()) {
                    (at::base::Term::NTerm(n1), at::base::Term::NTerm(n2)) => {
                        Some(Rewriter::term_to_expr(
                            &at::base::Term::new_number_term(n1.value * n2.value),
                        ))
                    }
                    _ => None,
                }
            }
            ("div", at::base::Term::TTerm(rt)) if rt.terms.len() == 2 => {
                match (rt.terms.get(0).unwrap(), rt.terms.get(1).unwrap()) {
                    (at::base::Term::NTerm(n1), at::base::Term::NTerm(n2)) => {
                        Some(Rewriter::term_to_expr(
                            &at::base::Term::new_number_term(n1.value / n2.value),
                        ))
                    }
                    _ => None,
                }
            }
            ("min", at::base::Term::TTerm(rt)) if rt.terms.len() == 2 => {
                match (rt.terms.get(0).unwrap(), rt.terms.get(1).unwrap()) {
                    (at::base::Term::NTerm(n1), at::base::Term::NTerm(n2)) => {
                        Some(Rewriter::term_to_expr(
                            &at::base::Term::new_number_term(if n1.value < n2.value {
                                n1.value
                            } else {
                                n2.value
                            }),
                        ))
                    }
                    _ => None,
                }
            }
            ("max", at::base::Term::TTerm(rt)) if rt.terms.len() == 2 => {
                match (rt.terms.get(0).unwrap(), rt.terms.get(1).unwrap()) {
                    (at::base::Term::NTerm(n1), at::base::Term::NTerm(n2)) => {
                        Some(Rewriter::term_to_expr(
                            &at::base::Term::new_number_term(if n1.value < n2.value {
                                n2.value
                            } else {
                                n1.value
                            }),
                        ))
                    }
                    _ => None,
                }
            }
            ("subterms", at::base::Term::RTerm(rt)) if meta.len() == 0 => Some(
                Rewriter::term_to_expr(&at::base::Term::new_list_term(rt.terms.clone())),
            ),
            ("with_subterms", at::base::Term::TTerm(rt)) if meta.len() == 0 => {
                match (&rt.terms[0], &rt.terms[1]) {
                    (at::base::Term::RTerm(constr), at::base::Term::LTerm(elems)) => {
                        Some(Rewriter::term_to_expr(&at::base::Term::new_rec_term(
                            constr.constructor.as_str(),
                            elems.terms.clone(),
                        )))
                    }
                    _ => None,
                }
            }
            ("debug", t) => {
                println!("{}", t);
                Some(Rewriter::term_to_expr(&t))
            }
            ("debug_context", t) => {
                println!("{}", c);
                Some(Rewriter::term_to_expr(&t))
            }
            ("fail", _) => None,
            ("gen_name", at::base::Term::STerm(st)) => {
                let id = self.gen_newname_count(&st.value);
                let sterm =
                    at::base::Term::new_string_term(format!("{}_{}", st.value, id).as_str());

                Some(Rewriter::term_to_expr(&sterm))
            }
            ("gen_num", at::base::Term::STerm(st)) => {
                let id = self.gen_newname_count(&st.value);
                let sterm = at::base::Term::new_number_term(id as f64);

                Some(Rewriter::term_to_expr(&sterm))
            }
            ("get_num", at::base::Term::STerm(st)) => {
                let id = self.get_newname_count(&st.value);
                let sterm = at::base::Term::new_number_term(id as f64);

                Some(Rewriter::term_to_expr(&sterm))
            }
            ("reset_num", at::base::Term::STerm(st)) => {
                self.reset_newname_count(&st.value);

                Some(Rewriter::term_to_expr(&at::base::Term::STerm(
                    st.clone(),
                )))
            }
            ("concat_str", at::base::Term::LTerm(lt)) => {
                let mut out: String = String::new();

                for item in lt.terms.iter() {
                    match item {
                        at::base::Term::STerm(s) => out.push_str(s.value.as_str()),
                        _ => return None,
                    }
                }

                Some(Rewriter::term_to_expr(
                    &at::base::Term::new_string_term(&out),
                ))
            }
            ("to_str", t) => Some(Rewriter::term_to_expr(
                &at::base::Term::new_string_term(&format!("{}", t)),
            )),
            ("eq", at::base::Term::TTerm(tt)) if tt.terms.len() == 2 => {
                let lhs = &tt.terms[0];
                let rhs = &tt.terms[1];

                if lhs == rhs {
                    Some(Rewriter::term_to_expr(&at::base::Term::new_tuple_term(
                        vec![lhs.clone(), rhs.clone()],
                    )))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn reduce(
        &mut self,
        c: &Context,
        e: &Expr,
        t: &at::base::Term,
    ) -> Result<Option<Expr>, Failure> {
        self.bench_increment_count("fn:reduce");

        Ok(match e {
            Expr::FRef(f) => {
                self.bench_increment_count("fn:reduce:fref");
                let new_meta: Vec<Expr> = f
                    .meta
                    .iter()
                    .map(|e| self.reduce(c, e, t).unwrap().unwrap())
                    .collect();

                match c.bound_functions.get(&f.name) {
                    Some(f) => Some(Expr::FRef(FRef {
                        name: f.name.clone(),
                        meta: [f.meta.clone(), new_meta].concat(),
                        ref_type: f.ref_type,
                    })),
                    _ => Some(Expr::FRef(FRef {
                        name: f.name.clone(),
                        meta: new_meta,
                        ref_type: f.ref_type,
                    })),
                }
            }
            Expr::Tuple(tup) => {
                self.bench_increment_count("fn:reduce:tuple");
                let mut res: Vec<at::base::Term> = vec![];
                for e in &tup.values {
                    match e {
                        // Variadic unrolling such as (a, b, ..c)
                        Expr::UnrollVariadic(l) => {
                            let list = c
                                .bound_variables
                                .get(&l.name)
                                .expect(format!("Cannot resolve reference {}", l.name).as_str());
                            match list {
                                // Reference must resolve to list term
                                at::base::Term::LTerm(l) => {
                                    for elem in &l.terms {
                                        res.push(elem.clone());
                                    }
                                }
                                _ => return Ok(None),
                            }
                        }

                        // Not variadic
                        _ => {
                            let value = self.reduce(c, &e, t)?;
                            if value.is_none() {
                                return Ok(None);
                            }

                            res.push(Rewriter::expr_to_term(&value.unwrap()))
                        }
                    }
                }

                Some(Expr::SimpleTerm(at::base::Term::new_tuple_term(res)))
            }
            Expr::Invoke(inv) => {
                self.bench_increment_count("fn:reduce:invoke");
                let arg = match self.reduce(c, &inv.arg, t)? {
                    Some(t) => t.to_term().unwrap(),
                    None => return Ok(None),
                };

                return self.interp_function(c, &inv.name, arg);
            }
            Expr::Ref(r) => {
                self.bench_increment_count("fn:reduce:ref");
                let res = &c.bound_variables.get(&r.name);
                if res.is_none() {
                    return Err(Failure {
                        error_message: String::from(format!(
                            "Could not resolve variable, {}",
                            r.name
                        )),
                        callstack: vec![],
                        failure_context: c.clone(),
                        term: t.clone(),
                    });
                }
                Some(Rewriter::term_to_expr(res.unwrap()))
            }
            Expr::UnrollVariadic(_) => {
                panic!("Cannot interp Expr::UnrollVariadic");
            }
            Expr::Number(n) => Some(Rewriter::term_to_expr(
                &at::base::Term::new_number_term(n.value),
            )),
            Expr::Op(Op::Choice(cond, th, el)) => {
                self.bench_increment_count("fn:reduce:choice");
                match self.reduce(c, &*cond, t)? {
                    Some(res) => self.reduce(c, &*th, &res.to_term().unwrap().clone())?,
                    None => self.reduce(c, &*el, t)?,
                }
            }
            Expr::Op(Op::Or(l, r)) => {
                self.bench_increment_count("fn:reduce:or");
                match self.reduce(c, &*l, t)? {
                    Some(t) => Some(t),
                    None => self.reduce(c, &*r, t)?,
                }
            }
            Expr::Op(Op::And(l, r)) => {
                self.bench_increment_count("fn:reduce:and");
                let lr = match self.reduce(c, &*l, t)? {
                    Some(t) => t.to_term().unwrap(),
                    None => return Ok(None),
                };

                self.reduce(c, &*r, &lr)?
            }
            Expr::Term(et) => {
                self.bench_increment_count("fn:reduce:term");
                let head = self.reduce(c, &et.constructor, t)?;

                if head.is_none() {
                    return Ok(None);
                }

                // Interpret subterms as tuple
                let terms = match self.reduce(
                    c,
                    &Expr::Tuple(Tuple {
                        values: et.terms.clone(),
                    }),
                    t,
                )? {
                    Some(Expr::SimpleTerm(at::base::Term::TTerm(ts))) => ts.terms,
                    _ => return Ok(None),
                };

                match head.unwrap() {
                    Expr::SimpleTerm(at::base::Term::STerm(s)) => Some(Rewriter::term_to_expr(
                        &at::base::Term::new_rec_term(&s.value, terms),
                    )),
                    _ => None,
                }
            }
            Expr::This => Some(Rewriter::term_to_expr(&t)),
            Expr::AddAnnotation(a) => {
                self.bench_increment_count("fn:reduce:addannotation");
                let mut inner_term = match self.reduce(c, &*a.inner, t)? {
                    Some(t) => t.to_term().unwrap(),
                    None => return Ok(None),
                };

                for subt in a.annotations.iter() {
                    let r = match self.reduce(c, &subt, t)? {
                        Some(t) => t.to_term().unwrap(),
                        None => return Ok(None),
                    };
                    inner_term.add_annotation(r);
                }

                Some(Rewriter::term_to_expr(&inner_term))
            }
            Expr::Annotation(a) => {
                self.bench_increment_count("fn:reduce:annotation");
                let mut inner_term = match self.reduce(c, &*a.inner, t)? {
                    Some(t) => t.to_term().unwrap(),
                    None => return Ok(None),
                };

                inner_term.clear_annotations();
                for subt in a.annotations.iter() {
                    match subt {
                        Expr::UnrollVariadic(n) => {
                            let list = c
                                .bound_variables
                                .get(&n.name)
                                .expect(format!("Cannot resolve reference {}", n.name).as_str());
                            match list {
                                // Reference must resolve to list term
                                at::base::Term::LTerm(l) => {
                                    for elem in &l.terms {
                                        inner_term.add_annotation(elem.clone());
                                    }
                                }
                                _ => return Ok(None),
                            }
                        }
                        _ => {
                            let r = match self.reduce(c, &subt, t)? {
                                Some(t) => t.to_term().unwrap(),
                                None => return Ok(None),
                            };

                            inner_term.add_annotation(r);
                        }
                    }
                }

                Some(Rewriter::term_to_expr(&inner_term))
            }
            Expr::Text(t) => Some(Rewriter::term_to_expr(
                &at::base::Term::new_string_term(t.value.as_str()),
            )),
            Expr::List(l) => {
                self.bench_increment_count("fn:reduce:list");
                let mut res = at::base::LTerm {
                    terms: Vec::new(),
                    annotations: at::base::Annotations::empty(),
                };
                for e in &l.values {
                    let r = match self.reduce(c, &e, t)? {
                        Some(t) => t.to_term().unwrap(),
                        None => return Ok(None),
                    };

                    res.terms.push(r);
                }
                Some(Rewriter::term_to_expr(&at::base::Term::LTerm(res)))
            }
            Expr::Let(l) => {
                self.bench_increment_count("fn:reduce:let");
                let rhs_res = match self.reduce(c, &*l.rhs, t)? {
                    Some(t) => t.to_term().unwrap(),
                    None => return Ok(None),
                };

                match check_and_bind_match(&l.lhs, &rhs_res) {
                    Some(bindings) => {
                        let mut new_c = c.clone();
                        new_c.merge(bindings);
                        self.reduce(&new_c, &*l.body, t)?
                    }
                    None => None,
                }
            }
            Expr::ListCons(l) => {
                self.bench_increment_count("fn:reduce:listcons");
                let head_res = match self.reduce(c, &*l.head, t)? {
                    Some(t) => t.to_term().unwrap(),
                    None => return Ok(None),
                };

                match self.reduce(c, &*l.tail, t)? {
                    Some(t) => match t.to_term() {
                        Some(at::base::Term::LTerm(tail_res)) => {
                            let mut res = vec![head_res];
                            res.extend(tail_res.terms.into_iter());
                            Some(Rewriter::term_to_expr(
                                &at::base::Term::new_anot_list_term(res, tail_res.annotations),
                            ))
                        }
                        _ => None,
                    },
                    None => return Ok(None),
                }
            }
            st @ Expr::SimpleTerm(_) => Some(st.clone()),
        })
    }

    fn term_to_expr(t: &at::base::Term) -> Expr {
        Expr::SimpleTerm(t.clone())
    }

    fn expr_to_term(t: &Expr) -> at::base::Term {
        match t {
            Expr::SimpleTerm(t) => t.clone(),
            _ => panic!("Can only unwrap SimpleTerm"),
        }
    }

    fn check_is_term(e: Expr) -> Option<Expr> {
        match e {
            t @ Expr::SimpleTerm(_) => Some(t),
            _ => None,
        }
    }

    fn try_interp_function_instance(
        &mut self,
        c: &Context,
        f: &Function,
        meta: &Vec<Expr>,
        t: &at::base::Term,
    ) -> Result<Option<Expr>, Failure> {
        self.bench_increment_count("fn:try_interp_function_instance");

        // Check matcher and bind variables to terms
        let maybe_bindings = check_and_bind_match(&f.matcher, &t);
        if maybe_bindings.is_none() {
            return Ok(None);
        }
        let bindings = maybe_bindings.unwrap();

        let mut new_context: Context = Context::new();

        new_context.merge(bindings);

        // Bind metas
        for (p, a) in f.meta.iter().zip(meta.iter()) {
            match (p, a) {
                (Expr::FRef(param), arg @ Expr::FRef(_)) => {
                    let resolved_arg = self.reduce(c, arg, t)?;
                    match resolved_arg {
                        Some(Expr::FRef(f)) => {
                            new_context.bound_functions.insert(param.name.clone(), f);
                        }
                        _ => {
                            return Ok(None);
                        }
                    }
                }
                (Expr::Ref(f), e) => {
                    new_context.bound_variables.insert(
                        f.name.clone(),
                        self.reduce(c, e, t)?.unwrap().to_term().unwrap(),
                    );
                }
                _ => panic!("Unsupported meta expression"),
            }
        }

        self.reduce(&new_context, &f.body, t)
    }

    pub fn interp_function(
        &mut self,
        c: &Context,
        function: &FRef,
        t: at::base::Term,
    ) -> Result<Option<Expr>, Failure> {
        self.bench_increment_count("fn:interp_function");

        // Evaluate meta args
        let new_meta: Vec<Expr> = function
            .meta
            .iter()
            .map(|e| self.reduce(c, e, &t).unwrap().unwrap())
            .collect();

        // Try to dereference dynamically bound function
        let derefed_function = match c.bound_functions.get(&function.name) {
            Some(f) => {
                let merged_meta = f
                    .meta
                    .clone()
                    .into_iter()
                    .chain(new_meta.into_iter())
                    .collect::<Vec<Expr>>();
                FRef {
                    name: f.name.clone(),
                    meta: merged_meta,
                    ref_type: f.ref_type,
                }
            }
            None => FRef {
                name: function.name.clone(),
                meta: new_meta,
                ref_type: function.ref_type,
            },
        };

        self.bench_increment_count(derefed_function.name.as_str());

        // Find user-defined functions
        let fns: Vec<Function> = self
            .rules
            .functions
            .iter()
            .filter(|f| f.name == *derefed_function.name)
            .map(|f| f.clone())
            .collect();

        if fns.len() == 0 && !Rewriter::is_builtin(&derefed_function.name) {
            panic!("No function with this name: {}", derefed_function.name);
        }

        // Try user-defined function
        for f in fns {
            match self.try_interp_function_instance(c, &f, &derefed_function.meta, &t) {
                Err(mut fail) => {
                    fail.with_call(f.name);
                    return Err(fail);
                }
                Ok(res) => match res {
                    Some(t) => {
                        return Ok(Some(Rewriter::check_is_term(t).unwrap()));
                    }
                    None => {}
                },
            }
        }

        // Try built-in function
        match self.try_run_builtin_function(c, function, &t) {
            Some(t) => {
                return Ok(Some(t));
            }
            None => {}
        }

        if function.ref_type == FunctionReferenceType::Force {
            Err(Failure {
                error_message: String::from(format!(
                    "Failed to compute function {}",
                    function.name.clone()
                )),
                callstack: vec![],
                failure_context: c.clone(),
                term: t.clone(),
            })
        } else {
            Ok(None)
        }
    }

    #[allow(dead_code)]
    fn bench_increment_count(&mut self, _name: &str) {
        #[cfg(feature = "bench-instrumentation")]
        {
            match self.metrics.counters.get_mut(_name) {
                Some(c) => *c += 1,
                None => {
                    self.metrics.counters.insert(String::from(_name), 1);
                }
            };
        }
    }
}
