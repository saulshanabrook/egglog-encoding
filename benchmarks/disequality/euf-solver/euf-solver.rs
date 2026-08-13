#![allow(non_camel_case_types)]

use std::iter::Peekable;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs::{read};
use std::hash::Hash;
use std::time::{Duration, Instant};

use clap::{Parser, ValueEnum};
use clap::builder::PossibleValue;
use minisat;


macro_rules! sexpr_str { ($fun:expr, $args:expr, $arg_conv:expr) => {{
  let mut result = format!("({f}", f=$fun);
  for arg in $args { result.push(' '); result.push_str(&$arg_conv(arg)); }
  result.push(')');
  result
}};}


macro_rules! concat_vecs { ($list:expr,$($others:expr),+) => {
  $list.into_iter()$(.chain($others.into_iter()))+.collect()
}}


// The empty type
#[derive(Clone, Debug)]
enum Void {} impl Void {
  fn absurd_ref<T>(&self) -> T { Void::absurd(self.clone()) }
  fn absurd<T>(v: Void) -> T { match v {} }
}



// A Bijection
struct Assoc<S, T>(HashMap<S,T>, HashMap<T,S>);

impl<S: Eq + PartialEq + Clone + Hash, T: Eq + PartialEq + Clone + Hash> Assoc<S,T> {
  fn new() -> Assoc<S, T> {
    Assoc(HashMap::new(), HashMap::new())
  }

  fn assoc(&mut self, x: S, y: T) {
    if let Some(k) = self.1.get(&y) { self.0.remove(k); }
    if let Some(k) = self.0.get(&x) { self.1.remove(k); }
    self.0.insert(x.clone(), y.clone());
    self.1.insert(y, x);
  }

  fn get_left_or_assoc_with<F>(&mut self, y: T, xf: F) -> S where F: FnOnce() -> S {
    match self.1.get(&y).cloned() {
      Some(x) => x,
      None => {
        self.assoc(xf(), y.clone());
        self.1.get(&y).unwrap().clone()
      }
    }
  }

  fn iter(&self) -> impl Iterator<Item=(&S, &T)> {
    self.0.iter()
  }
}



#[derive(Debug, Clone, Eq, PartialEq)]
enum Token {
  OpenParen,
  CloseParen,
  Error(String),
  Comment,
  Numeral(usize),
  Decimal(usize, usize, usize), // before_comma, after_comma, len_after_comma
  Str(Vec<char>),
  SimpleSymbol(Vec<char>),
  QuotedSymbol(Vec<char>),
}

fn tokenize<'a>(contents: &'a Vec<char>) -> impl Iterator<Item=Token> + 'a {/*{{{*/
  use Token::*;

  struct Tokenizer<'a> {
    state: Option<Token>,
    contents: &'a Vec<char>,
    index: usize,
  }

  impl<'a> Iterator for Tokenizer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
      macro_rules! advance { ($state:expr) => {
        { self.index += 1; self.state = Some($state); }
      }}

      while self.index < self.contents.len() {
        let c = self.contents[self.index];

        match self.state {
          None => match c {
            ' ' | '\t' | '\n' | '\r' => { self.index += 1; },
            '(' => advance!(OpenParen),
            ')' => advance!(CloseParen),
            ';' => advance!(Comment),
            '"' => advance!(Str(vec![])),
            c if '0' <= c && c <= '9' => advance!(Numeral(c as usize - '0' as usize)),
            '|' => advance!(QuotedSymbol(vec![])),
            c => advance!(SimpleSymbol(vec![ c ])),
          },

          Some(OpenParen) => { break },
          Some(CloseParen) => { break },
          Some(Error(_)) => { break },

          Some(Comment) => match c {
            '\r' | '\n' => { self.index += 1; break; },
            _ => { self.index += 1; },
          },

          Some(Numeral(n)) => match c {
            ' ' | '\t' | '\r' | '\n' | '(' | ')' | '"' | '|' => { break; }
            '.' => advance!(Decimal(n, 0, 0)),
            c if '0' <= c && c <= '9' => advance!(Numeral(n * 10 + c as usize - '0' as usize)),
            _ => advance!(Error(format!("Illegal character in numeral: {c}"))),
          },

          Some(Decimal(n, m, l)) => match c {
            ' ' | '\t' | '\r' | '\n' | '(' | ')' | '"' | '|' => { break; }
            c if '0' <= c && c <= '9' => advance!(Decimal(n, m * 10 + c as usize - '0' as usize, l + 1)),
            _ => advance!(Error(format!("Illegal character in decimal: {c}"))),
          },

          Some(Str(ref mut chars)) => match c {
            '"' if self.index + 1 < self.contents.len() && self.contents[self.index+1] == '"'
              => { self.index += 2; chars.push('"'); },
            '"' => { self.index += 1; break; },
            c => { self.index += 1; chars.push(c); }
          },

          Some(SimpleSymbol(ref mut chars)) => match c {
            ' ' | '\r' | '\n' | '\t' | '(' | ')' | '|' => { break; },
            c => { self.index += 1; chars.push(c); }
          },

          Some(QuotedSymbol(ref mut chars)) => match c {
            '|' => { self.index += 1; break; },
            '\\' => advance!(Error("Illegal character in quoted symbol: \\".into())),
            c => { self.index += 1; chars.push(c); }
          },
        }
      }

      let val = self.state.clone();
      self.state = None;
      return val;
    }
  }

  Tokenizer { state: None, index: 0, contents }
}/*}}}*/


#[derive(Clone, Debug)]
enum Const {
  Unsupported,
  Symbol(String),
}

#[derive(Clone, Debug)]
enum SExpr {
  Atom(Const),
  List(Vec<SExpr>),
}

fn parse_script(tokenizer: &mut Peekable<impl Iterator<Item=Token>>) -> Option<Vec<SExpr>> {//{{{
  use Token::*;

  let mut tokenizer = tokenizer.filter(|t| match t {
    Comment | Error(_) => false,
    _ => true
  }).peekable();

  fn parse_sexpr<I>(tokenizer: &mut Peekable<I>) -> Option<SExpr> where I: Iterator<Item=Token> {
    use SExpr::*;
    use Const::*;
    match tokenizer.next()? {
      Token::Comment | Token::Error(_) => unreachable!(), // assumed these are filtered
      Token::Numeral(_) => Some(Atom(Unsupported)),
      Token::Decimal(_,_,_) => Some(Atom(Unsupported)),
      Token::Str(_) => Some(Atom(Unsupported)),
      Token::SimpleSymbol(s) | Token::QuotedSymbol(s) => Some(Atom(Symbol(s.into_iter().collect()))),
      Token::OpenParen => {
        let mut list = vec![];
        while *tokenizer.peek()? != CloseParen {
          list.push(parse_sexpr(tokenizer)?);
        }
        tokenizer.next(); // consume the closed paren
        Some(List(list))
      },
      Token::CloseParen => None,
    }
  }

  let mut result = vec![];
  while let Some(_) = tokenizer.peek() {
    result.push(parse_sexpr(&mut tokenizer)?);
  }

  Some(result)
}//}}}





// UF is the type representing an uninterpreted function
// N is the type of what can be negated
// E is the type of what can be equated
// T is to make Term an F-algebra
#[derive(Clone, Debug)]
enum Term<UF, N, E, T> {
  Const(bool),
  Ident(String),
  UnFun(UF, Vec<T>),
  Not(Box<N>),
  Equal(Box<E>, Box<E>),
  Distinct(Box<E>, Box<E>),
  And(Vec<T>),
  Or(Vec<T>),
}


// T is to make QuantTerm an F-algebra
#[derive(Clone, Debug)]
enum QuantTerm<T> {
  Forall(Vec<String>, T),
  Exists(Vec<String>, T),
  Unquant(T),
}

impl<T> QuantTerm<T> {
  fn map<S,F>(&self, f: F) -> QuantTerm<S> where F: FnOnce(&T) -> S { match self {
    QuantTerm::Forall(xs, t) => QuantTerm::Forall(xs.clone(), f(t)),
    QuantTerm::Exists(xs, t) => QuantTerm::Exists(xs.clone(), f(t)),
    QuantTerm::Unquant(t) => QuantTerm::Unquant(f(t)),
  }}
}



// Free quantification
// Free negation
// Uninterpreted Functions
// Equality
#[derive(Clone)]
struct Term_FQ_FN_UF_E(QuantTerm<Term<String, Self, Self, Self>>);


// Free quantification
// Free negation
// No Uninterpreted Functions
// Equality
#[derive(Clone)]
struct Term_FQ_FN_E(QuantTerm<Term<Void, Self, Self, Self>>);


// Free Quantification
// Restricted Negation (to identifiers)
// No Uninterpreted Functions
// Equality
#[derive(Clone)]
struct Term_FQ_RN_E(QuantTerm<Term<Void, String, Self, Self>>);


// No Quantification (Skolemization done and universals ignored)
// Restricted Negation (to identifiers)
// No Uninterpreted Functions
// Equality
#[derive(Clone)]
struct Term_RN_E(Term<Void, String, Self, Self>);


#[derive(Clone)]
struct Term_RN(Term<Void, String, Void, Self>);



impl Term_FQ_FN_UF_E {
  fn from(sexprs: &Vec<SExpr>) -> Term_FQ_FN_UF_E {//{{{
    use Term::*;
    use QuantTerm::*;
    use SExpr::*;
    use crate::Const::{Symbol, Unsupported};

    fn is_expr_keyword(x: &str) -> bool {
         x == "not" || x == "=" || x == "distinct" || x == "and" || x == "or" || x == "forall"
      || x == "exists" || x == "ite" || x == "let" || x == "!" || x == "=>" || x == "true"
      || x == "false" || x == "match" || x == "xor" || x == "par"
    }

    fn make_const(b: bool) -> Term_FQ_FN_UF_E {
      Term_FQ_FN_UF_E(Unquant(Const(b))) }

    fn make_ident(x: &str) -> Term_FQ_FN_UF_E {
      Term_FQ_FN_UF_E(Unquant(Ident(x.to_string()))) }

    fn make_unfun(f: &str, es: Vec<Term_FQ_FN_UF_E>) -> Term_FQ_FN_UF_E {
      Term_FQ_FN_UF_E(Unquant(UnFun(f.to_string(), es))) }

    fn make_not(e: Term_FQ_FN_UF_E) -> Term_FQ_FN_UF_E {
      Term_FQ_FN_UF_E(Unquant(Not(Box::new(e)))) }

    fn make_equal(e1: Term_FQ_FN_UF_E, e2: Term_FQ_FN_UF_E) -> Term_FQ_FN_UF_E {
      Term_FQ_FN_UF_E(Unquant(Equal(Box::new(e1), Box::new(e2)))) }

    fn make_distinct(e1: Term_FQ_FN_UF_E, e2: Term_FQ_FN_UF_E) -> Term_FQ_FN_UF_E {
      Term_FQ_FN_UF_E(Unquant(Distinct(Box::new(e1), Box::new(e2)))) }

    fn make_and(es: Vec<Term_FQ_FN_UF_E>) -> Term_FQ_FN_UF_E {
      Term_FQ_FN_UF_E(Unquant(And(es))) }

    fn make_or(es: Vec<Term_FQ_FN_UF_E>) -> Term_FQ_FN_UF_E {
      Term_FQ_FN_UF_E(Unquant(Or(es))) }

    fn make_forall(vs: Vec<String>, e: Term_FQ_FN_UF_E) -> Term_FQ_FN_UF_E {
      Term_FQ_FN_UF_E(Forall(vs, Term::And(vec![ e ]))) }

    fn make_exists(vs: Vec<String>, e: Term_FQ_FN_UF_E) -> Term_FQ_FN_UF_E {
      Term_FQ_FN_UF_E(Exists(vs, Term::And(vec![ e ]))) }

    #[derive(Clone)]
    enum Env {
      Empty(),
      Extended { bindings: HashMap<String, Term_FQ_FN_UF_E>, parent: Box<Env> }
    }

    impl Env {
      fn contains(&self, k: &String) -> bool { match self {
        Env::Empty() => false,
        Env::Extended { bindings, parent } => bindings.contains_key(k) || parent.contains(k)
      }}

      fn get(&self, k: &String) -> Option<Term_FQ_FN_UF_E> { match self {
        Env::Empty() => None,
        Env::Extended { bindings, parent } => bindings.get(k).cloned().or_else(|| parent.get(k))
      }}
    }

    macro_rules! with_bindings { ($lst:expr, $handler:expr) => {
      $lst.iter().filter_map(|expr| match expr {
        List(lst) => match &lst[..] {
          [Atom(Symbol(name)), t] => $handler(name, t),
          _ => None
        }
        _ => None
      })
    }}

    fn parse_term(sexpr: &SExpr, env: &Env) -> Term_FQ_FN_UF_E {
      let rec = |s: &SExpr| parse_term(s, env);
      match sexpr {
        // try this in z3 for a surprise: `(define-fun true () bool false) (assert true) (check-sat)`
        Atom(Symbol(x)) if env.contains(x) => env.get(x).unwrap(),
        Atom(Symbol(r#true)) if r#true == "true" => make_const(true),
        Atom(Symbol(r#false)) if r#false == "false" => make_const(false),
        Atom(Symbol(x)) => make_ident(x),
        Atom(_) => panic!("Only symbols are supported"),
        List(list) => match &list[..] {
          [] => panic!("ERROR: Empty expression not supported"),
          [List(_) | Atom(Unsupported), ..] =>
            panic!("ERROR: Identifier expected for application"),
          [Atom(Symbol(cmd)), rest @ ..] => match (cmd.as_str(), rest) {
            ("match", _) => panic!("ERROR: match is not supported"),
            ("par", _) => panic!("ERROR: par is not supported"),
            ("!", [e, ..]) => rec(e),
            ("not", [e]) => make_not(rec(e)),
            ("=>", [e1, e2]) => make_or(vec![ make_not(rec(e1)), rec(e2) ]),
            ("and", es) => make_and(es.iter().map(rec).collect()),
            ("or", es) => make_or(es.iter().map(rec).collect()),
            ("xor", [e1, e2]) => {
              let e1 = rec(e1);
              let e2 = rec(e2);
              make_and(vec![ make_or(vec![ e1.clone(), e2.clone() ]), make_not(make_and(vec![ e1, e2 ])) ])
            },
            ("=", [e1, e2]) => make_equal(rec(e1), rec(e2)),
            ("distinct", [e1, e2]) => make_distinct(rec(e1), rec(e2)),
            ("distinct", [] | [_]) => panic!("ERROR: distinct needs at least 2 arguments"),
            ("distinct", more) => {
              let mut pairwise = vec![];
              for i in 0..more.len() { for j in i+1..more.len() {
                pairwise.push(make_distinct(rec(&more[i]), rec(&more[j])));
              }}
              make_and(pairwise)
            },
            ("ite", [e1, e2, e3]) => { // (e1 -> e2) & (!e1 -> e3) = (!e1 | e2) & (e1 | e3)
              let e1 = rec(e1);
              let e2 = rec(e2);
              let e3 = rec(e3);
              make_and(vec![ make_or(vec![make_not(e1.clone()), e2]), make_or(vec![e1, e3]) ])
            },
            ("forall", [List(args), t]) => {
              let args = with_bindings!(args, |name: &String, _| Some(name.clone())).collect();
              make_forall(args, rec(t))
            },
            ("exists", [List(args), t]) => {
              let args = with_bindings!(args, |name: &String, _| Some(name.clone())).collect();
              make_exists(args, rec(t))
            },
            ("let", [List(xs), t]) => {
              let bindings = with_bindings!(xs, |x: &String, t| Some((x.clone(), rec(t)))).collect();
              parse_term(t, &Env::Extended { bindings, parent: Box::new(env.clone()) })
            }
            (cmd, ..) if is_expr_keyword(cmd) => panic!("Wrong arguments to {cmd}"),
            (f,[]) => rec(&Atom(Symbol(f.to_string()))),
            (f, args) => make_unfun(f, args.iter().map(rec).collect()),
          }
        }
      }
    }

    let mut asserts = vec![];
    let mut env = Env::Empty();

    for sexpr in sexprs { match sexpr {
      SExpr::List(list) => match &list[..] {
        [Atom(Symbol(assert)), e] if assert == "assert" => {
          asserts.push(parse_term(e, &env));
        },
        [Atom(Symbol(definefun)), Atom(Symbol(name)), _, _, e] if definefun == "define-fun" => {
          env = Env::Extended {
            parent: Box::new(env.clone()),
            bindings: HashMap::from([ (name.clone(), parse_term(e, &env)) ])
          };
        }
        _ => {}
      }
      _ => {}
    }}

    make_and(asserts)
  }//}}}

  fn unique_vars(&self) -> Term_FQ_FN_UF_E {//{{{
    use Term::*;
    use QuantTerm::*;

    type T = Term_FQ_FN_UF_E;
    type TTerm = Term<String, T, T, T>;

    fn aux_quant(t: &T, env: &mut HashMap<String, usize>) -> T {
      Term_FQ_FN_UF_E(match &t.0 {
        Forall(xs, t) => {
          for x in xs { env.entry(x.clone()).and_modify(|c| *c += 1).or_insert(0); }
          Forall(xs.iter().map(|x| var_name(x, env)).collect(), aux(t, env))
        },
        Exists(xs, t) => {
          for x in xs { env.entry(x.clone()).and_modify(|c| *c += 1).or_insert(0); }
          Exists(xs.iter().map(|x| var_name(x, env)).collect(), aux(t, env))
        },
        Unquant(t) => Unquant(aux(t, env)),
      })
    }

    fn var_name(x: &String, env: &HashMap<String, usize>) -> String {
      let c = env.get(x).cloned().unwrap_or(0);
      if c == 0 { x.clone() } else { format!("@{c}.{x}") }
    }

    fn aux(t: &TTerm, env: &mut HashMap<String, usize>) -> TTerm {
      let mut rec = |t| aux_quant(t, env);
      match t {
        Const(b) => Const(*b),
        Ident(x) => Ident(var_name(x, env)),
        UnFun(f, args) => UnFun(f.clone(), args.iter().map(rec).collect()),
        Not(t) => Not(Box::new(rec(t))),
        And(ts) => And(ts.iter().map(rec).collect()),
        Or(ts) => Or(ts.iter().map(rec).collect()),
        Equal(t1, t2) => Equal(Box::new(rec(t1)), Box::new(rec(t2))),
        Distinct(t1, t2) => Distinct(Box::new(rec(t1)), Box::new(rec(t2))),
      }
    }

    let mut env = HashMap::new();
    aux_quant(self, &mut env)
  }//}}}

  fn eliminate_uf(&self) -> (Term_FQ_FN_E, Assoc<String, (String, Vec<String>)>) {//{{{
    use Term::*;
    use QuantTerm::*;

    type In = Term_FQ_FN_UF_E;
    type InTerm = Term<String, In, In, In>;
    type Out = Term_FQ_FN_E;
    type OutTerm = Term<Void, Out, Out, Out>;

    // used for pulling out boolean formulas from inside UF,
    // so (f a (not b)) becomes (f a c) with c=(not b) in the Env
    // at the end, all the equalities recorded here will be asserted
    type Env = HashMap<String, Out>;

    // used for flattening UF, so (f a (g b)) becomes (f a c) with c=(g b) in the UFEnv
    // these equalities must not be asserted!
    // (g b) could be any type, not necessarily bool, so asserting it breaks this.
    // these equalities are meant to be handled by the EUF theory using the e-graph
    type UFEnv = Assoc<String, (String, Vec<String>)>;

    fn var(c: &mut usize) -> String { *c += 1; format!("@uf.{c}") }

    fn aux_quant(t: &In, c: &mut usize, uf_terms: &mut UFEnv, env: &mut Env) -> Out {
      Term_FQ_FN_E(t.0.map(|t| aux(t, c, uf_terms, env)))
    }

    fn aux(t: &InTerm, c: &mut usize, uf_terms: &mut UFEnv, env: &mut Env) -> OutTerm {
      let mut rec = |t| aux_quant(t, c, uf_terms, env);
      match t {
        Const(b) => Const(*b),
        Ident(x) => Ident(x.clone()),
        Not(t) => Not(Box::new(rec(t))),
        Equal(t1, t2) => { let t1 = rec(t1); let t2 = rec(t2); Equal(Box::new(t1), Box::new(t2)) },
        Distinct(t1, t2) => { let t1 = rec(t1); let t2 = rec(t2); Distinct(Box::new(t1), Box::new(t2)) },
        And(ts) => And(ts.iter().map(rec).collect()),
        Or(ts) => Or(ts.iter().map(rec).collect()),
        UnFun(f, args) => {
          let mut new_args: Vec<String> = vec![];
          for arg in args {
            match aux_quant(arg, c, uf_terms, env).0 {
              Unquant(Ident(x)) => { new_args.push(x.clone()); }
              arg => {
                let new_var = var(c);
                env.insert(new_var.clone(), Term_FQ_FN_E(arg));
                new_args.push(new_var);
              }
            }
          }
          let ident = uf_terms.get_left_or_assoc_with((f.clone(), new_args), || var(c));
          Ident(ident)
        }
      }
    }

    let mut uf_terms = Assoc::new();
    let mut env = HashMap::new();
    let t = aux_quant(self, &mut 0, &mut uf_terms, &mut env);

    (if env.len() == 0 {
      t
    } else {
      let mut asserts = vec![ t ];
      for (v, t) in env {
        asserts.push(Term_FQ_FN_E(Unquant(
          Equal(Box::new(Term_FQ_FN_E(Unquant(Ident(v.clone())))),
                Box::new(t)))));
      }
      Term_FQ_FN_E(Unquant(And(asserts)))
    }, uf_terms)
  }//}}}
}

impl Term_FQ_FN_E {
  fn push_not_in(&self) -> Term_FQ_RN_E {//{{{
    use Term::*;
    use QuantTerm::*;

    type In = Term_FQ_FN_E;
    type InTerm = Term<Void, In, In, In>;
    type Out = Term_FQ_RN_E;
    type OutTerm = Term<Void, String, Out, Out>;

    fn aux_quant(t: &In) -> Out {
      Term_FQ_RN_E(t.0.map(|t| aux(t)))
    }

    fn aux(t: &InTerm) -> OutTerm {
      let rec = |t| aux_quant(t);
      match t {
        Const(b) => Const(*b),
        Ident(x) => Ident(x.clone()),
        Equal(t1, t2) => { let t1 = rec(t1); let t2 = rec(t2); Equal(Box::new(t1), Box::new(t2)) },
        Distinct(t1, t2) => { let t1 = rec(t1); let t2 = rec(t2); Distinct(Box::new(t1), Box::new(t2)) },
        UnFun(f, _) => f.absurd_ref(),
        And(ts) => And(ts.iter().map(rec).collect()),
        Or(ts) => Or(ts.iter().map(rec).collect()),
        Not(t) => match &t.0 {
          Forall(xs, t) => And(vec![ Term_FQ_RN_E(
            // build an existential (surrounded by an `and` because we must return a Term here)
            // surround the body with a Not, and recurse on it
            Exists(xs.clone(), aux(&Not(Box::new(Term_FQ_FN_E(Unquant(t.clone()))))))) ]),
          Exists(xs, t) => And(vec![ Term_FQ_RN_E(
            Forall(xs.clone(), aux(&Not(Box::new(Term_FQ_FN_E(Unquant(t.clone()))))))) ]),
          Unquant(t) => match t {
            Const(b) => Const(!b),
            Ident(x) => Not(Box::new(x.clone())),
            Not(t) => And(vec![ rec(t) ]),
            Equal(t1, t2) => { let t1 = rec(t1); let t2 = rec(t2); Distinct(Box::new(t1), Box::new(t2)) },
            Distinct(t1, t2) => { let t1 = rec(t1); let t2 = rec(t2); Equal(Box::new(t1), Box::new(t2)) },
            UnFun(f, _) => f.absurd_ref(),
            And(ts) =>
              Or(ts.iter().map(|t| Term_FQ_RN_E(Unquant(aux(&Not(Box::new(t.clone())))))).collect()),
            Or(ts) =>
              And(ts.iter().map(|t| Term_FQ_RN_E(Unquant(aux(&Not(Box::new(t.clone())))))).collect()),
          }
        }
      }
    }

    aux_quant(self)
  }//}}}
}

impl Term_FQ_RN_E {
  fn skolemize(&self) -> (Term_RN_E, Assoc<String, (String, Vec<String>)>) {//{{{
    use Term::*;
    use QuantTerm::*;

    type In = Term_FQ_RN_E;
    type InTerm = Term<Void, String, In, In>;
    type Out = Term_RN_E;
    type OutTerm = Term<Void, String, Out, Out>;

    fn aux_quant(t: &In, uni_quant_vars: &Vec<String>, env: &mut Assoc<String, (String, Vec<String>)>) -> Out {
      Term_RN_E(match &t.0 {
        Unquant(t) => aux(t, uni_quant_vars, env),
        Forall(xs, t) => aux(t, &concat_vecs!(uni_quant_vars.clone(), xs.clone()), env),
        Exists(xs, t) => {
          for x in xs { // guaranteed to be unique (when unique_vars is in the pipeline)
            env.assoc(x.clone(), (format!("@skol.{x}"), uni_quant_vars.clone()));
          }
          aux(t, uni_quant_vars, env)
        }
      })
    }

    fn aux(t: &InTerm, uni_quant_vars: &Vec<String>, env: &mut Assoc<String, (String, Vec<String>)>) -> OutTerm {
      let mut rec = |t| aux_quant(t, uni_quant_vars, env);
      match t {
        Const(b) => Const(*b),
        Ident(x) => Ident(x.clone()),
        UnFun(f, _) => f.absurd_ref(),
        Not(x) => Not(x.clone()),
        Equal(t1, t2) => Equal(Box::new(rec(t1)), Box::new(rec(t2))),
        Distinct(t1, t2) => Distinct(Box::new(rec(t1)), Box::new(rec(t2))),
        And(ts) => And(ts.iter().map(rec).collect()),
        Or(ts) => Or(ts.iter().map(rec).collect()),
      }
    }

    let mut env = Assoc::new();
    let t = aux_quant(self, &vec![], &mut env);
    return (t, env)
  }//}}}
}

impl Term_RN_E {
  // Keep in mind that some equalities are "logical equivalences" and others are "theory equalities"
  // for example: (= (not a b) (and c d)) vs (= (f a e) (g c d))
  // since we already eliminated UF then the second equality looks like (= i j)
  // and we seperate them like this:
  // - theory equalities are (dis)equalities between two identifiers which will be returned in the hashmap
  // - equivalences are all other (dis)equalities which will be rewritten appropriately
  fn eliminate_eq(&self) -> (Term_RN, Assoc<String, (String, String)>) { //{{{
    use Term::*;

    fn new_eq_var(x1: &String, x2: &String, c: &mut usize, env: &mut Assoc<String, (String,String)>) -> String {
      env.get_left_or_assoc_with((x1.clone(), x2.clone()), || {
        *c += 1;
        format!("@eq{c}")
      })
    }

    fn aux(t: &Term_RN_E, counter: &mut usize, env: &mut Assoc<String, (String,String)>) -> Term_RN {
      let mut rec = |t| aux(t, counter, env);
      Term_RN(match &t.0 {
        Const(b) => Const(*b),
        Ident(x) => Ident(x.clone()),
        UnFun(f, _) => f.absurd_ref(),
        Not(x) => Not(x.clone()),
        And(ts) => And(ts.iter().map(rec).collect()),
        Or(ts) => Or(ts.iter().map(rec).collect()),
        Equal(t1, t2) => match (rec(t1).0, rec(t2).0) {
          (Ident(x1), Ident(x2)) => Ident(new_eq_var(&x1, &x2, counter, env)),
          (t1, t2) => Or(vec![ Term_RN(And(vec![ Term_RN(t1.clone()), Term_RN(t2.clone()) ])),
                               Term_RN(And(vec![ Term_RN(t1).negate(), Term_RN(t2).negate() ])) ])
        },
        Distinct(t1, t2) => match (rec(t1).0, rec(t2).0) {
          (Ident(x1), Ident(x2)) => Not(Box::new(new_eq_var(&x1, &x2, counter, env))),
          (t1, t2) => And(vec![ Term_RN(Or(vec![ Term_RN(t1.clone()), Term_RN(t2.clone()) ])),
                                Term_RN(Or(vec![ Term_RN(t1).negate(), Term_RN(t2).negate() ])) ])
        },
      })
    }

    let mut env = Assoc::new();
    let t = aux(self, &mut 0, &mut env);
    return (t, env)
  }//}}}
}

impl Term_RN {
  fn negate(&self) -> Term_RN {//{{{
    use Term::*;

    Term_RN(match &self.0 {
      UnFun(t, _) => t.absurd_ref(),
      Equal(t, _) | Distinct(t, _) => t.absurd_ref(),
      Const(b) => Const(!b),
      Ident(x) => Not(Box::new(x.clone())),
      Not(x) => Ident(x.to_string()),
      And(ts) => Or(ts.iter().map(|t| t.negate()).collect()),
      Or(ts) => And(ts.iter().map(|t| t.negate()).collect()),
    })
  }//}}}

  fn cnf(&self) -> CNF {//{{{
    use Term::*;

    fn cnf(t: &Term_RN) -> Vec<Vec<SatSymb>> { match &t.0 {
      UnFun(t, _) => t.absurd_ref(),
      Equal(t, _) | Distinct(t, _) => t.absurd_ref(),
      Const(b) => vec![vec![ SatSymb::Const(*b) ]],
      Ident(x) => vec![vec![ SatSymb::Pos(x.clone()) ]],
      Not(x) => vec![vec![ SatSymb::Neg(*x.clone()) ]],
      And(ts) => ts.iter().flat_map(cnf).collect(),
      Or(ts) if ts.len() == 0 => vec![vec![ SatSymb::Const(false) ]],
      Or(ts) if ts.len() == 1 => cnf(&ts[0]),
      Or(ts) => {
        let n = ts.len();
        let cnf1 = cnf(&Term_RN(Or(ts[0..n/2].to_vec())));
        let cnf2 = cnf(&Term_RN(Or(ts[n/2..n].to_vec())));

        let mut result = vec![];
        for p in cnf1 { for q in &cnf2 {
          result.push(concat_vecs!(p.clone(), q.clone()));
        }}

        result
      }
    }}

    // returning None means the clause is always true
    fn compress(clause: &Vec<SatSymb>) -> Option<Vec<SatSymb>> {
      use SatSymb::*;

      let mut pos = HashSet::new();
      let mut neg = HashSet::new();
      let mut new_clause = vec![];
      let mut has_false = false;

      for c in clause { match c {
        Const(true) => { return None }
        Const(false) => { has_false = true }
        Pos(x) => if neg.contains(x) { return None }
                  else if !pos.contains(x) { pos.insert(x.clone()); new_clause.push(c.clone()) }
        Neg(x) => if pos.contains(x) { return None }
                  else if !neg.contains(x) { neg.insert(x.clone()); new_clause.push(c.clone()) }
      }}

      if new_clause.len() == 0 && has_false {
        Some(vec![ Const(false) ])
      } else if new_clause.len() == 0 && !has_false {
        None
      } else {
        Some(new_clause)
      }
    }

    CNF(cnf(self).iter().filter_map(compress).collect())
  }//}}}
}


#[derive(Clone, PartialEq, Eq)]
enum SatSymb {
  Const(bool),
  Pos(String),
  Neg(String),
}

struct CNF(Vec<Vec<SatSymb>>);


impl CNF {
  fn solve(&self) -> impl Iterator<Item=(Vec<(String, bool)>, Duration)> {//{{{
    use SatSymb::*;

    let mut sat = minisat::Solver::new();
    let mut lit_map = HashMap::new();

    for disjunct in &self.0 {
      let clause = disjunct.iter().map(|c| match c {
        Const(b) => (*b).into(),
        Pos(x)   => *lit_map.entry(x.clone()).or_insert_with(|| sat.new_lit()),
        Neg(x)   => !*lit_map.entry(x.clone()).or_insert_with(|| sat.new_lit()),
      }).collect::<Vec<_>>();
      sat.add_clause(clause);
    }

    struct SolverIter {
      solver: minisat::Solver,
      lits: HashMap<String, minisat::Bool>,
    }

    impl Iterator for SolverIter {
      type Item = (Vec<(String, bool)>, Duration);

      fn next(&mut self) -> Option<Self::Item> {
        let start_sat = Instant::now();
        let model = self.solver.solve().ok()?;
        let time_in_sat = start_sat.elapsed();

        let mut result = vec![];

        // we will add `!(model(a) and model(b) and ...) = !model(a) or !model(b) or ...``` to the
        // solver to prohibit this solution and select the next one
        let new_clause = self.lits.iter().map(|(name, var)| {
          result.push((name.clone(), model.value(var)));
          if model.value(var) { !*var } else { *var }
        }).collect::<Vec<_>>();

        self.solver.add_clause(new_clause);
        return Some((result, time_in_sat))
      }
    }

    SolverIter { solver: sat, lits: lit_map }
  }//}}}
}





struct EUFSolverConfig {
  debug: bool,
  exit_on_first_sat: bool,
  collect_stats: bool,
  use_equality_embedding: bool,
}

struct EGraphStat {
  num_nodes: usize,
  num_classes: usize,
  time_in_sat: Duration,
  time_in_egraph: Duration,
}

struct EUFSolverResult {
  sat: bool,
  egraph_stats_per_solution: Vec<EGraphStat>,
  time_in_egraph_setup: Duration,
  full_time: Duration,
}

enum EUFSolver {} impl EUFSolver {
  fn to_cnf(t: &Term_FQ_FN_UF_E)
    -> (CNF, HashMap<String, (String, Vec<String>)>, Assoc<String, (String, String)>)
  {//{{{
    let (t, uf_env) = t.unique_vars()
                       .eliminate_uf();
    let (t, skols)  = t.push_not_in()
                       .skolemize();
    let (t, eq_env) = t.eliminate_eq();
    let cnf = t.cnf();

    (cnf, uf_env.0.into_iter().chain(skols.0.into_iter()).collect::<HashMap<_,_>>(), eq_env)
  }//}}}

  fn check_sat_ee(config: &EUFSolverConfig, t: &Term_FQ_FN_UF_E) -> EUFSolverResult {//{{{
    use egg::{EGraph, SymbolLang, Runner, multi_rewrite as mrw, rewrite as rw};

    let start_full_solution_time = Instant::now();

    let (cnf, theory_eqs, eq_names) = EUFSolver::to_cnf(t);

    let start_egraph_setup = Instant::now();

    let mut egraph: EGraph<SymbolLang, ()> = Default::default();

    for (x, (f, args)) in theory_eqs.into_iter() {
      let f_args = sexpr_str!(f, args, |__|__);
      let id1 = egraph.add_expr(&x.parse().unwrap());
      let id2 = egraph.add_expr(&f_args.parse().unwrap());
      if config.debug { eprintln!("{x} = {f_args}"); }
      egraph.union(id1, id2);
    }

    for (e, (x, y)) in eq_names.iter() {
      let id1 = egraph.add_expr(&e.parse().unwrap());
      let id2 = egraph.add_expr(&format!("(eq {x} {y})").parse().unwrap());
      if config.debug { eprintln!("{e} = (eq {x} {y})"); }
      egraph.union(id1, id2);
    }

    egraph.rebuild();

    let mut result = EUFSolverResult {
      sat: false,
      egraph_stats_per_solution: vec![],
      time_in_egraph_setup: start_egraph_setup.elapsed(),
      full_time: Duration::ZERO,
    };

    for (solution, time_in_sat) in cnf.solve() {
      let time_in_egraph = Instant::now();
      let mut egraph = egraph.clone();

      for (var, val) in solution {
        let id1 = egraph.add_expr(&var.parse().unwrap());
        let id2 = egraph.add_expr(&format!("{val}").parse().unwrap());
        egraph.union(id1, id2);
      }

      // apply the saturation strategy
      let mut egraph = Runner::default().with_egraph(egraph).run(&[
        mrw!("e0"; "?t = true = (eq ?x ?y)" => "?x = ?y"),
        mrw!("e1"; "?f = false = (eq ?x ?y)" => "?f = (eq ?y ?x)"),
        mrw!("e2"; "?f = false = (eq ?x ?y), ?t = true" => "?t = (eq ?x ?x), ?t = (eq ?y ?y)"),
      ]).egraph;

      egraph.rebuild();

      let t = egraph.add_expr(&format!("true").parse().unwrap());
      let f = egraph.add_expr(&format!("false").parse().unwrap());

      if config.collect_stats {
        result.egraph_stats_per_solution.push(EGraphStat {
          num_nodes: egraph.total_size(),
          num_classes: egraph.number_of_classes(),
          time_in_sat: time_in_sat,
          time_in_egraph: time_in_egraph.elapsed(),
        });
      }

      result.sat |= t != f;
      if result.sat && config.exit_on_first_sat {
        result.full_time = start_full_solution_time.elapsed();
        return result
      }
    }

    result.full_time = start_full_solution_time.elapsed();
    return result
  }//}}}

  fn check_sat_de(config: &EUFSolverConfig, t: &Term_FQ_FN_UF_E) -> EUFSolverResult {//{{{
    use disegg::{EGraph, SymbolLang};

    let start_full_solution_time = Instant::now();

    let (cnf, theory_eqs, eq_names) = EUFSolver::to_cnf(t);

    let start_egraph_setup = Instant::now();

    let mut egraph: EGraph<SymbolLang, ()> = Default::default();

    for (x, (f, args)) in theory_eqs.into_iter() {
      let id1 = egraph.add_expr(&x.parse().unwrap());
      let id2 = egraph.add_expr(&sexpr_str!(f, &args, |x|x).parse().unwrap());
      if config.debug { eprintln!("{x} = {}", sexpr_str!(f, args, |__|__)); }
      egraph.union(id1, id2);
    }

    let mut result = EUFSolverResult {
      sat: false,
      egraph_stats_per_solution: vec![],
      time_in_egraph_setup: start_egraph_setup.elapsed(),
      full_time: Duration::ZERO, // will be changed later
    };

    for (solution, time_in_sat) in cnf.solve() {
      let time_in_egraph = Instant::now();
      let mut egraph = egraph.clone();

      for (var, val) in solution {
        if let Some((x, y)) = eq_names.0.get(&var) {
          let id1 = egraph.add_expr(&x.parse().unwrap());
          let id2 = egraph.add_expr(&y.parse().unwrap());
          if val {
            egraph.union(id1, id2);
          } else {
            egraph.disunion(id1, id2);
          }
        } else {
          let id1 = egraph.add_expr(&var.parse().unwrap());
          let id2 = egraph.add_expr(&format!("{val}").parse().unwrap());
          egraph.union(id1, id2);
        }
      }

      egraph.rebuild();

      if config.collect_stats {
        result.egraph_stats_per_solution.push(EGraphStat {
          num_nodes: egraph.total_size(),
          num_classes: egraph.number_of_classes(),
          time_in_egraph: time_in_egraph.elapsed(),
          time_in_sat,
        });
      }

      result.sat |= egraph.is_consistent(); // no contradiction found
      if result.sat && config.exit_on_first_sat {
        result.full_time = start_full_solution_time.elapsed();
        return result
      }
    }

    result.full_time = start_full_solution_time.elapsed();
    return result
  }//}}}

  fn check_sat(config: &EUFSolverConfig, t: &Term_FQ_FN_UF_E) -> EUFSolverResult {//{{{
    if config.use_equality_embedding {
      EUFSolver::check_sat_ee(config, t) // equality embedding, not estonian
    } else {
      EUFSolver::check_sat_de(config, t) // disequality edges, not german
    }
  }//}}}
}

#[derive(Parser)]
#[command(about, long_about=None)]
struct Cli {
  /// The path to a SMTLIB2 file
  file: String,
  /// Use disegg instead of egg
  #[arg(short, long, default_value_t = false)]
  disegg: bool,
  /// Display the stats
  #[arg(short, long, default_value_t = false)]
  stats: bool,
}


fn main() -> Result<(),()> {
  let Cli { file, disegg, stats, } = Cli::parse();

  let contents = read(&file).map_err(|_| { eprintln!("ERROR: Could not read file"); () })?
                  .into_iter().map(|c: u8| c.into()).collect();

  let sexprs = parse_script(&mut tokenize(&contents).peekable()).ok_or(())?;
  let t = Term_FQ_FN_UF_E::from(&sexprs);

  let result = EUFSolver::check_sat(&EUFSolverConfig {
    collect_stats: stats,
    debug: false,
    exit_on_first_sat: true,
    use_equality_embedding: !disegg,
  }, &t);

  if stats {
    println!("file,status,egraph setup time,full time,sat solution,nodes,classes,sat time,egraph time");
    for (i, stat) in result.egraph_stats_per_solution.iter().enumerate() {
      println!("{},{},{:.3?},{:.3?},{},{},{},{:.3?},{:.3?}",
        file,
        if result.sat { "sat" } else { "unsat" },
        result.time_in_egraph_setup,
        result.full_time,
        i,
        stat.num_nodes,
        stat.num_classes,
        stat.time_in_sat,
        stat.time_in_egraph,
        );
    }
  } else {
    println!("{file}: {}", if result.sat { "sat" } else { "unsat" });
  }

  Ok(())
}
