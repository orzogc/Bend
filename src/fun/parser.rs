use crate::{
  fun::{
    display::DisplayFn, Adt, Book, CtrField, Definition, FanKind, MatchRule, Name, Num, Op, Pattern, Rule,
    Tag, Term, STRINGS,
  },
  imp::parser::PyParser,
  maybe_grow,
};
use highlight_error::highlight_error;
use TSPL::Parser;

// Bend grammar description:
// <Book>       ::= (<Data> | <Rule>)*
// <ADT>        ::= "type" <Name> "=" ( <Name> | "(" <Name> (<Name>)* ")" )+
// <Rule>       ::= ("(" <Name> <Pattern>* ")" | <Name> <Pattern>*) "=" <Term>
// <Pattern>    ::= "(" <Name> <Pattern>* ")" | <NameEra> | <Number> | "(" <Pattern> ("," <Pattern>)+ ")"
// <Term>       ::=
//   <Number> | <NumOp> | <Tup> | <App> | <Group> | <Nat> | <Lam> | <UnscopedLam> | <Bend> | <Fold> |
//   <Use> | <Dup> | <LetTup> | <Let> | <Bind> | <Match> | <Switch> | <Era> | <UnscopedVar> | <Var>
// <Lam>        ::= <Tag>? ("λ"|"@") <NameEra> <Term>
// <UnscopedLam>::= <Tag>? ("λ"|"@") "$" <Name> <Term>
// <NumOp>      ::= "(" <Operator> <Term> <Term> ")"
// <Tup>        ::= "(" <Term> ("," <Term>)+ ")"
// <App>        ::= <Tag>? "(" <Term> (<Term>)+ ")"
// <Group>      ::= "(" <Term> ")"
// <Use>        ::= "use" <Name> "=" <Term> ";"? <Term>
// <Let>        ::= "let" <NameEra> "=" <Term> ";"? <Term>
// <Bind>       ::= "do" <Name> "{" <Ask> "}"
// <Ask>        ::= "ask" <Pattern> "=" <Term> ";" <Term> | <Term>
// <LetTup>     ::= "let" "(" <NameEra> ("," <NameEra>)+ ")" "=" <Term> ";"? <Term>
// <Dup>        ::= "let" <Tag>? "{" <NameEra> (","? <NameEra>)+ "}" "=" <Term> ";"? <Term>
// <List>       ::= "[" (<Term> ","?)* "]"
// <String>     ::= "\"" (escape sequence | [^"])* "\""
// <Char>       ::= "'" (escape sequence | [^']) "'"
// <Match>      ::= "match" <Name> ("=" <Term>)? ("with" <Var> (","? <Var>)*)? "{" <MatchArm>+ "}"
// <MatchArm>   ::= "|"? <Pattern> ":" <Term> ";"?
// <Switch>     ::= "switch" <Name> ("=" <Term>)? ("with" <Var> (","? <Var>)*)? "{" <SwitchArm>+ "}"
// <SwitchArm>  ::= "|"? (<Num>|"_") ":" <Term> ";"?
// <Var>        ::= <Name>
// <UnscopedVar>::= "$" <Name>
// <NameEra>    ::= <Name> | "*"
// <Era>        ::= "*"
// <Tag>        ::= "#" <Name>
// <Name>       ::= [_\-./a-zA-Z0-9]+
// <Number>     ::= ([0-9]+ | "0x"[0-9a-fA-F]+ | "0b"[01]+)
// <Operator>   ::= ( "+" | "-" | "*" | "/" | "%" | "==" | "!=" | "<<" | ">>" | "<=" | ">=" | "<" | ">" | "^" )

pub type ParseResult<T> = std::result::Result<T, String>;

pub struct TermParser<'i> {
  input: &'i str,
  index: usize,
}

impl<'a> TermParser<'a> {
  pub fn new(input: &'a str) -> Self {
    Self { input, index: 0 }
  }

  /* AST parsing functions */

  pub fn parse_book(&mut self, default_book: Book, builtin: bool) -> ParseResult<Book> {
    let mut book = default_book;
    let mut indent = self.advance_newlines();
    let mut last_rule = None;
    while !self.is_eof() {
      let ini_idx = *self.index();

      // Record type definition
      if self.try_parse_keyword("object") {
        let mut prs = PyParser { input: self.input, index: *self.index() };
        let (obj, nxt_indent) = prs.parse_object(indent)?;
        self.index = prs.index;
        let end_idx = *self.index();
        prs.add_object(obj, &mut book, ini_idx, end_idx, builtin)?;
        indent = nxt_indent;
        last_rule = None;
        continue;
      }

      // Imp function definition
      if self.try_parse_keyword("def") {
        let mut prs = PyParser { input: self.input, index: *self.index() };
        let (def, nxt_indent) = prs.parse_def(indent)?;
        self.index = prs.index;
        let end_idx = *self.index();
        prs.add_def(def, &mut book, ini_idx, end_idx, builtin)?;
        indent = nxt_indent;
        last_rule = None;
        continue;
      }

      // Fun/Imp type definition
      if self.try_parse_keyword("type") {
        self.skip_trivia();
        let rewind_index = self.index;

        let _ = self.labelled(|p| p.parse_top_level_name(), "datatype name")?;

        if self.starts_with(":") {
          let mut prs = PyParser { input: self.input, index: rewind_index };
          let (r#enum, nxt_indent) = prs.parse_type(indent)?;
          self.index = prs.index;
          let end_idx = *self.index();
          prs.add_type(r#enum, &mut book, ini_idx, end_idx, builtin)?;
          indent = nxt_indent;
          last_rule = None;
          continue;
        } else {
          self.index = rewind_index;
          let (nam, adt) = self.parse_datatype(builtin)?;
          let end_idx = *self.index();
          self.with_ctx(book.add_adt(nam, adt), ini_idx, end_idx)?;
          indent = self.advance_newlines();
          last_rule = None;
          continue;
        }
      }

      // Import declaration
      if self.try_parse_keyword("use") {
        let import = self.parse_import()?;
        book.imports.insert(import.clone());
        indent = self.advance_newlines();
        last_rule = None;
        continue;
      }

      // Fun function definition
      let ini_idx = *self.index();
      let (name, rule) = self.parse_rule()?;
      let end_idx = *self.index();
      // Add to book
      if let Some(def) = book.defs.get_mut(&name) {
        if let Some(last_rule) = last_rule {
          if last_rule == name {
            // Continuing with a new rule to the current definition
            def.rules.push(rule);
          } else {
            // Trying to add a new rule to a previous definition, coming from a different rule.
            let msg = format!("Redefinition of function '{name}'");
            return self.with_ctx(Err(msg), ini_idx, end_idx);
          }
        } else {
          // Trying to add a new rule to a previous definition, coming from another kind of top-level.
          let msg = format!("Redefinition of function '{name}'");
          return self.with_ctx(Err(msg), ini_idx, end_idx);
        }
      } else {
        // Adding the first rule of a new definition
        book.defs.insert(name.clone(), Definition::new(name.clone(), vec![rule], builtin));
      }
      indent = self.advance_newlines();
      last_rule = Some(name);
    }

    Ok(book)
  }

  fn parse_datatype(&mut self, builtin: bool) -> ParseResult<(Name, Adt)> {
    // data name = ctr (| ctr)*
    self.skip_trivia();
    let name = self.labelled(|p| p.parse_top_level_name(), "datatype name")?;
    self.consume("=")?;
    let mut ctrs = vec![self.parse_datatype_ctr(&name)?];
    while self.try_consume("|") {
      ctrs.push(self.parse_datatype_ctr(&name)?);
    }
    let ctrs = ctrs.into_iter().collect();
    let adt = Adt { ctrs, builtin };
    Ok((name, adt))
  }

  fn parse_datatype_ctr(&mut self, typ_name: &Name) -> ParseResult<(Name, Vec<CtrField>)> {
    // (name  ('~'? field)*)
    // name
    if self.try_consume("(") {
      self.skip_trivia();
      let name = self.parse_top_level_name()?;
      let name = Name::new(format!("{typ_name}/{name}"));

      fn parse_field(p: &mut TermParser) -> ParseResult<CtrField> {
        let rec = p.try_consume("~");
        p.skip_trivia();
        let nam = p.labelled(|p| p.parse_bend_name(), "datatype constructor field")?;
        Ok(CtrField { nam, rec })
      }

      let fields = self.list_like(parse_field, "", ")", "", false, 0)?;
      Ok((name, fields))
    } else {
      // name
      let name = self.labelled(|p| p.parse_top_level_name(), "datatype constructor name")?;
      let name = Name::new(format!("{typ_name}/{name}"));
      Ok((name, vec![]))
    }
  }

  fn parse_import(&mut self) -> Result<Name, String> {
    // use package
    let import = self.labelled(|p| p.parse_bend_name_import(), "package name")?;

    if self.try_consume("{") {
      todo!("syntax not implemented yet")
    }

    Ok(import)
  }

  fn parse_rule(&mut self) -> ParseResult<(Name, Rule)> {
    // (name pat*) = term
    // name pat* = term
    let (name, pats) = if self.try_consume_exactly("(") {
      self.skip_trivia();
      let name = self.labelled(|p| p.parse_top_level_name(), "function name")?;
      let pats = self.list_like(|p| p.parse_pattern(false), "", ")", "", false, 0)?;
      self.consume("=")?;
      (name, pats)
    } else {
      let name = self.labelled(|p| p.parse_top_level_name(), "top-level definition")?;
      let mut pats = vec![];
      while !self.try_consume("=") {
        pats.push(self.parse_pattern(false)?);
        self.skip_trivia();
      }
      (name, pats)
    };

    let body = self.parse_term()?;

    let rule = Rule { pats, body };
    Ok((name, rule))
  }

  fn parse_pattern(&mut self, simple: bool) -> ParseResult<Pattern> {
    maybe_grow(|| {
      let (tag, unexpected_tag) = self.parse_tag()?;
      self.skip_trivia();

      // Ctr or Tup
      if self.starts_with("(") {
        self.advance_one();
        let head_ini_idx = *self.index();
        let head = self.parse_pattern(simple)?;
        let head_end_idx = *self.index();

        // Tup
        self.skip_trivia();
        if self.starts_with(",") || simple {
          self.consume(",")?;
          let mut els = self.list_like(|p| p.parse_pattern(simple), "", ")", ",", true, 1)?;
          els.insert(0, head);
          return Ok(Pattern::Fan(FanKind::Tup, tag.unwrap_or(Tag::Static), els));
        }

        // Ctr
        unexpected_tag(self)?;
        let Pattern::Var(Some(name)) = head else {
          return self.expected_spanned("constructor name", head_ini_idx, head_end_idx);
        };
        let els = self.list_like(|p| p.parse_pattern(simple), "", ")", "", false, 0)?;
        return Ok(Pattern::Ctr(name, els));
      }

      // Dup
      if self.starts_with("{") {
        let els = self.list_like(|p| p.parse_pattern(simple), "{", "}", ",", false, 0)?;
        return Ok(Pattern::Fan(FanKind::Dup, tag.unwrap_or(Tag::Auto), els));
      }

      // List
      if self.starts_with("[") && !simple {
        unexpected_tag(self)?;
        let els = self.list_like(|p| p.parse_pattern(simple), "[", "]", ",", false, 0)?;
        return Ok(Pattern::Lst(els));
      }

      // String
      if self.starts_with("\"") && !simple {
        unexpected_tag(self)?;
        let str = self.parse_quoted_string()?;
        return Ok(Pattern::Str(STRINGS.get(str)));
      }

      // Char
      if self.starts_with("'") {
        unexpected_tag(self)?;
        let char = self.parse_quoted_char()?;
        return Ok(Pattern::Num(char as u32));
      }

      // Number
      if self.peek_one().map_or(false, |c| c.is_ascii_digit()) {
        unexpected_tag(self)?;
        let num = self.parse_u32()?;
        return Ok(Pattern::Num(num));
      }

      // Channel
      if self.starts_with("$") {
        unexpected_tag(self)?;
        self.advance_one();
        self.skip_trivia();
        let name = self.parse_bend_name()?;
        return Ok(Pattern::Chn(name));
      }

      // Var
      unexpected_tag(self)?;
      let nam = self.labelled(|p| p.parse_name_or_era(), "pattern-matching pattern")?;
      Ok(Pattern::Var(nam))
    })
  }

  pub fn parse_term(&mut self) -> ParseResult<Term> {
    maybe_grow(|| {
      let (tag, unexpected_tag) = self.parse_tag()?;
      self.skip_trivia();

      // Lambda, unscoped lambda
      if self.starts_with("λ") || self.starts_with("@") {
        self.advance_one();
        let tag = tag.unwrap_or(Tag::Static);
        let pat = self.parse_pattern(true)?;
        let bod = self.parse_term()?;
        return Ok(Term::Lam { tag, pat: Box::new(pat), bod: Box::new(bod) });
      }

      // App, Tup, Num Op
      if self.starts_with("(") {
        self.advance_one();

        // Opr but maybe a tup
        self.skip_trivia();
        let starts_with_oper = self.peek_one().map_or(false, |c| "+-*/%&|<>^=!".contains(c));
        if starts_with_oper {
          let opr = self.parse_oper()?;

          // jk, actually a tuple
          self.skip_trivia();
          if self.starts_with(",") && opr == Op::MUL {
            let mut els = vec![Term::Era];
            while self.try_consume(",") {
              els.push(self.parse_term()?);
            }
            self.consume(")")?;
            return Ok(Term::Fan { fan: FanKind::Tup, tag: tag.unwrap_or(Tag::Static), els });
          }

          // Opr
          unexpected_tag(self)?;
          let fst = self.parse_term()?;
          let snd = self.parse_term()?;
          self.consume(")")?;
          return Ok(Term::Oper { opr, fst: Box::new(fst), snd: Box::new(snd) });
        }

        // Tup or App
        let head = self.parse_term()?;

        // Tup
        self.skip_trivia();
        if self.starts_with(",") {
          let mut els = vec![head];
          while self.try_consume(",") {
            els.push(self.parse_term()?);
          }
          self.consume(")")?;
          return Ok(Term::Fan { fan: FanKind::Tup, tag: tag.unwrap_or(Tag::Static), els });
        }

        // App
        let els = self.list_like(|p| p.parse_term(), "", ")", "", false, 0)?;
        let term = els.into_iter().fold(head, |fun, arg| Term::App {
          tag: tag.clone().unwrap_or(Tag::Static),
          fun: Box::new(fun),
          arg: Box::new(arg),
        });
        return Ok(term);
      }

      // List
      if self.starts_with("[") {
        unexpected_tag(self)?;
        let els = self.list_like(|p| p.parse_term(), "[", "]", ",", false, 0)?;
        return Ok(Term::List { els });
      }

      // Sup
      if self.starts_with("{") {
        let els = self.list_like(|p| p.parse_term(), "{", "}", ",", false, 2)?;
        return Ok(Term::Fan { fan: FanKind::Dup, tag: tag.unwrap_or(Tag::Auto), els });
      }

      // Unscoped var
      if self.starts_with("$") {
        self.advance_one();
        unexpected_tag(self)?;
        self.skip_trivia();
        let nam = self.parse_bend_name()?;
        return Ok(Term::Link { nam });
      }

      // Era
      if self.starts_with("*") {
        self.advance_one();
        unexpected_tag(self)?;
        return Ok(Term::Era);
      }

      // Nat
      if self.starts_with("#") {
        self.advance_one();
        unexpected_tag(self)?;
        let val = self.parse_u32()?;
        return Ok(Term::Nat { val });
      }

      // String
      if self.starts_with("\"") {
        unexpected_tag(self)?;
        let str = self.parse_quoted_string()?;
        return Ok(Term::Str { val: STRINGS.get(str) });
      }

      // Char
      if self.starts_with("'") {
        unexpected_tag(self)?;
        let char = self.parse_quoted_char()?;
        return Ok(Term::Num { val: Num::U24(char as u32 & 0x00ff_ffff) });
      }

      // Symbol
      if self.starts_with("`") {
        unexpected_tag(self)?;
        let val = self.parse_quoted_symbol()?;
        return Ok(Term::Num { val: Num::U24(val) });
      }

      // Native Number
      if self.peek_one().map_or(false, is_num_char) {
        unexpected_tag(self)?;
        let num = self.parse_number()?;
        return Ok(Term::Num { val: num });
      }

      // Use
      if self.try_parse_keyword("use") {
        unexpected_tag(self)?;
        self.skip_trivia();
        let nam = self.parse_bend_name()?;
        self.consume("=")?;
        let val = self.parse_term()?;
        self.try_consume(";");
        let nxt = self.parse_term()?;
        return Ok(Term::Use { nam: Some(nam), val: Box::new(val), nxt: Box::new(nxt) });
      }

      // Let
      if self.try_parse_keyword("let") {
        unexpected_tag(self)?;
        let pat = self.parse_pattern(true)?;
        self.consume("=")?;
        let val = self.parse_term()?;
        self.try_consume(";");
        let nxt = self.parse_term()?;
        return Ok(Term::Let { pat: Box::new(pat), val: Box::new(val), nxt: Box::new(nxt) });
      }

      // Ask (monadic operation)
      if self.try_parse_keyword("ask") {
        unexpected_tag(self)?;
        let pat = self.parse_pattern(true)?;
        self.consume("=")?;
        let val = self.parse_term()?;
        self.try_consume(";");
        let nxt = self.parse_term()?;
        return Ok(Term::Ask { pat: Box::new(pat), val: Box::new(val), nxt: Box::new(nxt) });
      }

      // If
      if self.try_parse_keyword("if") {
        let cnd = self.parse_term()?;
        self.consume("{")?;
        let thn = self.parse_term()?;
        self.consume("}")?;
        self.consume("else")?;
        self.consume("{")?;
        let els = self.parse_term()?;
        self.consume("}")?;
        return Ok(Term::Swt {
          arg: Box::new(cnd),
          bnd: Some(Name::new("%cond")),
          with: Vec::new(),
          pred: Some(Name::new("%cond-1")),
          arms: vec![els, thn],
        });
      }

      // Match
      if self.try_parse_keyword("match") {
        unexpected_tag(self)?;
        let (bnd, arg, with) = self.parse_match_header()?;
        let arms = self.list_like(|p| p.parse_match_arm(), "{", "}", ";", false, 1)?;
        return Ok(Term::Mat { arg: Box::new(arg), bnd, with, arms });
      }

      // Switch
      if self.try_parse_keyword("switch") {
        unexpected_tag(self)?;
        let (bnd, arg, with) = self.parse_match_header()?;

        self.consume("{")?;
        self.try_consume("|");
        self.consume("0")?;
        self.consume(":")?;
        let zero = self.parse_term()?;
        self.try_consume(";");

        let mut arms = vec![zero];
        let mut expected_num = 1;
        loop {
          self.try_consume("|");
          // case _
          if self.try_consume("_") {
            self.consume(":")?;
            arms.push(self.parse_term()?);
            self.try_consume(";");
            self.consume("}")?;
            break;
          }
          // case num
          let val = self.parse_u32()?;
          if val != expected_num {
            return self.expected(&format!("'{}'", &expected_num.to_string()));
          }
          expected_num += 1;
          self.consume(":")?;
          arms.push(self.parse_term()?);
          self.try_consume(";");
        }
        let pred = Some(Name::new(format!("{}-{}", bnd.as_ref().unwrap(), arms.len() - 1)));
        return Ok(Term::Swt { arg: Box::new(arg), bnd, with, pred, arms });
      }

      // Do (monadic block)
      if self.try_parse_keyword("do") {
        unexpected_tag(self)?;
        let typ = self.parse_name()?;
        self.consume("{")?;
        let bod = self.parse_term()?;
        self.consume("}")?;
        return Ok(Term::Do { typ: Name::new(typ), bod: Box::new(bod) });
      }

      // Fold
      if self.try_parse_keyword("fold") {
        unexpected_tag(self)?;
        let (bnd, arg, with) = self.parse_match_header()?;
        let arms = self.list_like(|p| p.parse_match_arm(), "{", "}", ";", false, 1)?;
        return Ok(Term::Fold { arg: Box::new(arg), bnd, with, arms });
      }

      // Bend
      if self.try_parse_keyword("bend") {
        unexpected_tag(self)?;
        let args = self.list_like(
          |p| {
            let bind = p.parse_bend_name()?;
            let init = if p.try_consume("=") { p.parse_term()? } else { Term::Var { nam: bind.clone() } };
            Ok((bind, init))
          },
          "",
          "{",
          ",",
          false,
          0,
        )?;
        let (bind, init): (Vec<_>, Vec<_>) = args.into_iter().unzip();
        let bind = bind.into_iter().map(Some).collect::<Vec<_>>();
        self.skip_trivia();
        self.parse_keyword("when")?;
        let cond = self.parse_term()?;
        self.consume(":")?;
        let step = self.parse_term()?;
        self.skip_trivia();
        self.parse_keyword("else")?;
        self.consume(":")?;
        let base = self.parse_term()?;
        self.consume("}")?;
        return Ok(Term::Bend {
          bind,
          init,
          cond: Box::new(cond),
          step: Box::new(step),
          base: Box::new(base),
        });
      }

      // Open
      if self.try_parse_keyword("open") {
        unexpected_tag(self)?;
        self.skip_trivia();
        let typ = self.parse_top_level_name()?;
        self.skip_trivia();
        let var = self.parse_bend_name()?;
        self.try_consume(";");
        let bod = self.parse_term()?;
        return Ok(Term::Open { typ, var, bod: Box::new(bod) });
      }

      // Var
      unexpected_tag(self)?;
      let nam = self.labelled(|p| p.parse_bend_name(), "term")?;
      Ok(Term::Var { nam })
    })
  }

  fn parse_name_or_era(&mut self) -> ParseResult<Option<Name>> {
    self.labelled(
      |p| {
        if p.try_consume_exactly("*") {
          Ok(None)
        } else {
          let nam = p.parse_bend_name()?;
          Ok(Some(nam))
        }
      },
      "name or '*'",
    )
  }

  /// Parses a tag where it may or may not be valid.
  ///
  /// If it is not valid, the returned callback can be used to issue an error.
  fn parse_tag(&mut self) -> ParseResult<(Option<Tag>, impl FnOnce(&mut Self) -> Result<(), String>)> {
    let index = self.index;
    self.skip_trivia();
    let tag = if self.peek_one() == Some('#')
      && !self.peek_many(2).is_some_and(|x| x.chars().nth(1).unwrap().is_ascii_digit())
    {
      let msg = "Tagged terms not supported for hvm32.".to_string();
      return self.with_ctx(Err(msg), index, index + 1);
    } else {
      None
    };
    let end_index = self.index;
    let has_tag = tag.is_some();
    Ok((tag, move |slf: &mut Self| {
      if has_tag {
        let msg = "\x1b[1m- unexpected tag:\x1b[0m".to_string();
        slf.with_ctx(Err(msg), index, end_index)
      } else {
        Ok(())
      }
    }))
  }

  fn parse_match_arg(&mut self) -> ParseResult<(Option<Name>, Term)> {
    let ini_idx = *self.index();
    let mut arg = self.parse_term()?;
    let end_idx = *self.index();

    self.skip_trivia();
    match (&mut arg, self.starts_with("=")) {
      (Term::Var { nam }, true) => {
        self.consume("=")?;
        Ok((Some(std::mem::take(nam)), self.parse_term()?))
      }
      (Term::Var { nam }, false) => Ok((Some(nam.clone()), Term::Var { nam: std::mem::take(nam) })),
      (_, true) => self.expected_spanned("argument name", ini_idx, end_idx),
      (arg, false) => Ok((Some(Name::new("%arg")), std::mem::take(arg))),
    }
  }

  fn parse_match_header(&mut self) -> ParseResult<(Option<Name>, Term, Vec<Name>)> {
    let (bnd, arg) = self.parse_match_arg()?;
    self.skip_trivia();
    let with = if self.try_parse_keyword("with") {
      self.skip_trivia();
      let mut with = vec![self.parse_bend_name()?];
      self.skip_trivia();
      while !self.starts_with("{") {
        self.try_consume(",");
        self.skip_trivia();
        with.push(self.parse_bend_name()?);
        self.skip_trivia();
      }
      with
    } else {
      vec![]
    };
    Ok((bnd, arg, with))
  }

  fn parse_match_arm(&mut self) -> ParseResult<MatchRule> {
    self.try_consume("|");
    self.skip_trivia();
    let nam = self.parse_name_or_era()?;
    self.consume(":")?;
    let bod = self.parse_term()?;
    Ok((nam, vec![], bod))
  }
}

impl<'a> Parser<'a> for TermParser<'a> {
  fn input(&mut self) -> &'a str {
    self.input
  }

  fn index(&mut self) -> &mut usize {
    &mut self.index
  }

  /// Generates an error message for parsing failures, including the highlighted context.
  ///
  /// Override to have our own error message.
  fn expected<T>(&mut self, exp: &str) -> ParseResult<T> {
    let ini_idx = *self.index();
    let end_idx = *self.index() + 1;
    self.expected_spanned(exp, ini_idx, end_idx)
  }

  /// Consumes an instance of the given string, erroring if it is not found.
  ///
  /// Override to have our own error message.
  fn consume(&mut self, text: &str) -> ParseResult<()> {
    self.skip_trivia();
    if self.input().get(*self.index()..).unwrap_or_default().starts_with(text) {
      *self.index() += text.len();
      Ok(())
    } else {
      self.expected(format!("'{text}'").as_str())
    }
  }

  fn skip_trivia(&mut self) {
    while let Some(c) = self.peek_one() {
      if c.is_ascii_whitespace() {
        self.advance_one();
        continue;
      }
      if c == '#' {
        while let Some(c) = self.peek_one() {
          if c != '\n' {
            self.advance_one();
          } else {
            break;
          }
        }
        self.advance_one(); // Skip the newline character as well
        continue;
      }
      break;
    }
  }
}

pub fn is_name_char(c: char) -> bool {
  c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '-' || c == '/'
}

pub fn is_num_char(c: char) -> bool {
  "0123456789+-".contains(c)
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Indent {
  Val(isize),
  Eof,
}

impl Indent {
  pub fn new(val: isize) -> Self {
    Indent::Val(val)
  }

  pub fn enter_level(&mut self) {
    if let Indent::Val(val) = self {
      *val += 2;
    }
  }

  pub fn exit_level(&mut self) {
    if let Indent::Val(val) = self {
      *val -= 2;
    }
  }
}

impl Book {
  fn add_adt(&mut self, nam: Name, adt: Adt) -> ParseResult<()> {
    if let Some(adt) = self.adts.get(&nam) {
      if adt.builtin {
        return Err(format!("{} is a built-in datatype and should not be overridden.", nam));
      } else {
        return Err(format!("Repeated datatype '{}'", nam));
      }
    } else {
      for ctr in adt.ctrs.keys() {
        match self.ctrs.entry(ctr.clone()) {
          indexmap::map::Entry::Vacant(e) => _ = e.insert(nam.clone()),
          indexmap::map::Entry::Occupied(e) => {
            if self.adts.get(e.get()).is_some_and(|adt| adt.builtin) {
              return Err(format!("{} is a built-in constructor and should not be overridden.", e.key()));
            } else {
              return Err(format!("Repeated constructor '{}'", e.key()));
            }
          }
        }
      }
      self.adts.insert(nam.clone(), adt);
    }
    Ok(())
  }
}

impl<'a> ParserCommons<'a> for TermParser<'a> {}

pub trait ParserCommons<'a>: Parser<'a> {
  fn labelled<T>(&mut self, parser: impl Fn(&mut Self) -> ParseResult<T>, label: &str) -> ParseResult<T> {
    match parser(self) {
      Ok(val) => Ok(val),
      Err(_) => self.expected(label),
    }
  }

  fn parse_restricted_name(&mut self, kind: &str) -> ParseResult<Name> {
    let ini_idx = *self.index();
    let name = self.take_while(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '-' || c == '/');
    if name.is_empty() {
      self.expected("name")?
    }
    let name = Name::new(name.to_owned());
    let end_idx = *self.index();
    if name.contains("__") {
      let msg = format!("{kind} names are not allowed to contain \"__\".");
      self.with_ctx(Err(msg), ini_idx, end_idx)
    } else if name.starts_with("//") {
      let msg = format!("{kind} names are not allowed to start with \"//\".");
      self.with_ctx(Err(msg), ini_idx, end_idx)
    } else {
      Ok(name)
    }
  }

  /// Parses a name from the input, supporting alphanumeric characters, underscores, periods, hyphens, and at.
  fn parse_bend_name_import(&mut self) -> Result<Name, String> {
    self.skip_trivia();
    let name = self
      .take_while(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '-' || c == '/' || c == '@');
    if name.is_empty() { self.expected("name") } else { Ok(Name::new(name)) }
  }

  fn parse_top_level_name(&mut self) -> ParseResult<Name> {
    self.parse_restricted_name("Top-level")
  }

  fn parse_bend_name(&mut self) -> ParseResult<Name> {
    self.parse_restricted_name("Variable")
  }

  /// Consumes exactly the text without skipping.
  fn consume_exactly(&mut self, text: &str) -> ParseResult<()> {
    if self.input().get(*self.index()..).unwrap_or_default().starts_with(text) {
      *self.index() += text.len();
      Ok(())
    } else {
      self.expected(format!("'{text}'").as_str())
    }
  }

  fn consume_new_line(&mut self) -> ParseResult<()> {
    self.skip_trivia_inline();
    self.try_consume_exactly("\r");
    self.labelled(|p| p.consume_exactly("\n"), "newline")
  }

  /// Skips trivia, returns the number of trivia characters skipped in the last line.
  fn advance_newlines(&mut self) -> Indent {
    loop {
      let num_spaces = self.advance_trivia_inline();
      if self.peek_one() == Some('\r') {
        self.advance_one();
      }
      if self.peek_one() == Some('\n') {
        self.advance_one();
      } else if self.is_eof() {
        return Indent::Eof;
      } else {
        return Indent::Val(num_spaces);
      }
    }
  }

  /// Advances the parser to the next non-trivia character in the same line.
  /// Returns how many characters were advanced.
  fn advance_trivia_inline(&mut self) -> isize {
    let mut char_count = 0;
    while let Some(c) = self.peek_one() {
      if " \t".contains(c) {
        self.advance_one();
        char_count += 1;
        continue;
      }
      if c == '#' {
        while let Some(c) = self.peek_one() {
          if c != '\n' {
            self.advance_one();
            char_count += 1;
          } else {
            break;
          }
        }
        continue;
      }
      break;
    }
    char_count
  }

  /// Skips until the next non-trivia character in the same line.
  fn skip_trivia_inline(&mut self) {
    self.advance_trivia_inline();
  }

  fn expected_spanned<T>(&mut self, exp: &str, ini_idx: usize, end_idx: usize) -> ParseResult<T> {
    let is_eof = self.is_eof();
    let detected = DisplayFn(|f| if is_eof { write!(f, " end of input") } else { Ok(()) });
    let msg = format!("\x1b[1m- expected:\x1b[0m {}\n\x1b[1m- detected:\x1b[0m{}", exp, detected);
    self.with_ctx(Err(msg), ini_idx, end_idx)
  }

  fn with_ctx<T>(
    &mut self,
    res: Result<T, impl std::fmt::Display>,
    ini_idx: usize,
    end_idx: usize,
  ) -> ParseResult<T> {
    res.map_err(|msg| {
      let ctx = highlight_error(ini_idx, end_idx, self.input());
      format!("{msg}\n{ctx}")
    })
  }

  /// Consumes text if the input starts with it or trivia. Otherwise, do nothing.
  fn try_consume(&mut self, text: &str) -> bool {
    self.skip_trivia();
    if self.starts_with(text) {
      self.consume(text).unwrap();
      true
    } else {
      false
    }
  }

  /// Consumes text if the input starts exactly with it. Otherwise, do nothing.
  fn try_consume_exactly(&mut self, text: &str) -> bool {
    if self.starts_with(text) {
      self.consume_exactly(text).unwrap();
      true
    } else {
      false
    }
  }

  fn try_parse_keyword(&mut self, keyword: &str) -> bool {
    if !self.starts_with(keyword) {
      return false;
    }
    let input = &self.input()[*self.index() + keyword.len()..];
    let next_is_name = input.chars().next().map_or(false, is_name_char);
    if !next_is_name {
      self.consume_exactly(keyword).unwrap();
      true
    } else {
      false
    }
  }

  fn parse_keyword(&mut self, keyword: &str) -> ParseResult<()> {
    let ini_idx = *self.index();
    self.consume_exactly(keyword)?;
    let end_idx = *self.index();
    let input = &self.input()[*self.index()..];
    let next_is_name = input.chars().next().map_or(false, is_name_char);
    if !next_is_name {
      Ok(())
    } else {
      self.expected_spanned(&format!("keyword '{keyword}'"), ini_idx, end_idx + 1)
    }
  }

  /// Parses a list-like structure like "[x1, x2, x3,]".
  /// Since a list is always well terminated, we consume newlines.
  ///
  /// `parser` is a function that parses an element of the list.
  ///
  /// If `hard_sep` the separator between elements is mandatory.
  /// Always accepts trailing separators.
  ///
  /// `min_els` determines how many elements must be parsed at minimum.
  fn list_like<T>(
    &mut self,
    parser: impl Fn(&mut Self) -> ParseResult<T>,
    start: &str,
    end: &str,
    sep: &str,
    hard_sep: bool,
    min_els: usize,
  ) -> ParseResult<Vec<T>> {
    self.consume_exactly(start)?;

    let mut els = vec![];
    // Consume the minimum number of elements
    for i in 0..min_els {
      self.skip_trivia();
      els.push(parser(self)?);
      self.skip_trivia();
      if hard_sep && !(i == min_els - 1 && self.starts_with(end)) {
        self.consume(sep)?;
      } else {
        self.try_consume(sep);
      }
    }

    // Consume optional elements
    while !self.try_consume(end) {
      els.push(parser(self)?);
      self.skip_trivia();
      if hard_sep && !self.starts_with(end) {
        self.consume(sep)?;
      } else {
        self.try_consume(sep);
      }
    }
    Ok(els)
  }

  fn parse_oper(&mut self) -> ParseResult<Op> {
    let opr = if self.try_consume_exactly("+") {
      Op::ADD
    } else if self.try_consume_exactly("-") {
      Op::SUB
    } else if self.try_consume_exactly("**") {
      Op::POW
    } else if self.try_consume_exactly("*") {
      Op::MUL
    } else if self.try_consume_exactly("/") {
      Op::DIV
    } else if self.try_consume_exactly("%") {
      Op::REM
    } else if self.try_consume_exactly("<<") {
      Op::SHL
    } else if self.try_consume_exactly(">>") {
      Op::SHR
    } else if self.try_consume_exactly("<") {
      Op::LT
    } else if self.try_consume_exactly(">") {
      Op::GT
    } else if self.try_consume_exactly("==") {
      Op::EQ
    } else if self.try_consume_exactly("!=") {
      Op::NEQ
    } else if self.try_consume_exactly("&") {
      Op::AND
    } else if self.try_consume_exactly("|") {
      Op::OR
    } else if self.try_consume_exactly("^") {
      Op::XOR
    } else {
      return self.expected("numeric operator");
    };
    Ok(opr)
  }

  fn peek_oper(&mut self) -> Option<Op> {
    let opr = if self.starts_with("+") {
      Op::ADD
    } else if self.starts_with("-") {
      Op::SUB
    } else if self.starts_with("**") {
      Op::POW
    } else if self.starts_with("*") {
      Op::MUL
    } else if self.starts_with("/") {
      Op::DIV
    } else if self.starts_with("%") {
      Op::REM
    } else if self.starts_with("<<") {
      Op::SHL
    } else if self.starts_with(">>") {
      Op::SHR
    } else if self.starts_with("<") {
      Op::LT
    } else if self.starts_with(">") {
      Op::GT
    } else if self.starts_with("==") {
      Op::EQ
    } else if self.starts_with("!=") {
      Op::NEQ
    } else if self.starts_with("&") {
      Op::AND
    } else if self.starts_with("|") {
      Op::OR
    } else if self.starts_with("^") {
      Op::XOR
    } else {
      return None;
    };
    Some(opr)
  }

  fn parse_u32(&mut self) -> ParseResult<u32> {
    let radix = match self.peek_many(2) {
      Some("0x") => {
        self.advance_many(2);
        16
      }
      Some("0b") => {
        self.advance_many(2);
        2
      }
      _ => 10,
    };
    let num_str = self.take_while(move |c| c.is_digit(radix) || c == '_');
    let num_str = num_str.chars().filter(|c| *c != '_').collect::<String>();

    let next_is_hex = self.peek_one().map_or(false, |c| "0123456789abcdefABCDEF".contains(c));
    if next_is_hex || num_str.is_empty() {
      let base = match radix {
        16 => "hexadecimal",
        10 => "decimal",
        2 => "binary",
        _ => unreachable!(),
      };
      self.expected(format!("valid {base} digit").as_str())
    } else {
      u32::from_str_radix(&num_str, radix).map_err(|e| e.to_string())
    }
  }

  fn parse_number(&mut self) -> ParseResult<Num> {
    let ini_idx = *self.index();

    // Parses sign
    let sgn = if self.try_consume_exactly("+") {
      Some(1)
    } else if self.try_consume_exactly("-") {
      Some(-1)
    } else {
      None
    };

    // Parses main value
    let num = self.parse_u32()?;

    // Parses frac value (Float type)
    // TODO: Will lead to some rounding errors
    // TODO: Doesn't cover very large/small numbers
    let fra = if let Some('.') = self.peek_one() {
      self.advance_one();
      let ini_idx = *self.index();
      let fra = self.parse_u32()? as f32;
      let end_idx = *self.index();
      let fra = fra / 10f32.powi((end_idx - ini_idx) as i32);
      Some(fra)
    } else {
      None
    };

    // F24
    if let Some(fra) = fra {
      let sgn = sgn.unwrap_or(1);
      return Ok(Num::F24(sgn as f32 * (num as f32 + fra)));
    }

    // I24
    if let Some(sgn) = sgn {
      let num = sgn * num as i32;
      if !(-0x00800000..=0x007fffff).contains(&num) {
        return self.num_range_err(ini_idx, "I24");
      }
      return Ok(Num::I24(num));
    }

    // U24
    if num >= 1 << 24 {
      return self.num_range_err(ini_idx, "U24");
    }
    Ok(Num::U24(num))
  }

  fn num_range_err<T>(&mut self, ini_idx: usize, typ: &str) -> ParseResult<T> {
    let msg = format!("\x1b[1mNumber literal outside of range for {}.\x1b[0m", typ);
    let end_idx = *self.index();
    self.with_ctx(Err(msg), ini_idx, end_idx)
  }

  /// Parses up to 4 base64 characters surrounded by "`".
  /// Joins the characters into a u24 and returns it.
  fn parse_quoted_symbol(&mut self) -> ParseResult<u32> {
    self.consume_exactly("`")?;
    let mut result = 0;
    let mut count = 0;
    while count < 4 {
      if self.starts_with("`") {
        break;
      }
      count += 1;
      let Some(c) = self.advance_one() else { self.expected("base_64 character")? };
      let c = c as u8;
      let nxt = match c {
        b'A'..=b'Z' => c - b'A',
        b'a'..=b'z' => c - b'a' + 26,
        b'0'..=b'9' => c - b'0' + 52,
        b'+' => 62,
        b'/' => 63,
        _ => return self.expected("base64 character"),
      };
      result = (result << 6) | nxt as u32;
    }
    self.consume_exactly("`")?;
    Ok(result)
  }
}
