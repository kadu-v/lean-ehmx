#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NamedTy {
    Var(String),
    Int,
    Bool,
    Arr(Box<Self>, Vec<String>, Box<Self>),
}
#[derive(Clone, Debug)]
pub struct SchemeAst {
    pub bound: Vec<String>,
    pub preds: Vec<(String, NamedTy)>,
    pub ty: NamedTy,
}
#[derive(Clone, Debug)]
pub struct OpAst {
    pub bound: Vec<String>,
    pub input: NamedTy,
    pub output: NamedTy,
}
#[derive(Clone, Debug)]
pub enum NamedExpr {
    Var(String),
    Int(String),
    Bool(bool),
    Lam(String, Box<Self>),
    App(Box<Self>, Box<Self>),
    Let(String, Box<Self>, Box<Self>),
    Perform(String, Box<Self>),
    Handle(
        Box<Self>,
        String,
        String,
        Box<Self>,
        String,
        String,
        Box<Self>,
    ),
}

pub fn lex(src: &str) -> Result<Vec<String>, String> {
    let chars: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if i + 1 < chars.len() {
            let two: String = chars[i..i + 2].iter().collect();
            if two == "->" || two == "=>" {
                out.push(two);
                i += 2;
                continue;
            }
        }
        if c == '-' && i + 1 < chars.len() && chars[i + 1].is_ascii_digit() || c.is_ascii_digit() {
            let start = i;
            if c == '-' {
                i += 1;
            }
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            out.push(chars[start..i].iter().collect());
            continue;
        }
        if c.is_ascii_alphabetic() || c == '_' || c == '?' {
            let start = i;
            i += 1;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            if c == '?' && i == start + 1 {
                return Err(format!(
                    "effect variable needs a name at column {}",
                    start + 1
                ));
            }
            out.push(chars[start..i].iter().collect());
            continue;
        }
        if "\\(){}.,;=:-".contains(c) {
            out.push(c.to_string());
            i += 1;
            continue;
        }
        return Err(format!("unexpected character '{c}' at column {}", i + 1));
    }
    Ok(out)
}

pub struct Parser {
    tokens: Vec<String>,
    pos: usize,
}
impl Parser {
    pub fn new(src: &str) -> Result<Self, String> {
        Ok(Self {
            tokens: lex(src)?,
            pos: 0,
        })
    }
    fn peek(&self) -> Option<&str> {
        self.tokens.get(self.pos).map(String::as_str)
    }
    fn take(&mut self) -> Result<String, String> {
        let t = self
            .peek()
            .ok_or_else(|| "unexpected end of input".to_string())?
            .to_owned();
        self.pos += 1;
        Ok(t)
    }
    fn eat(&mut self, tok: &str) -> bool {
        if self.peek() == Some(tok) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, tok: &str) -> Result<(), String> {
        if self.eat(tok) {
            Ok(())
        } else {
            Err(format!("expected '{tok}', found {:?}", self.peek()))
        }
    }
    pub fn finish(&self) -> Result<(), String> {
        if self.pos == self.tokens.len() {
            Ok(())
        } else {
            Err(format!("unexpected token '{}'", self.tokens[self.pos]))
        }
    }
    fn name(&mut self) -> Result<String, String> {
        let x = self.take()?;
        if !is_name(&x)
            || matches!(
                x.as_str(),
                "let"
                    | "in"
                    | "with"
                    | "return"
                    | "handle"
                    | "perform"
                    | "true"
                    | "false"
                    | "forall"
            )
        {
            Err(format!("expected a name, found '{x}'"))
        } else {
            Ok(x)
        }
    }
    pub fn parse_expr(&mut self) -> Result<NamedExpr, String> {
        if self.eat("\\") {
            let x = self.name()?;
            self.expect("->")?;
            return Ok(NamedExpr::Lam(x, Box::new(self.parse_expr()?)));
        }
        if self.eat("let") {
            let x = self.name()?;
            self.expect("=")?;
            let e1 = self.parse_expr()?;
            self.expect("in")?;
            let e2 = self.parse_expr()?;
            return Ok(NamedExpr::Let(x, Box::new(e1), Box::new(e2)));
        }
        if self.eat("handle") {
            let body = self.parse_expr()?;
            self.expect("with")?;
            self.expect("{")?;
            self.expect("return")?;
            let r = self.name()?;
            self.expect("->")?;
            let ret = self.parse_expr()?;
            self.expect(";")?;
            let op = self.name()?;
            self.expect("(")?;
            let x = self.name()?;
            self.expect(";")?;
            let k = self.name()?;
            if x == k {
                return Err("operation argument and continuation need different names".into());
            }
            self.expect(")")?;
            self.expect("->")?;
            let clause = self.parse_expr()?;
            self.expect("}")?;
            return Ok(NamedExpr::Handle(
                Box::new(body),
                op,
                r,
                Box::new(ret),
                x,
                k,
                Box::new(clause),
            ));
        }
        self.parse_app()
    }
    fn atom_start(&self) -> bool {
        match self.peek() {
            Some("(" | "perform" | "true" | "false") => true,
            Some(x)
                if is_name(x)
                    && !matches!(x, "in" | "with" | "return" | "let" | "handle" | "forall") =>
            {
                true
            }
            Some(x) if is_integer(x) => true,
            _ => false,
        }
    }
    fn parse_app(&mut self) -> Result<NamedExpr, String> {
        let mut e = self.parse_atom()?;
        while self.atom_start() {
            e = NamedExpr::App(Box::new(e), Box::new(self.parse_atom()?));
        }
        Ok(e)
    }
    fn parse_atom(&mut self) -> Result<NamedExpr, String> {
        if self.eat("(") {
            let e = self.parse_expr()?;
            self.expect(")")?;
            return Ok(e);
        }
        if self.eat("perform") {
            let op = self.name()?;
            let arg = self.parse_atom()?;
            return Ok(NamedExpr::Perform(op, Box::new(arg)));
        }
        let x = self.take()?;
        match x.as_str() {
            "true" => Ok(NamedExpr::Bool(true)),
            "false" => Ok(NamedExpr::Bool(false)),
            _ if is_integer(&x) => Ok(NamedExpr::Int(normalize_int(&x))),
            _ if is_name(&x) => Ok(NamedExpr::Var(x)),
            _ => Err(format!("expected expression, found '{x}'")),
        }
    }
    fn parse_bound(&mut self) -> Result<Vec<String>, String> {
        let mut out = Vec::new();
        if self.eat("forall") {
            while !self.eat(".") {
                out.push(self.name()?);
                self.eat(",");
            }
            if out.is_empty() {
                return Err("forall requires a variable".into());
            }
        }
        Ok(out)
    }
    pub fn parse_scheme(&mut self) -> Result<SchemeAst, String> {
        let bound = self.parse_bound()?;
        let mut preds = Vec::new();
        if matches!(self.peek(), Some("Eq" | "Show")) {
            loop {
                let class = self.take()?;
                if class != "Eq" && class != "Show" {
                    return Err("expected Eq or Show".into());
                }
                preds.push((class, self.parse_type_primary()?));
                if !self.eat(",") {
                    break;
                }
            }
            self.expect("=>")?;
        }
        Ok(SchemeAst {
            bound,
            preds,
            ty: self.parse_type()?,
        })
    }
    pub fn parse_predicate(&mut self) -> Result<(String, NamedTy), String> {
        let c = self.take()?;
        if c != "Eq" && c != "Show" {
            return Err("expected Eq or Show".into());
        }
        Ok((c, self.parse_type_primary()?))
    }
    pub fn parse_op(&mut self) -> Result<OpAst, String> {
        let bound = self.parse_bound()?;
        let input = self.parse_type()?;
        self.expect("->")?;
        let output = self.parse_type()?;
        Ok(OpAst {
            bound,
            input,
            output,
        })
    }
    pub fn parse_type(&mut self) -> Result<NamedTy, String> {
        let a = self.parse_type_primary()?;
        if self.eat("-") {
            self.expect("{")?;
            let mut items = Vec::new();
            if !self.eat("}") {
                loop {
                    items.push(self.name()?);
                    if self.eat("}") {
                        break;
                    }
                    self.expect(",")?;
                }
            }
            self.expect("->")?;
            let b = self.parse_type()?;
            Ok(NamedTy::Arr(Box::new(a), items, Box::new(b)))
        } else {
            Ok(a)
        }
    }
    fn parse_type_primary(&mut self) -> Result<NamedTy, String> {
        if self.eat("(") {
            let t = self.parse_type()?;
            self.expect(")")?;
            return Ok(t);
        }
        let x = self.name()?;
        match x.as_str() {
            "Int" => Ok(NamedTy::Int),
            "Bool" => Ok(NamedTy::Bool),
            _ => Ok(NamedTy::Var(x)),
        }
    }
}
fn is_name(s: &str) -> bool {
    let mut c = s.chars();
    matches!(c.next(),Some(x) if x.is_ascii_alphabetic() || x=='_' || x=='?')
        && c.all(|x| x.is_ascii_alphanumeric() || x == '_')
}
fn is_integer(s: &str) -> bool {
    let digits = s.strip_prefix('-').unwrap_or(s);
    !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
}
fn normalize_int(s: &str) -> String {
    let neg = s.starts_with('-');
    let digits = s.trim_start_matches('-').trim_start_matches('0');
    if digits.is_empty() {
        "0".into()
    } else if neg {
        format!("-{digits}")
    } else {
        digits.into()
    }
}
