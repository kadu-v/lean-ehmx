# EHM(X) inference REPL

Run from the repository root:

```sh
cargo run --manifest-path ehmx/Cargo.toml
```

To solve the built-in `Eq` and `Show` constraints while inferring, run:

```sh
cargo run --manifest-path ehmx/Cargo.toml -- --with-solver
```

From `ehmx/`, the shorter command is `cargo r -- --with-solver`. Cargo needs the
`--` separator to pass `--with-solver` to the REPL; `cargo r --with-solver` is
rejected by Cargo before this program starts. The ordinary mode remains
symbolic.

```text
ehmx> :bind y : Int
ehmx> perform ping y
ehmx> handle (perform ping y) with { return r -> r; ping(x;k) -> k x }
ehmx> :bind f : forall a. Eq a => a -{}-> a
ehmx> f 1
ehmx> eq 1 2
ehmx> :bind id : forall a. a -{}-> a
ehmx> \y -> handle (perform ping y) with { return r -> r; ping(x;k) -> k (id x) }
```

`:help` lists the commands. A bare expression infers its type, effect, and remaining constraints. The REPL does not execute expressions. Ordinary mode leaves type equalities symbolic; solver mode unifies free type equalities. Effect variables in declarations begin with `?`, for example `forall a ?e. a -{?e}-> a`.

`ping : forall a. a -> a` is available at startup and after `:reset`.
The `Eq` predicate and `eq : forall a. Eq a => a -{}-> a -{}-> Bool` are also available at startup and after `:reset`. `eq` generates an `Eq` constraint; the REPL does not execute comparisons. In ordinary mode it does not resolve class instances.

In solver mode, the built-in instances are `Eq Int`, `Eq Bool`, `Show Int`, and
`Show Bool`. For example, `eq 1 2` yields `Bool` with no remaining constraints.
You can try `Show` with `:bind f : forall a. Show a => a -{}-> a`, then `f true`.
An explicitly declared `:assume` can discharge another exact predicate. A
class predicate on a still-unknown type stays in the residual constraints.
The solver also unifies free type equalities and simplifies forced-empty effect
variables. Handler constraints beneath `forall`/`exists` stay symbolic when
they need quantified solving; a remaining effect variable is not silently set
to the empty set.

In a handler clause, the type variables freshly introduced for calls such as `id x` are projected inside the operation's universal quantifier. The remaining constraint therefore contains `∀α. ∃α. ...`. The REPL retains these symbolic constraints; its simplifier is not a complete decision procedure for them.

Use ↑/↓ to navigate commands entered in the current session. Ctrl-C clears the current input; Ctrl-D exits.
