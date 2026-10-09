# EHM(X) inference REPL

Run from the repository root:

```sh
cargo run --manifest-path ehmx/Cargo.toml
```

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

`:help` lists the commands. A bare expression infers its type, effect, and remaining constraints. The REPL does not execute expressions or unify type variables. Effect variables in declarations begin with `?`, for example `forall a ?e. a -{?e}-> a`.

`ping : forall a. a -> a` is available at startup and after `:reset`.
The `Eq` predicate and `eq : forall a. Eq a => a -{}-> a -{}-> Bool` are also available at startup and after `:reset`. `eq` generates an `Eq` constraint; the REPL does not execute comparisons or resolve class instances.

In a handler clause, the type variables freshly introduced for calls such as `id x` are projected inside the operation's universal quantifier. The remaining constraint therefore contains `∀α. ∃α. ...`. The REPL retains these symbolic constraints; its simplifier is not a complete decision procedure for them.

Use ↑/↓ to navigate commands entered in the current session. Ctrl-C clears the current input; Ctrl-D exits.
