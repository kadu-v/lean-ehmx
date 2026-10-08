# EHM(X) inference REPL

Run from the repository root:

```sh
cargo run --manifest-path ehmx/Cargo.toml
```

```text
ehmx> :op ping : forall a. a -> a
ehmx> :bind y : Int
ehmx> perform ping y
ehmx> handle (perform ping y) with { return r -> r; ping(x;k) -> k x }
ehmx> :bind f : forall a. Eq a => a -{}-> a
ehmx> f 1
```

`:help` lists the commands. A bare expression infers its type, effect, and remaining constraints. The REPL does not execute expressions or unify type variables. Effect variables in declarations begin with `?`, for example `forall a ?e. a -{?e}-> a`.

Use ↑/↓ to navigate commands entered in the current session. Ctrl-C clears the current input; Ctrl-D exits.
