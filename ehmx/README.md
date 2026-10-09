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
Solver mode also displays a `scheme` line. For `\x -> eq x x`, it has the form
`∀α. Eq α => ((α -{}-> Bool) !{})`: the arrow effect is latent in the
function type, and `!{}` is the effect of evaluating the lambda expression.
The REPL generalizes only names absent from the environment and `:assume`.
The scheme is the generalization of the solver's residual result; the
partial solver does not certify that every such scheme is a principal normal
form.
An explicitly declared `:assume` can discharge another exact predicate. A
class predicate on a still-unknown type stays in the residual constraints.
The solver also unifies free type equalities and simplifies forced-empty effect
variables. It eliminates local existential witnesses from quantified handler
constraints when a type equality or both directions of an effect inclusion
determine the witness. Other quantified constraints remain symbolic. For
`handle (perform ping 1) with { return r -> r; ping(x;k) -> k x }`, the
constraint simplifies to `true`, while the scheme is `∀μ. (Int !{μ})`.
The handler rule permits additional output effects, so `μ` is not forced to
the empty set.

The same simplification works when the handler is inside a value `let`:
`let a = \x -> handle (perform ping x) with { return r -> r; ping(x;k) -> k x } in a 1`
has `constraints: true` and a scheme of the form `∀μ. (Int !{μ})`.
Mutual effect inclusions are identified only when at least one effect name is
local to inference; effect names free in the environment remain fixed.

In a handler clause, the type variables freshly introduced for calls such as `id x` are projected inside the operation's universal quantifier. A constraint of the form `∀α. ∃β. ...` can remain when the witness is not determined by an equality. The solver is not a complete decision procedure for these constraints.

Use ↑/↓ to navigate commands entered in the current session. Ctrl-C clears the current input; Ctrl-D exits.

## Constraint-system API

`system::ConstraintSystem` is the inference parameter. Its associated
`Formula` is a complete constraint, with operations for conjunction, type
equality, effect inclusion, exclusion, and existential projection. The
`handler_clause` method represents the rigid-operation-parameter check with
local existential witnesses. `system::generate` uses only this interface and
returns a `QualifiedOutput<X::Formula>`.
Scheme instantiation uses existential projection and type/effect equalities.
It leaves the formula stored by `X` intact, so implementations do not expose
its internal bound names or a formula-renaming operation.
This follows the constraint-system parameter of
[HM(X)](https://publikationen.bibliothek.kit.edu/26696/1987); the handler
operation and effect names are the EHM(X) extensions.

`ClassSystem` is the REPL's `Eq`/`Show` instance; `EmptySystem` has the same
type and effect constraints with no class predicates. The concrete
`PredicateSystem` implementation retains the existing printed constraint
syntax. The REPL now uses the generic generator through this instance.
The Rust trait specifies an API, while the semantic laws of a valid instance
are stated in `lean/SystemFXi/EHMX/ConstraintSystem.lean`. The current solver
is specific to `ClassSystem` and remains partial.
Lean proves generic generation soundness and completeness for the core
fragment. It proves the semantic steps for polymorphic value `let`, fresh
variable instantiation, and quantified handler clauses over abstract X.
`GenericCompleteness.lean` connects executable generation to these steps for
variables, lambdas, applications, both forms of `let`, and `perform`, using a
supply-indexed relation that preserves previously allocated names. It also
proves executable variable inference is principal over arbitrary X.
`GenericLogicalInstantiation.lean` proves that projection with diagonal
equalities has exactly the qualified-scheme instances and bounds its free
names without inspecting binders inside X formulas. The executable Rust
generator uses the same construction. Solver mode repeats simplification
after projection exposes new equalities.
It also proves that full monotype principality, once established,
lifts through HM(X) normalization to a principal computation scheme for any
valid `ConstraintSystem`. `GenericHandlerFree.lean` completes the executable
induction for every expression without a handler, including polymorphic
`let`, and proves principality against all declarative typings of the same
expression. With a principal HM(X) normalizer it also proves existence of a
solved principal computation scheme for this fragment. The handler branch
of completeness over arbitrary X remains open. The existing full theorem
applies to the predicate-backed syntax instance.
`LawfulGeneratedFV` states the basic free-name laws implied by HM(X)'s
projection-based free-variable definition, and the syntax instance satisfies
them. The generic generator's next supply is proved monotone.
`GenericSupport.lean` proves that every successful run, including handlers,
keeps all result free names below its final supply.
`GenericEffectFresh.lean` proves that immediate effect names are allocated
after the starting supply and that fresh operation binders satisfy the
handler's outer scope check. The complete handler induction still needs the
clause scope and quantified witness construction.
`GenericOrigin.lean` proves that generalization leaves only environment free
names, variable instantiation preserves the source of old names, and the
handler constructor preserves that property when its three subresults do. It
also shows that old names in a return result precede the operation binders
once the return result's origin premise is established.
`GenericHandlerBridge.lean` turns alignment of every rigid operation assignment
with a declarative clause into the existential witnesses required by the
generic handler constraint.
`GenericEmbedding.lean` verifies the renaming, free-name, and semantic laws
needed to embed abstract X formulas into that existing proof, but the typing
and generator transfer is not yet proved.
