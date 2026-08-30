# Problem I: asymptotic quasitracial cuts without a universal radical

## New per-quasitrace theorem

Let an ideal `I triangleleft A` have an increasing positive-contractive
approximate unit `(e_n)`, and assume quasitraces are traces on the quotient
`A/I`.

For one bounded `2`-quasitrace `tau` on `A`, it is enough that

- the particular restrictions `tau|Her_A(e_n)` are traces; and
- the two square-seminorm limits

```text
tau((e_n-e_n^2)^2) -> 0,
tau([e_n,a]*[e_n,a]) -> 0             for every a in A.
```

vanish.  Then `tau` is a trace.  The result has no intersection over all
bounded quasitraces, no universal quantifier on the hereditary-head
linearity, and no exact square-null membership at any finite stage.

## Exact identity in the sequence quotient

Take the coordinate ultralimit quasitrace on `ell_infinity(A)` and factor by
its square-null ideal.  The class `q=[(e_n)]` becomes a projection commuting
with the constant copy of `A`.  Therefore the head and tail cuts are exact
homomorphisms in this quotient.

The tail quasitrace vanishes on `I` because `(1-e_n)i->0` in norm, so it
factors through `A/I` and is a trace.  The head functional is

```text
rho(a)=lim_omega tau(e_n a e_n).
```

Each summand is linear because `tau` is a trace on `Her_A(e_n)`.  For every
self-adjoint `a`, orthogonal additivity at the central projection gives

```text
tau(a)=rho(a)+sigma(a).
```

This is the exact defect identity: the additivity defect of `tau` is the sum
of the head and tail defects, both zero.

## Strictness over the universal-radical hypothesis

Take

```text
A=C([0,1]),
I={f in A:f(0)=0},
e_n(t)=min(1,nt).
```

The universal bounded-quasitrace radical of `A` is zero because point
evaluations are traces and separate points.  For every `n`, the nonzero
function `e_n-e_n^2` therefore does **not** lie in that radical, so the prior
quasitracial-idempotence theorem does not apply to this approximate unit.

Nevertheless, for every bounded trace `tau` on `A`, dominated convergence
gives

```text
tau((e_n-e_n^2)^2)->0,
```

and all commutators vanish.  The hereditary heads and quotient are
commutative.  Thus the new theorem applies.  This example is deliberately
elementary: it proves strict weakening of the hypotheses, not a new
noncommutative positive class by itself.

## Necessary counterexample certificate

Under the local head and quotient hypotheses, a nontracial quasitrace cannot
see the cuts become both idempotent and central in its square seminorm.
Hence it must retain a positive asymptotic idempotence defect, or one fixed
ambient element must retain a positive commutator defect.  This isolates the
only possible escape from the sequence-quotient splitting argument.
