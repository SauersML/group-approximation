# STW XXII: C-space selection boundary after the all-degree theorem

## Established input

For strict support slack `tau(supp(a))<=s<tau(e)`, the weighted
purification fibres

```text
F(a)={w in eR:w^*w=a}
```

are nonempty and closed in a common complete `L^2` operator ball.  The
multifunction is lower semicontinuous.  The all-degree filling theorem makes
the value family uniformly equi-`LC^k` and each value `k`-connected for
every finite `k`.

## Why the standard C-space theorem does not apply

Uspenskij's C-space theorem uses a lower locally constant multifunction
(or, in its open-graph formulation, an aspherical multifunction with open
graph).  Lower local constancy means that every compact subset of one value
persists throughout some base neighbourhood.

For an exact purification pullback `Phi(x)=F(a(x))`, choose any
`w in Phi(x_0)`.  Then

```text
w in Phi(x)  iff  a(x)=w^*w=a(x_0).
```

Thus the compact singleton `{w}` persists near `x_0` only when the weight
field is locally constant there.  Exact purification therefore has the
wrong graph regularity for Uspenskij's theorem on every genuinely varying
stratum.  The graph is naturally closed, not open.

## Exact literature boundary

Gutev's *Selections and Higher Separation Axioms*, Section 6.2, Theorem
6.5 records the lower-locally-constant C-space theorem.  Questions 21 and
22 then explicitly ask whether lower semicontinuity plus uniformly
equi-`LC^omega`, `C^omega` values is enough, first for strongly
countable-dimensional spaces and then for paracompact C-spaces.  The
purification family has precisely this known geometric package, but not
the stronger graph hypothesis.

Therefore the all-degree theorem rigorously yields the finite-covering-
dimensional result, but does not by itself turn the conditional C-space
screening theorem into an unconditional result.  The exact missing input
is `(LWCL)` or a new selection/exactification theorem special to weighted
purification.  This is a theorem-applicability obstruction, not a
counterexample and not evidence for a singular trace.

## Sources

- V. Gutev, [*Selections and Higher Separation Axioms*](https://arxiv.org/abs/1805.07638), Section 6.2, Theorem 6.5 and Questions 21--22.
- V. Uspenskij, *A selection theorem for C-spaces*, Topology and its Applications 85 (1998), 351--374, Theorem 1.3.
