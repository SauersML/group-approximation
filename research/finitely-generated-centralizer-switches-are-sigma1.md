---
rg: 2
id: finitely-generated-centralizer-switches-are-sigma1
kind: claim
title: Finite equation and finitely generated centralizer switches cannot encode totality
distinct_from:
  amenability-of-finite-presentations-is-pi2-complete: that asks for a Pi-zero-two hard amenability family; this rules out the most direct finite-equation and finitely generated centralizing-HNN switches.
  amenability-fp-position-proof: that obtains first-level hardness by Adian--Rabin; this explains why replacing its single word by any finite packet remains at the first level.
---

**ESTABLISHED.**  For a computable family of finite presentations
`A_e`, any computably supplied finite packet of equations is simultaneously
true on a `Sigma^0_1` set of indices: a certificate is the finite packet
of van Kampen derivations.

Likewise, if `K_e=<h_(e,1),...,h_(e,r_e)> <= A_e` is a computably
supplied finitely generated subgroup, then

```text
{e:K_e=A_e}
```

is `Sigma^0_1`.  A finite certificate gives, for each presentation
generator of `A_e`, a word in the `h_(e,j)` and a derivation of the
equality.

If every `A_e` is amenable, the centralizing HNN extension

```text
C_e=<A_e,t | [t,h_(e,j)]=1, 1<=j<=r_e>
```

is amenable exactly when `K_e=A_e`.  Equality gives `A_e x Z`; if
`K_e<A_e` and `a in A_e\K_e`, Britton's lemma gives

```text
<t,a t a^-1> ~= F_2.
```

Therefore the amenable index set of every such switch is c.e.  Since
`TOT` is `Pi^0_2`-complete and not c.e., neither finite equation
packets nor finitely generated centralizer switches can prove
[[amenability-of-finite-presentations-is-pi2-complete]].  In particular,
using finitely many word equalities in a finitely presented solvable group
with undecidable word problem does not raise the quantifier level.  A
successful compiler must propagate a genuinely infinite table from finitely
many relators.

DERIVATION
[[finitely-generated-centralizer-switches-sigma1-proof]]
