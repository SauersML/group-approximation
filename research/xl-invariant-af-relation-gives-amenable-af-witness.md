---
rg: 2
id: xl-invariant-af-relation-gives-amenable-af-witness
kind: claim
title: A G-invariant minimal AF relation on an amenable Cantor G-space gives an amenable action on a simple AF algebra, and forbids boundary factors
distinct_from:
  xl-commuting-minimal-action-gives-classifiable-witness: that needs a commuting group action; here G only has to preserve each finite relation R_n as a set (it may permute inside classes), no Følner averaging is needed, and the witness algebra is AF.
  xl-commuting-minimal-action-forbids-proximal-factors: that uses commuting maps and proximality; here classes are permuted, and the obstruction is proved for strongly proximal factors via G-maps into P(B).
---

Let `X` be a Cantor space with a topologically amenable action of a countable
group `G`.  Let `R_1 subset R_2 subset ...` be compact open (proper étale)
equivalence relations on `X` with `R = union R_n` minimal (every class dense),
and suppose `(g x g)(R_n) = R_n` for all `g in G` and all `n`.

**(A) Witness.**  `A = C*(R) = lim C*(R_n)` is a unital simple infinite
dimensional AF algebra (so classifiable and stably finite), `G` acts on it by
`alpha_g = ` the automorphism induced by the groupoid automorphism `g x g`,
and `alpha` is amenable.  `T(A)` is the simplex of `R`-invariant measures.
Hence XL holds for `G` if such `(X, R)` exists.  The commuting case
(`R_n = ` orbits of finite subgroups `Gamma_n` of a locally finite group) is a
special case.

**(B) Obstruction.**  If `B` is a strongly proximal `G`-flow and
`phi : X -> P(B)` is a continuous `G`-map, then `phi` is constant, with value
a `G`-invariant measure.  For a nontrivial boundary `B` no invariant measure
exists, so there is **no continuous `G`-map `X -> P(B)`** at all; in
particular `X` factors onto no nontrivial boundary: Gromov boundaries, tree ends, `G/P` and
everything built over them are excluded, even when `G` is allowed to permute
the classes of `R_n` (the multi-valued map `x -> p([x]_n)` is forced to be
single valued on the `R`-saturation of a `G`-minimal set, which is dense).

**What remains.**  The route (A) needs an amenable Cantor `G`-space with **no
nontrivial boundary factor** that carries a `G`-invariant minimal AF relation.
If every compact amenable `G`-space of a nonamenable group had a nontrivial
boundary factor, both commuting-action and invariant-AF-relation routes would
be dead for every `G`; this dichotomy question is open.

Two reformulations (immediate from the definitions).  A continuous `G`-map
`X -> P(B)` is the same as a `G`-equivariant ucp map `C(B) -> C(X)`, so (B)
says there is no `G`-ucp map `C(partial_F G) -> C(X)`; in particular `C(X)`
is never `G`-injective (Kalantar--Kennedy: `C(partial_F G)` is the
`G`-injective envelope of `C`).  And the data `(X, R_n)` is a tower of
finite-to-one `G`-factors `X -> X/R_1 -> X/R_2 -> ...` with trivial tail
(`intersection of C(X/R_n) = C`); each `X/R_n` is amenable by the same class
averaging as in A.2.
