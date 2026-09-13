---
rg: 2
id: relator-width-over-transitive-abelian-extensions
kind: claim
title: An abelian normal subgroup acted on transitively adds at most a fixed amount to relator width, so affine special linear targets give nothing beyond linear soficity
distinct_from:
  simple-group-psl-width-is-finite-field-linear-soficity: that bounds width over SL_n(q) and PSL_n(q); this passes the bound to extensions by an abelian normal subgroup on which the group is transitive, such as F_q^n x| SL_n(q).
  relator-width-over-nilpotent-by-locally-finite-groups: that absorbs a nilpotent normal subgroup under a top of bounded type; this absorbs one transitive abelian layer under a top of any size.
  simple-nonsofic-width-over-bounded-composition-factor-groups: that is the open case of abelian layers under unbounded tops with scarce conjugators; this is the opposite extreme, where every nontrivial element of the layer is conjugate to every other.
---

**ESTABLISHED (unreviewed, 2026-09-13, lane `ex2-weak-sofic-affine-targets`).**

Let `G = <X | R>` be an infinite finitely presented simple group. `w_Q(a)` and `Cons_K^Q` are as in
`simple-group-relator-width-in-finite-simple-targets`. Fix once for all, as in Section 1 of
`simple-group-psl-width-is-finite-field-linear-soficity-proof`, a template
`x = prod_(j <= J) [u_(x,j), v_(x,j)] · n_x` in `F(X)`, with `n_x` a product of `J'` conjugates of
`R^(+-1)` and every `u_(x,j)`, `v_(x,j)` of length `<= L`.

**Theorem A.** Let `Q` be a finite group and `A` an abelian normal subgroup of `Q` on which `Q` acts
transitively by conjugation on `A \ {1}`. Let `a in Q^X` and `abar` its image in `(Q/A)^X`, and put
`K = w_(Q/A)(abar)`. Then
```text
w_(Q/A)(abar) <= w_Q(a) <= max( K + 2 ,  2 J L K + J' ) .
```

**Corollaries.**
1. **Affine special linear groups.** Over `Q = F_q^n x| SL_n(q)`, `n >= 2`, all `q`, the width of `G` is
   bounded iff `G` is not linear sofic over finite fields (definition on
   `simple-group-psl-width-is-finite-field-linear-soficity`). Under that hypothesis `G` has no weak
   models into the groups `ASL_n(q)` with any bi-invariant lengths.
2. **Affine symplectic groups.** Over `F_q^(2m) x| Sp_(2m)(q)` the width is bounded if `G` is not linear
   sofic over finite fields, by `simple-group-classical-width-finite-field-linear-soficity`.
3. **Non-split extensions.** Theorem A needs no splitting. Any finite `Q` with a normal subgroup
   `A ≅ F_q^n` on which `Q/C_Q(A)` contains `SL_n(q)` or `Sp_n(q)` in its natural action is covered, as
   soon as the width over `Q/A` is bounded.

**The abelian layer and the relators.** The one point to check is that the relators survive the
layer, and they do:
- If some relator value `r(a)` acts nontrivially on `A`, then `[r(a), beta] = (r(a) · beta) beta^-1`
  for `beta in A`. Its image `(h - 1)A` is nonzero, and transitivity carries a nonzero element of it
  to any element of `A`. Every element of the layer costs 2 relator conjugates.
- If every relator value centralizes `A`, so does the normal closure `N` of the relator values, which
  contains the tuple. Then the layer is central along the tuple, and the template's commutators kill it.

**Model test.**
- *Trivial model.* A sofic group has unbounded width over `PSL_n(q)`, hence over `ASL_n(q)`, since the
  lower bound is the projection.
- *Real object.* For the binary Leavitt unit group `R^x`, weak models into affine special linear groups
  exist iff `R^x` is linear sofic over finite fields. That is the Gottschalk gate
  `binary-leavitt-unit-group-is-f2-linear-sofic` in characteristic 2.
- *Where the hypothesis matters.* Transitivity fails for adjoint layers `sl_n(q)` and for many copies
  of the natural module. The adjoint layers of congruence groups are treated by this lane's
  `simple-group-width-over-congruence-targets`.

**For the rigidity claim.** On `fg-simple-weakly-sofic-groups-are-sofic`, affine targets over
classical tops add no room beyond the linear-sofic horn (a) recorded there.

Derivation: `relator-width-over-transitive-abelian-extensions-proof`. Credit: elementary; bounded graph
check (no node on affine targets for relator width); no literature search.
