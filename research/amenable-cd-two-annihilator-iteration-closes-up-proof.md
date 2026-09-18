---
rg: 2
id: amenable-cd-two-annihilator-iteration-closes-up-proof
kind: route
title: The annihilator of a zero divisor is a non-finitely-generated projective of non-integral dimension, whose trace ideal regenerates thinner zero divisors
target: amenable-cd-two-annihilator-iteration-closes-up
requires:
  - l2-small-projectives-with-rank-gap-are-finitely-generated
  - amenable-principal-fp-group-algebras-are-domains
  - elementary-amenable-torsion-free-strong-atiyah
---

Notation as in the target. Modules are left modules, and `⊗ = ⊗_{Q[G]}`. `dim = dim_NG` is Lück's
extended dimension. `rk(a) = dim(NG a)`. For `x ∈ NG`, `l(x)` is its left support projection, the
smallest projection `q` with `q x = x`, and `r(x)` its right support, the smallest `p` with
`x p = x`.

## Imports

- **(I1)–(I5)** are those of `amenable-principal-fp-group-algebras-are-domains-proof`: additivity
  of `dim` and `dim NG^m e = tr(e)`; amenable dimension-flatness,
  `dim Tor_p^{Q[G]}(NG, M) = 0` for `p >= 1`; integral traces of idempotents over `Q[G]` for
  torsion-free amenable `G` (Step 0 there, from Higson–Kasparov and the Baum–Connes trace theorem);
  positivity `dim NG b > 0` for `b ≠ 0`; and `pd_{Q[G]} M <= cd_Q G` for every `M`.
- **(I6) Supports.** For `x ∈ NG`, `ann_l^{NG}(x) = NG(1 − l(x))`, so `dim NG x = tr(l(x))`. The
  projections `l(x)` and `r(x)` are Murray–von Neumann equivalent (polar decomposition), so
  `tr l(x) = tr r(x)`. Since `l(x*) = r(x)`, this gives `dim NG x* = dim NG x`. (Standard; Lück,
  *L²-invariants*, §6.1 and §8.1.)
- **(A.1)** Item 1 of `l2-small-projectives-with-rank-gap-are-finitely-generated`, over `Q[G]`. That
  node records that items 1–2 hold verbatim over `Q[G]`. Its dimension `dim_U(U ⊗ P)` equals
  `dim(NG ⊗ P)`, and `dim_U(U b) = dim(NG b)`, because `U` is flat over `NG` and
  `dim_U(U ⊗_{NG} N) = dim_NG N` (its import (J1)).

## Lemma 0 (the annihilator formula; any amenable `G`)

Let `0 ≠ a ∈ Q[G]`, `J = ann_l(a) = {x ∈ Q[G] : xa = 0}`, and `M = Q[G]/Q[G]a`. Then
`dim(NG ⊗ J) = 1 − rk(a)`.

This is the computation "Dimension of `L`" in Step 2 of
`amenable-principal-fp-group-algebras-are-domains-proof`, and it uses only (I1), (I2) and (I4).
The exact sequences are `0 → J → Q[G] → Q[G]a → 0` and `0 → Q[G]a → Q[G] → M → 0`. Tensoring
them with `NG` changes dimensions only by quotients of `Tor_1` terms, which have dimension 0.
Torsion-freeness is not used. ∎

## Item 1

*Left.* If `J = 0`, then `rk(a) = 1` by Lemma 0. If `0 ≠ b ∈ J`, then `ba = 0`, so
`NG b ⊆ ann_l^{NG}(a) = NG(1 − l(a))` by (I6). By (I4) and (I1),
`0 < dim NG b <= 1 − tr l(a) = 1 − rk(a)`. So `rk(a) < 1` iff `ann_l(a) ≠ 0`, that is, iff `a` is a
left zero divisor.

*Right.* The involution `(Σ λ_g g)* = Σ λ_g g^{-1}` preserves `Q[G]`. `ac = 0` with `c ≠ 0` iff
`c* a* = 0` with `c* ≠ 0`. So `a` is a right zero divisor iff `a*` is a left zero divisor. By the
left case this holds iff `rk(a*) < 1`, and `rk(a*) = rk(a)` by (I6). ∎

## Item 2

Let `a ≠ 0` be a zero divisor, `J = ann_l(a)` and `M = Q[G]/Q[G]a`. By (I5), `pd M <= 2`. From
`0 → Q[G]a → Q[G] → M → 0` with `Q[G]` free, `pd Q[G]a <= 1`. From
`0 → J → Q[G] → Q[G]a → 0`, dimension shifting makes `J` projective.

By Lemma 0, `dim(NG ⊗ J) = 1 − rk(a)`. Here `rk(a) > 0` by (I4), and `rk(a) < 1` by item 1. So the
dimension lies in `(0,1)`.

Suppose `J` were finitely generated. Then `J ≅ Q[G]^m e` for an idempotent matrix `e`, and
`NG ⊗ J ≅ NG^m e`. Its dimension `tr(e)` is an integer by (I3), which contradicts
`dim ∈ (0,1)`. So `J` is not finitely generated. ∎

## Item 3

`J` is projective, not finitely generated, and `L²`-small (`dim(NG ⊗ J) < 1`). Take
`0 < ε < 1`. By (A.1) there is `0 ≠ b ∈ T(J)` with `rk(b) < ε < 1`. Here
`T(J) = Σ_{f ∈ Hom_{Q[G]}(J, Q[G])} f(J)`, and `b` may be taken as `f_i(x)` for a dual-basis
functional `f_i`. By item 1, `b` is a zero divisor. ∎

## Item 4

`1 = rk(1) ∈ Σ(G)`. If some `0 ≠ a` has `rk(a) < 1`, then `a` is a zero divisor by item 1. Items 2
and 3 then give zero divisors of rank below any `ε > 0`, so `inf Σ(G) = 0`. Otherwise every nonzero
element has rank 1, and item 1 says there are no zero divisors.

If `cd_Q G <= 1`, then `pd M <= 1` by (I5), so `Q[G]a` is projective. The sequence
`0 → J → Q[G] → Q[G]a → 0` then splits, and `J = Q[G]e` for an idempotent `e`. `J` is finitely
generated, so by item 2 `a` is not a zero divisor. ∎

## Item 5

Start with a zero divisor `a_0`. Given a zero divisor `a_n`, apply item 3 to `ann_l(a_n)` with
`ε = rk(a_n)/2`. This gives a zero divisor `a_{n+1} ∈ T(ann_l(a_n))` with
`rk(a_{n+1}) < rk(a_n)/2`. Then `rk(a_n) < 2^{-n} rk(a_0) → 0`, and by item 2
`dim(NG ⊗ ann_l(a_n)) = 1 − rk(a_n) ↑ 1`.

Each step uses item 1 (dimension-flatness and supports), (I5) (`gl.dim <= 2`), (I3) (integrality)
and (A.1), each on the element `a_n` alone. Their hypotheses are "`G` torsion-free amenable with
`cd_Q G <= 2`" and "`a_n` is a zero divisor". The first is fixed, and the second is the output of
the previous step. So the chain exists for every group with one zero divisor, and every
proposition obtained along it follows from "`Q[G]` has a zero divisor". A contradiction therefore
needs a further input that is incompatible with one zero divisor, that is, by item 4, an input
equivalent to `Q[G]` being a domain.

*Følner densities.* For amenable `G`, Elek's theorem identifies the normalized kernel dimensions of
`a_n` on Følner sets with `1 − rk(a_n)` (recalled, not used). Adding Følner or Elek approximation to
the list of inputs adds only the statement "these densities tend to 1", which is item 5 itself. ∎

## Item 6

`B = ⊕_{k∈Z} Z/2 = ⟨g_k⟩` is countable and locally finite, so `cd_Q B <= 1`: it is a countable
directed union of finite groups, each of `Q`-cohomological dimension 0. Then
`cd_Q L <= cd_Q B + cd_Q Z <= 2` for `L = B ⋊ Z`. By (I5), `gl.dim Q[L] <= 2`. `L` is amenable,
so (I2), item 1 and Lemma 0 hold for `L`.

`e_n = ∏_{k=1}^n (1+g_k)/2` is a self-adjoint idempotent, hence a projection, with
`rk(e_n) = tr(e_n) = 2^{-n}` by (I1). It is a zero divisor, since `e_n(1 − e_n) = 0`. If
`x e_n = 0`, then `x = x(1 − e_n)`, so `ann_l(e_n) = Q[L](1 − e_n)`. This is finitely generated,
of dimension `1 − 2^{-n} ∉ Z`. So the conclusion of item 2 fails for `L`, and only through (I3),
which needs torsion-freeness. `L` is not a counterexample to the target, because `cd_Z L = ∞`. ∎

## Remark R

`G` is finitely generated, amenable, `cd_Z G = 2`, and `ab = 0` with `a, b ≠ 0`. Let
`H = ⟨supp a ∪ supp b⟩`, finitely generated with `cd_Z H <= 2`, and `Q[H]` not a domain.

- If `cd H <= 1`, then `H` is free (Stallings–Swan) and amenable, so `H` is `1` or `Z`, and `Q[H]`
  is a domain.
- If `H` is elementary amenable, then `C[H]` is a domain by
  `elementary-amenable-torsion-free-strong-atiyah`.

So `cd H = 2` and `H` is not elementary amenable. Hence `H` is not solvable, and it is a
two-dimensional counterexample to Kropholler's question. ∎
