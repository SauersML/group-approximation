---
rg: 2
id: oyakawa-graph-wreath-rf-iff-acting-group-rf-proof
kind: route
title: Properness and local finiteness discharge Needham's separation conditions
target: oyakawa-graph-wreath-rf-iff-acting-group-rf
requires:
  - needham-graph-wreath-rf-criterion
  - oyakawa-graph-wreath-hyperbolic
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Write `W = X(H) ⋊ G` with `X` locally finite, `G` acting properly, `H` finite
nontrivial.

**Necessity.**  `G` embeds in `W` as a complement, and residual finiteness
passes to subgroups.

**Sufficiency.**  Assume `G` residually finite and check the three conditions
of `needham-graph-wreath-rf-criterion` with `Γ = G`, `Δ = H`.

*Condition 1.*  `H` is finite, hence residually finite; `G` is residually
finite by hypothesis.

*Condition 2, second alternative* (the one with no abelian hypothesis on the
lamp group).  Fix `v ∈ V(X)`.  Properness makes `Stab_G(v)` finite and local
finiteness makes `N(v)` finite, so

```text
F_v = {g in G : g·v in N(v)}
```

is finite: for each `u ∈ N(v)` the transporter `{g : g·v = u}` is empty or a
coset of `Stab_G(v)`.  The graph is simplicial, so `v ∉ N(v)` and hence
`1 ∉ F_v`.  Residual finiteness gives `K ⊴_f G` avoiding the finitely many
elements of `F_v`, and then `K·v ∩ N(v) = ∅`.

*Condition 3.*  Let `v ≠ w` be non-adjacent.  The same transporter argument
applied to the finite set `N(v) ∪ {v}` makes

```text
F_(v,w) = {g in G : g·w in N(v) ∪ {v}}
```

finite, and `1 ∉ F_(v,w)` precisely because `w` is neither `v` nor a
neighbour of `v`.  A finite-index `K` avoiding `F_(v,w)` gives
`K·w ∩ (N(v) ∪ {v}) = ∅`.

Needham's criterion then makes `W` residually finite.

**Why the hypotheses are used exactly where they are.**  Local finiteness
makes the *target* neighbourhood finite; properness makes each *transporter*
finite; the two together are what turn a separability requirement about an
infinite action into avoidance of a finite subset of `G`, which is all
residual finiteness can ever give.  Both fail in Oyakawa's relative Theorem
1.3, which is why the argument stops at Corollary 1.4.
