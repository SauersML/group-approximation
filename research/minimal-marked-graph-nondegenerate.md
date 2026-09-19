---
rg: 2
id: minimal-marked-graph-nondegenerate
kind: claim
title: The minimal marked orbital graph has zero adjacency radical
distinct_from:
  minimal-marked-graph-private-neighbour: that is the combinatorial separation property, quantified over all finite vertex sets and stated inside the G-set; this is the linear-algebraic consequence for one bilinear form, and it is strictly weaker — it is exactly the mod-2 shadow of the private-neighbour statement at each finite support.
  invariant-graph-clifford-phase: that proves the equivalence "b_S nondegenerate <=> A_S is a factor <=> <z> is the monolith" for the whole family; this evaluates the left-hand side for the minimal member, which that claim leaves open.
  marked-double-coset-infinite-degree: that measures the degree of this same graph and finds it infinite, which deletes the finite-degree part of the family; this measures the radical of its adjacency form and finds it zero, which keeps the minimal member inside the usable part.
artifacts:
  - research/artifacts/kun-thom-private-neighbour-2026-08-18.md
---

With the Kun--Thom Laurent pair, `X = G/Γ` and `S_min` the orbital graph of
the marked double coset `ΓhΓ` as in `minimal-marked-graph-private-neighbour`,
let `b = b_{S_min}` be the alternating `F_2`-form on `V = F_2^{(X)}` with
`b(δ_x, δ_y) = 1` iff `x ∼ y`.  Then

```text
Rad(b_{S_min}) = 0.
```

In particular no two distinct vertices are twins: `gΓhΓ ≠ ΓhΓ` for `g ∉ Γ`.

**What this decides.**  By `invariant-graph-clifford-phase` item 4, this is
equivalent to each of: `Z(Ṽ_{S_min}) = ⟨z⟩`; the twisted lamp algebra
`A_{S_min}` at the central character `z ↦ −1` is a factor, hence the
hyperfinite `II₁` factor; and — `G` acting faithfully on `X` — `⟨z⟩` is the
monolith of `W̃_{S_min}`, so `W̃_{S_min}` is a minimal nonsofic quotient of
`H` in which the marked radical word survives.

It therefore settles the sub-question posed in
`invariant-graph-crossed-product-ce`: the minimal member of the
invariant-graph family does **not** reintroduce a `G`-invariant abelian
direction in the centre of the base, so the coordinate the Kun--Thom
permutation-normalization argument acts on is absent from the cheapest model,
not merely from the complete one.  The existential over graphs in that
claim's algebraic half can be discharged by the minimal graph; what remains
of that claim is exactly `minimal-marked-graph-crossed-product-ce`.

## Scope

This is nondegeneracy of one form on the full infinite space `V`.  It does
**not** say that the restriction of `b` to an arbitrary finite window is
nondegenerate — that is false in general, and the repair is
`vertex-supported-symplectic-completion`.  It says nothing about Connes
embeddability, and it does not contradict the finite-rank invariant-form
no-go: the nondegenerate finite subspaces produced downstream are not
`G`-invariant.
