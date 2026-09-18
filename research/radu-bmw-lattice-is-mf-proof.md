---
rg: 2
id: radu-bmw-lattice-is-mf-proof
kind: route
title: Radu's lattice is a free-kernel lift of a linear group acting on the vertical tree, so the free generalized wreath MF theorem applies
target: radu-bmw-lattice-is-mf
requires:
  - free-generalized-wreath-over-residually-finite-group-is-mf
  - free-kernel-tree-actions-embed-in-free-generalized-wreath
  - radu-horizontal-tree-group-is-linear
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - radu-mark-is-controlled-by-one-commutator
  - universal-mf-quotient
---

## Item 1

**Setup.**
- *Trees and kernel.* `Γ_R` acts simply transitively on the vertices of `T_h × T_v`
  (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`). Put
  `Λ_v = ker(Γ_R -> Aut(T_h))`, which is normal. By `radu-horizontal-tree-group-is-linear`,
  items 2--3, `Λ_v = ker ρ` is free, and `Q = Γ_R/Λ_v ≅ ρ(Γ_R) ⊆ PGL_2(K)` is finitely generated
  linear, hence residually finite.
- *`Λ_v` fixes no vertex of `T_v`.* If `g ∈ Λ_v` fixes `v ∈ T_v`, it fixes `(u, v)` for every
  vertex `u ∈ T_h`. Simple transitivity then gives `g = 1`.
- *`Λ_v` inverts no edge of `T_v`.* If `g ∈ Λ_v` inverts an edge, `g^2` fixes its endpoints, so
  `g^2 = 1`. `Λ_v` is torsion-free, so `g = 1`.

**Conclusion.** Item 1 of `free-kernel-tree-actions-embed-in-free-generalized-wreath` gives
`Γ_R ↪ Z ≀^*_(E^±(Λ_v\T_v)) Q`. The corollary of
`free-generalized-wreath-over-residually-finite-group-is-mf` makes `Γ_R` MF. Subgroups of MF
groups are MF, which covers `π_1(S_R)`. `universal-mf-quotient` turns MF into triviality of the
radical.

## Item 2

`δ^4 != 1` in `Γ_R`: it is a nontrivial element of the finite residual, since `Γ_R` is not
residually finite and `δ^(±4)` are the shortest such elements
(`radu-bmw-lattice-embeds-in-titz-witzel-kernel`, item 2). Let `Φ : Γ_R -> U(\mathcal A)` be an
injective homomorphism into a norm corona `\mathcal A = prod M_(d_n) / (+) M_(d_n)`, and take
stage representatives `a_n, ..., z_n` of the images of the generators.

Each relator maps to `1` in `\mathcal A`. The corona norm is `limsup_n` of the stage norms, so the
relator defects tend to `0`. Moreover `||Φ(δ^4) - 1|| = limsup_n ||δ_n^4 - 1|| > 0`, since `Φ` is
injective. Replacing each stage unitary by a nearby unitary changes none of these limits.

## Item 3

In `U(\mathcal A)` the metric `d(u,v) = ||u - v||` is bi-invariant, and `Φ(a), ..., Φ(z)` are
involutions satisfying the six relators exactly. (RL1) of `radu-mark-is-controlled-by-one-commutator`,
at zero defect, gives

```text
0 < ||Φ(δ^4) - 1||  <=  2 ||Φ(u δ) - Φ(δ u)||  =  2 ||Φ([u, δ]) - 1||,        u = y δ^2 y.
```

The last equality uses bi-invariance. Taking stage representatives as in item 2 gives item 3.

## Consequence

- `π_1(S_R) ⊆ K` is MF, so no non-MF subgroup of `K` lies inside it.
- The chain of exact-quotient implications behind non-residual finiteness (Titz Mite--Witzel
  Proposition 3.4(4) with Lemma 3.5) has only one step that is not quantitative in every
  bi-invariant metric: the collapse of `[u, δ]`. Item 3 shows that step fails in operator norm.

∎
