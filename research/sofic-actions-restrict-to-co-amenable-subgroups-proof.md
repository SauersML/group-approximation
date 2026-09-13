---
rg: 2
id: sofic-actions-restrict-to-co-amenable-subgroups-proof
kind: route
title: Følner sets of the coset space times a model of the restriction, glued by the section cocycle
target: sofic-actions-restrict-to-co-amenable-subgroups
requires:
  - gkp-sofic-action-toolkit
artifacts:
  - research/artifacts/pfg-positive-co-amenable-restriction-2026-09-13.md
---

Full proofs are in the artifact: Theorem 1.1, Corollaries 1.2 and 1.3, and
Lemma 2.1.

**(CA).** Fix `F`, `E`, `ε`, a section `σ : G/H → G` with `σ(H) = 1`, and the
cocycle `c(g,y) = σ(gy)^-1 g σ(y) ∈ H`, which satisfies
`c(gh,y) = c(g,hy)c(h,y)`. Let `Φ` be a Følner set of `G/H` for `F·F`. Let `ψ`
model `α|_H` on the finite cocycle set `F_H = c(F·F, Φ)` and the finite point
set `E_H = σ(Φ)^-1 E`. Define:

- `φ(g)(y,a) = (gy, ψ(c(g,y))a)` on `(Φ ∩ g^-1Φ) × A_H`, extended to a
  permutation of `Φ × A_H`;
- labels `π_(y,a)(x) = π^H_a(σ(y)^-1 x)`.

Multiplicativity is the cocycle identity plus multiplicativity of `ψ` on `F_H`,
off a Følner boundary of relative size `< 2δ`. For equivariance put
`k = c(g,y)` and `z = σ(gy)^-1 x`. Then `α(k^-1)z = σ(y)^-1 α(g^-1)x`, so (OA)
for `ψ` gives (OA) for `φ` on the good set `Φ_0 × S_H`, where
`Φ_0 = { y : Fy ⊆ Φ }`.

**(FI).** Let `H_0 = core_G(H)`. Each sheet `t_i × Y` of `G ×_H Y` is
`H_0`-invariant, and `H_0` acts on it by `β` restricted to `H_0` and twisted by
conjugation by `t_i`. That action is sofic by GKP 2.15(3). The finite union is
sofic by GKP 2.16. Then apply (CA) to the finite-index, hence co-amenable,
`H_0`.

**(LS).** Pull labels back along `ι`: `π_s(x) = π^Y_s(ι(x))`. Partial
equivariance turns the (OA) condition for `β` at `ι(x)` into (OA) for `α` at
`x`.

**(G).** Restricted to `H`, the left action `G ↷ G` is a free action of a sofic
group. It is sofic by GKP Theorem 2.14 with `N = 1` and Proposition 2.16. (CA)
makes `G ↷ G` sofic, and GKP Theorem 2.12, "in particular", makes `G` sofic.
`∎`
