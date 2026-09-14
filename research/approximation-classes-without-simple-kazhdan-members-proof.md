---
rg: 2
id: approximation-classes-without-simple-kazhdan-members-proof
kind: route
title: Simplicity turns every residual approximation into an embedding, and amenability with property (T) forces finiteness
target: approximation-classes-without-simple-kazhdan-members
requires: []
---

Let `G` be an infinite finitely generated simple group with property (T).

- **Residually finite.** A finite quotient separating some `g ≠ 1` has a proper kernel of finite index. By simplicity the
  kernel is trivial, so `G` is finite, a contradiction.
- **Locally residually finite.** `G` is finitely generated, so it would be residually finite.
- **Amenable.** A discrete amenable group with property (T) is finite. Amenability gives almost invariant unit
  vectors in `ℓ^2(G)`, so (T) gives an invariant unit vector. That vector is a nonzero constant function, so `G` is
  finite. This is standard; see Bekka–de la Harpe–Valette, *Kazhdan's property (T)*, Chapter 1 (theorem number not
  re-checked).
- **Residually amenable.** Some homomorphism to an amenable group is nontrivial. Its kernel is a proper normal subgroup,
  so it is trivial, and `G` embeds in an amenable group. Then `G` is amenable, hence finite.
- **Residually solvable.** Solvable groups are amenable, so this is a case of the previous item.
