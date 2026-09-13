---
rg: 2
id: radu-horizontal-quotient-is-quaternionic-s-arithmetic
kind: claim
title: Radu's BMW lattice maps with free kernel onto a discrete subgroup of PGL_2(Q_2) x PGL_2(Q_2) normalizing a maximal order of the definite quaternion algebra over Q(sqrt17)
distinct_from:
  radu-horizontal-tree-group-is-linear: that proves the horizontal quotient is linear and 2-adically realizes the horizontal tree; this identifies it with an S-arithmetic group of a quaternion algebra, discrete in a product of two trees
  radu-bmw-lattice-embeds-in-titz-witzel-kernel: that embeds the lattice in a Kazhdan building lattice; this maps it onto an arithmetic group acting properly on a product of two trees
---

**ESTABLISHED (unreviewed).** Let `ρ : Γ_R → PGL_2(K)` be the representation of
`radu-horizontal-tree-group-is-linear`, and `Q = ρ(Γ_R) ≅ Γ_R/Λ_v`. Let `F = Q(w)` with
`2w^2 − w − 2 = 0`, that is `w = (1 ± √17)/4` and `F = Q(√17)`. Put

```text
g = ρ(ba)/m,   h = ρ(abxyxy)/(4m(m+1)^2)    (both in SL_2(K)),
B = F⟨1, g, h, gh⟩,   O = Z[1/2][w]⟨1, g, h, gh⟩.
```

1. **The algebra.** `tr g = w`, `tr h = −1/2`, `tr gh = 1/2 − w`, and `tr[g,h] = 0`. `B` is a
   quaternion algebra, ramified at both real places of `F` and at no finite place. The
   standard formula gives `B ≅ (tr^2 g − 4, tr[g,h] − 2)_F = (w^2 − 4, −2)_F`, but the proof
   does not use it.
   So `B` is the totally definite quaternion algebra over `Q(√17)` with trivial finite
   discriminant.
2. **The order.** `O` is a maximal `Z[1/2][w]`-order: the Gram determinant of the reduced
   trace form on `1, g, h, gh` is `−4`, an `S`-unit for `S = {primes above 2}`.
3. **Normalizing.** Conjugation by each of `ρ(a), ρ(b), ρ(c), ρ(x), ρ(y), ρ(z)` maps `O` onto
   `O`. So `Q` embeds in `N(O)/F^×` inside `PB^×(F)`.
4. **Discrete in two trees.** `2` splits in `F` as `𝔮𝔮'`, both with residue field `F_2`, and
   `B` splits at both. `N(O)/F^×` is discrete in
   `PB^×(F_𝔮) × PB^×(F_𝔮') ≅ PGL_2(Q_2) × PGL_2(Q_2)`, since the real factors are compact.
   So `Q` acts properly on the product `T_h × T'` of two 3-regular Bruhat–Tits trees. The first
   factor is the horizontal tree action of `Γ_R` (at `𝔮`, `v_𝔮(m) = ±1`).
5. **Consequences.**
   * `Γ_R` surjects, with infinitely generated free kernel `Λ_v`, onto a discrete irreducible
     subgroup `Q` of `Aut(T_3) × Aut(T_3)`.
   * The vertex stabilizer `ρ(V)`, a quotient of `PGL_2(Z)`, is discrete in `PGL_2(F_𝔮')` and
     acts properly on `T'`.
   * Radu's non-residual finiteness lives entirely in the kernel of the map to this
     arithmetic group.

Whether `Q` has finite index in `N(O)/F^×`, i.e. is a cocompact arithmetic lattice, is
`radu-horizontal-quotient-is-arithmetic-lattice`.

**Credit.** Titz Mite–Witzel (arXiv:2509.05054v2, Remark 3.6) give `Φ : D → SL_2(Q(√−15, √17))`
on the derived subgroup `D = <abxyxy, ba>`. `tr Φ(abxyxy) = −1/2` and
`tr Φ(ba) = −(1+√17)/4` agree with `tr h` and with `−tr g` at the place `w = (1+√17)/4`, as
expected for SL_2-lifts `±g`. This is consistent with `Φ` being `ρ|_D` up to sign and
conjugacy; that identification was not checked further. The quaternion algebra, the maximal order, and the discreteness in two trees
are observed here. A bounded check (Titz Mite–Witzel pp. 9–11, Radu arXiv:1712.01091
pp. 1–8, Burger–Mozes *Lattices* §2.4) found no statement of them.

Proof in `radu-horizontal-quotient-is-quaternionic-s-arithmetic-proof`.
