---
rg: 2
id: kazhdan-almost-v-central-v-elements-proof
kind: route
title: Push the Kazhdan group down to the orbit space of an attracting basin, where it acts through V, then through an abelian group of translation numbers
target: kazhdan-subgroups-of-almost-v-have-no-central-v-elements
requires:
  - almost-v-fw-subgroups-act-through-finitely-many-germs
  - thompson-v-has-haagerup-property
---

Notation as in the claim.

**Input on V (read at source).** Bleak, Bowman, Gordon Lynch, Graham, Hughes, Matucci and
Sapir, *Centralizers in R. Thompson's group V_n*, arXiv:1107.0672 (e-print TeX `CIV.tex`,
tarball sha256 `ac0f66f7...190eab4`, fetched via MSI):
- every element of `V` admits a revealing pair (l. 904--912, citing Brin, *Higher
  dimensional Thompson groups*, §10.7);
- an element has finite order iff it has a revealing pair with `A = B` (Lemma
  `torsionRevPair`, l. 1116--1133);
- every component of `B - A` of a revealing pair contains an attractor, and an attractor
  gives an attracting fixed point of a power of the element whose basin contains a cone
  (Lemma `AttractorProps`, l. 1053--1075); the set of periodic attracting points is finite
  (l. 1098--1101).
If `w` has infinite order, a revealing pair has `A ≠ B`. Both trees have the same number of
leaves, so neither contains the other, and `B - A` is nonempty. So **`w` has at least one
attracting periodic point, and the set `𝒜_w` of them is finite.** Here "attracting
periodic" is topological: `w^q(a) = a` and every point of a neighborhood of `a` converges
to `a` under `w^q`. This is invariant under conjugation by homeomorphisms commuting with
`w`. The combinatorial set of the source is exactly this set: its other periodic points are
repelling or lie in cones fixed pointwise by a power.

**Local form at an attracting point.** Let `w^q(a) = a` with `a` attracting. Some cone
`cone(u)` containing `a` is mapped by `w^q` by a prefix replacement `ux ↦ u'x`, with `u'` a
prefix of `a`. If `u' = u`, points near `a` are fixed, not attracted. If `|u'| < |u|`, then
`w^q` expands distances near `a` by `2^(|u|-|u'|)`. So `u' = ue` with `e` nonempty, and
`a = u e^∞`. Put `N = cone(u)`. Then `w^q(N) = cone(ue) ⊊ N` and the intersection of all
`w^(qn)(N)` is `{a}`.

## Proof of item 1

1. **Fix the point.** Each `γ in Λ` commutes with `w`, so it permutes the finite set `𝒜_w`.
   So a finite-index `Λ_1 <= Λ` fixes `𝒜_w` pointwise. Fix `a in 𝒜_w`, choose `q` and `N` as
   above, and put `w' = w^q`. `Λ_1` has (T).
2. **Basin and fundamental domain.** Let `B = ⋃_{n>=0} w'^-n(N)`, the basin of `a`, which is
   open. Put `D = N \ w'(N) = cone(u) \ cone(ue)`, which is clopen and compact. For
   `x in B \ {a}`, the set `{n in Z : w'^n x in N}` is nonempty and upward closed. It is
   bounded below, since otherwise `x` lies in every `w'^k(N)`, so `x = a`. Its minimum `n_0`
   gives `w'^(n_0) x in D`. So `B \ {a}` is the disjoint union of the sets `w'^n(D)` (it is
   nonempty because `C` has no isolated points), and
   `π(x) =` the unique point of `w'^Z x` in `D` is continuous.
3. **The action descends.** Each `γ in Λ_1` fixes `a` and commutes with `w'`, so it
   preserves `B \ {a}` and `w'`-orbits. Put `ψ(γ) = π ∘ γ|_D : D -> D`. It is a
   homeomorphism with inverse `ψ(γ^-1)`, and `ψ` is a homomorphism because `π(γ w'^j y) =
   π(γ y)`.
4. **The action is V-local on the basin.** `sing(γ)` is finite. Since `w in V`, conjugation
   gives `sing(wγw^-1) = w(sing γ)`, and `wγw^-1 = γ`, so `sing(γ)` is a finite `w`-invariant
   set and consists of `w`-periodic points. `B \ {a}` contains none: a `w`-periodic point is
   `w'`-periodic, and a `w'`-periodic point of `B` converges to `a`, so it is `a`. So `γ` is
   V-local at every point of `B \ {a}`. Near `x in D`, `ψ(γ) = w'^-n ∘ γ` for a locally
   constant `n`, a composite of V-local maps.
5. **Into V.** Extend `ψ(γ)` by the identity off the clopen set `D`. The result is a
   homeomorphism of `C` that is V-local at every point. By compactness it is a prefix
   replacement on the cones of a finite partition, so it lies in `V`. So `ψ(Λ_1) <= V`.
   It has (T), so by `thompson-v-has-haagerup-property` it is finite. Put
   `Λ_2 = ker ψ`, of finite index in `Λ`.
6. **Translation numbers.** For `γ in Λ_2` and `x in B \ {a}`, `γ(x) = w'^(n_γ(x)) x` for a
   unique integer `n_γ(x)`, since `w'` acts freely on `B \ {a}`. The function `n_γ` is
   locally constant and `w'`-invariant, so it is determined by its restriction to `D`, a
   locally constant function `D -> Z`. For `γ, δ in Λ_2`,
   `n_(γδ)(x) = n_γ(δ x) + n_δ(x) = n_γ(x) + n_δ(x)` by `w'`-invariance. So `γ ↦ n_γ|_D` is
   a homomorphism from `Λ_2` to the torsion-free abelian group `C(D, Z)`. `Λ_2` has (T), so
   its abelian quotients are finite. A finite subgroup of `C(D, Z)` is trivial. So
   `n_γ = 0` for all `γ in Λ_2`, and `Λ_2` fixes `B` pointwise. `∎`

## Proof of item 2

Replace `Λ` by `k^-1 Λ k <= H` and `w` by `k^-1 w k in V`. Then `w` is central in `Λ`, so
it commutes with `Λ`. Suppose `w` has infinite order. Item 1 gives `a in 𝒜_w`, `w' = w^q`,
and a finite-index `Λ_2 <= Λ` fixing the basin `B` of `a` pointwise. `w` lies in `Λ`, so
`w'^m in Λ_2` for some `m >= 1`. But `w'^m` moves every point of `B \ {a}`, a nonempty set.
This is a contradiction. `∎`
