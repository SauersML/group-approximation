---
rg: 2
id: o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences
kind: claim
title: An outer finite group action on O_2 is Rokhlin iff the unit class vanishes in K_0 of the fixed-point central sequence algebra, which is always properly infinite and carries a dual action on K_0
distinct_from:
  outer-actions-on-o2-kk-g-contractible-iff-rokhlin: that identifies the Rokhlin property with KK^G-contractibility; this turns both into the vanishing of one K_0-class in the fixed-point central sequence algebra.
  bootstrap-zp-actions-realize-every-cyclotomic-k-module: that proves invariants factoring through equivariant K-theory of the action cannot detect phantoms; this K_0-class lives in a non-separable algebra built from central sequences and is not such an invariant.
---

**ESTABLISHED (derivation from Szabó, Hirshberg--Winter and the Rokhlin
characterization; one standard input flagged in the proof).**  Let `G` be a
finite group, `α : G ↷ O_2` pointwise outer, `A_∞ = ℓ^∞(N, O_2)/c_0(N, O_2)`,
and `F^α := (A_∞ ∩ O_2')^α`, the fixed points of the central sequence
algebra.

1. **Proper infiniteness.**  `F^α` contains a unital copy of `O_∞`.  For
   abelian `G`, the full central sequence algebra `A_∞ ∩ O_2'` contains
   isometries `v_χ` of every eigenvalue, `α_g(v_χ) = χ(g) v_χ` for `χ ∈ Ĝ`.
   These are not fixed, but `Ad(v_χ)` maps `F^α` into itself.
2. **Criterion.**  The following are equivalent:
   - `α` has the Rokhlin property;
   - `O_2` embeds unitally into `F^α`;
   - `[1] = 0` in `K_0(F^α)`;
   - `(O_2, α) ≃_(KK^G) 0`.
3. **Self-duality.**  For abelian `G` and any unital `A` with any action `α`,
   `F_∞(A)^α = F_∞(A ⋊_α G)^(α̂)`.  So `α` absorbs `id_(O_2)` iff `α̂` does.
4. **Dual action on `K_0`.**  Let `G` be abelian.  `Φ_χ(x) = v_χ x v_χ*` is an
   endomorphism of `F^α`.  Its map `φ_χ` on `K_0(F^α)` does not depend on the
   choice of `v_χ`, and `χ ↦ φ_χ` is an action of `Ĝ` on `K_0(F^α)`.  If
   `s_g` are isometries with orthogonal ranges and `α_h(s_g) = s_(hg)`, then
   `F = Σ_g s_g s_g*` lies in `F^α` and `[F] = Σ_(χ ∈ Ĝ) φ_χ[1]`.  The following
   are also equivalent to item 2:
   - `F ~ 1` in `F^α`;
   - `Σ_(χ ≠ 1) φ_χ[1] = 0` in `K_0(F^α)`.

**Consequence for detection.**  By item 3 of
`outer-actions-on-o2-kk-g-contractible-iff-rokhlin`,
`zp-restriction-and-crossed-product-detect-kk-g-contractibility` is
equivalent to the following.  For every outer `α : Z/p ↷ O_2` with
`O_2 ⋊_α Z/p ≃_KK 0`, the unit class of `F^α` vanishes.  Equivalently,
`Σ_(k=1)^(p−1) φ^k [1] = 0`.
* The fence node says no invariant of the equivariant K-theory of the action
  can certify a phantom.  This class is not such an invariant.
* So a phantom is certified by a nonzero unit class in the K-theory of a fixed
  central sequence algebra.
* A proof of detection must show that KK-contractibility of the crossed
  product forces that class to vanish.

**Model tests.**
* The Rokhlin model `id ⊗ μ_G` has a unital `O_2` in `F^α`, by
  Hirshberg--Winter averaging.
* For the trivial action on `O_2`, `F^α = F_∞(O_2)`, which contains `O_2`, so
  `[1] = 0`.  That action is excluded by outerness: it is contractible but not
  Rokhlin.  So item 2 genuinely needs the outer hypothesis.
* Any outer action with non-contractible crossed product has `[1] ≠ 0` in
  `K_0(F^α)`, since contractibility forces the crossed product to vanish.

No priority is claimed.  Items 2 and 3 are routine given the cited theorems.
The dual action of item 4 is an observation of this lane.

Proof: `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences-proof`.
