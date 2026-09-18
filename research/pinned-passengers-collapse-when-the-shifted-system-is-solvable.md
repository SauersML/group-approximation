---
rg: 2
id: pinned-passengers-collapse-when-the-shifted-system-is-solvable
kind: claim
title: In a pinned HNN-recursive annular germ group, if the pinning system with shifted driver data has any solution in the base, the passenger already lies in the driver; so a genuinely non-ascending pinned host needs the passenger's depth transport to be definable over the driver but unrealized in the base
requires:
  - fp-annular-germ-groups-are-hnn-recursive
  - fp-rf-groups-embed-in-hnn-recursive-annular-germ-groups
  - pinned-annular-passengers-are-class-functions-of-the-driver
distinct_from:
  pinned-annular-passengers-are-class-functions-of-the-driver: that constrains the driver at a single depth; this constrains how the pinned passenger interacts with the HNN stable letter.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

**Setting.** The germ group is `E = ⟨L, s | s^{-1} ℓ s = μ̂(ℓ), ℓ ∈ L_1⟩`, with:
- `L_1 = M̂`, the driver germs, and `μ̂(L_1) ⊆ L_1`;
- `L = ⟨M̂, Ĝ⟩`;
- `s = t b`, with `b ∈ B_p` and `t` the zoom.

This is the shape of `fp-annular-germ-groups-are-hnn-recursive`, with θ = μ̂. The passenger `ĝ` (a
tuple of germs) is pinned: for `n ≥ n_0`, `ĝ(n)` is the unique solution in `V` of `R(x; m̂(n)) = 1`.

**Theorem.**
1. `y := s^{-1} ĝ s` satisfies `R(y; μ̂(m̂)) = 1` in `E`, and at every large depth it is the unique
   `V`-solution of the depth-`n` system with parameters `μ̂(m̂)(n)`.
2. **Collapse.** Suppose some tuple `λ ∈ L` satisfies `R(λ; μ̂(m̂)) = 1`. Then `λ = y`, and `ĝ ∈ L_1`:
   the passenger is a driver germ, which is the ascending / telescope case.
3. Hence in a pinned host with a passenger outside the driver, the shifted systems
   `R(x; μ̂^k(m̂)) = 1` (`k ≥ 1`) have no solution in `L` at all. They are solved in `E` by
   `s^{-k} ĝ s^k`, which lies in `s^{-k} L s^k ∖ L`.

**Proof.**
1. Conjugate `R(ĝ; m̂) = 1` by `s` and use `s^{-1} m̂ s = μ̂(m̂)`. Depthwise,
   `μ̂(m̂)(n) = b(n)^{-1} m̂(n+1) b(n)` with `b(n) ∈ V`. So the depth-`n` shifted system is the
   depth-`(n+1)` system conjugated by `b(n)`, and its unique solution is
   `b(n)^{-1} ĝ(n+1) b(n) = y(n)`.
2. `λ` solves the shifted system at every large depth, so by 1 `λ(n) = y(n)` eventually. Hence
   `λ = y` as germs, and `y ∈ L ∩ s^{-1} L s`. By Britton's lemma, `L ∩ s^{-1} L s = s^{-1} L_1 s`:
   a reduced word `s^{-1} λ' s λ''` with `λ' ∈ L ∖ L_1` is nontrivial. So `s^{-1} ĝ s = s^{-1} λ' s`
   with `λ' ∈ L_1`, i.e. `ĝ ∈ L_1`.
3. Apply 2 to `s^{-k}`-conjugates.

## Lesson for general BH

A one-point finitely presented host can carry a passenger that is not in its driver only if the
passenger's depth transport is **definable but not realized**. `s^{-1}ĝs` is pinned by the shifted
driver data, so it is determined by them, yet no element of the base group `L` may realize it. If one
did, uniqueness would force it to be the transport and pull the passenger back into the telescope.
So the non-ascending regime is exactly the place where "a unique solution exists in `V` at every
depth" and "no solution exists in the finitely generated group `L`" coexist. This is a compactness
gap. Finitely many equations must have unique solutions at every finite level, with no uniform
witness in the base. That gap is the one-point analogue of the master route's requirement that the
compiler's rigidity have no normal form: bh-g3-libridge's cap on normal forms, and bh-free-32's
definability cap.
