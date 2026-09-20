---
rg: 2
id: jones-subgroup-coset-spaces-carry-invariant-orders
kind: claim
title: For every Jones subgroup F_n and every endomorphism psi of Thompson's group F, the coset space of psi^{-1}(F_n) carries an F-invariant total order, so no explicitly known non-parabolic maximal subgroup of F is a point stabilizer of a 2-transitive action
distinct_from:
  jones-subgroup-cosets-form-a-parity-lamplighter: that gives the coset space of the Jones subgroup as an affine lamplighter action on finite sets of dyadics; this puts an F-invariant lexicographic total order on the coset spaces of every Jones subgroup F_n and of all their pullbacks under endomorphisms of F
  thompson-f-two-transitive-colour-pairs-are-totally-mixed: that constrains colourings of irrational orbits in a hypothetical 2-transitive action; this is about digit-sum colourings of the dyadics, whose pairwise disagreement sets always have a least point, and it excludes concrete subgroups
  thompson-f-known-maximal-subgroups-are-jones-pullbacks: that imports the literature facts; this proves the ordering theorem and applies it to them
artifacts:
  - experiments/thompson-f-2-transitive-2026-09-17/jones_coset_order_check.py
---

**ESTABLISHED (lane proof, unreviewed).** Let `D` be the dyadic rationals in `(0,1)`. For
`n ≥ 2`, let `c_n : D → ℤ/n` be the binary digit sum mod `n`. Let `F` act on functions
`D → ℤ/n` by `g·φ = φ ∘ g^{-1}`.

1. **First-disagreement lemma.** Let `g ∈ F` have tree pair with leaves `w_1, …, w_k → v_1, …, v_k`
   in left-to-right order. Then `g·c_n − c_n` is constant, equal to `ds(w_i) − ds(v_i) mod n`, on
   `[.v_i, .v_i + 2^{−|v_i|}) ∩ D`. It vanishes on the first range leaf. So if `g·c_n ≠ c_n`, the
   set where `g·c_n` and `c_n` differ has a **least element**, namely the left endpoint `.v_i` of
   the first leaf with `ds(w_i) ≢ ds(v_i)`. The same then holds for any two distinct points of the
   orbit `F·c_n`.
2. **Invariant order.** For `φ ≠ ψ` in `F·c_n`, let `μ` be the least point where they differ.
   Put `φ ≺ ψ` iff `φ(μ) < ψ(μ)`, reading `ℤ/n` as `{0, …, n−1}`. This is a strict total order on
   `F·c_n ≅ F/\vec F_n`, and `F` preserves it.
3. **Pullbacks.** For every homomorphism `ψ : F → F`, the `F`-set `F/ψ^{-1}(\vec F_n)` embeds
   `F`-equivariantly (`f` acting through `ψ(f)`) into `F·c_n`. So it carries an `F`-invariant
   total order too; that is, `ψ^{-1}(\vec F_n)` is relatively convex in `F`. The same holds for all
   conjugates.
4. **Consequence for Problem 2.20.** An action preserving a total order on a set of at least two
   points has no self-paired non-diagonal orbital, so it is not 2-transitive. By
   `thompson-f-known-maximal-subgroups-are-jones-pullbacks`, none of the following is the point
   stabilizer of a 2-transitive action of `F`:
   - the Golan–Sapir maximal subgroup `Ψ^{-1}(\vec F)`;
   - Golan's maximal subgroups `ν(\vec F_p)`, `p` prime;
   - any conjugate of these.

   Parabolic maximal subgroups `Stab(α)` are excluded the same way, using the order of `F·α ⊂ (0,1)`.

**What this changes.** Every maximal subgroup of infinite index of `F` that is given explicitly
in [Golan–Sapir 2015] or [Golan 2022] now fails as the stabilizer of a 2-transitive action, and
fails for the strongest possible reason: an invariant order. These subgroups are the candidates
listed under `thompson-f-admits-a-faithful-2-transitive-action`.

The test protocol recorded there (T1: "the extreme point lies in the second set only") was
marked "not yet run on a concrete maximal candidate". Its stated difficulty was that "dense
self-similar sets such as the odd digit sum dyadics make Δ accumulate at its extreme points". That
is false at the left end. `S Δ gS` is a finite union of standard dyadic intervals `[a,b) ∩ D`, so
its minimum is attained; only the supremum can fail to be attained, at `1`. Test T1 therefore
applies, and it kills these candidates.

**What survives.** The following remain untested:
- maximal subgroups obtained by Zorn's lemma above finitely generated `H` with `H[F,F] = F`
  (Golan–Sapir §4, Golan Theorem `thm:int4`);
- Golan's later maximal subgroups with exactly `n` orbits on `D` ([G23], cited in the revision of
  arXiv:2209.03244);
- any maximal subgroup that is not a pullback of a colouring stabilizer.

**Check.** `experiments/thompson-f-2-transitive-2026-09-17/jones_coset_order_check.py` tests
item 1 exactly on random tree pairs, and item 2 on a dyadic grid, for `n = 2, 3, 5`. The grid tests
cover antisymmetry, the transport of the first-difference point and its colour pair by `f`, and
transitivity. Every check passes.

Scope: elementary; no novelty is claimed for item 2 beyond its use here. The identification of
`Stab(c_n)` with `\vec F_n`, and of the maximal subgroups, is imported.

Proof route: `jones-subgroup-coset-spaces-carry-invariant-orders-proof`.
