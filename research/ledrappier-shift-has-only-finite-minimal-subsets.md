---
rg: 2
id: ledrappier-shift-has-only-finite-minimal-subsets
kind: claim
title: (FL, REFUTED 2026-09-19) Every Z^2-minimal subset of Ledrappier's shift is finite, equivalently every nonempty closed invariant subset contains a periodic point; a characteristic-2, topological analogue of Furstenberg's x2 x3 theorem for minimal sets, which would rule out algebraic T1 on every Ledrappier power
requires:
  - algebraic-t1-needs-an-infinite-minimal-subset-of-ledrappier
distinct_from:
  algebraic-t1-needs-an-infinite-minimal-subset-of-ledrappier: that proves (FL) rules out algebraic T1 and gathers partial evidence; this states (FL) as the open crux, with its equivalent forms and first tests.
  free-minimal-triangle-permutive-sft-exists: that asks for, and conjectures against, a free minimal sub-SFT; (FL) concerns all closed invariant subsets, not only sub-SFTs, and implies the conjectured refutation form.
---

**REFUTED** (lane bh-bq2, 2026-09-19, lane proof, not reviewed): `ledrappier-shift-has-infinite-toeplitz-minimal-subsets` builds a non-periodic Toeplitz point of `X_L`, so `X_L` has infinite minimal subsets. The statement is kept below for the record.

## Statement

Let `X_L = {x ∈ F_2^(Z^2) : x(v + e_2) = x(v) + x(v + e_1)}`. **(FL):** every `Z^2`-minimal subset of `X_L` is
finite. The following are equivalent forms:
- every uniformly recurrent point of `X_L` is doubly periodic;
- every nonempty closed `Z^2`-invariant subset of `X_L` contains a periodic point;
- in the `S`-adic model `X_L = K_S/A`, with `A = F_2[s^(±1), (1+s)^(-1)]`, every closed set invariant under `×s`
  and `×(1+s)` contains a point of finite orbit.

The first and second forms are equivalent because every closed invariant set contains a minimal subset.

## Consequences

- **T1.** No power `X_L^n` has an infinite minimal subset, so algebraic T1 (the time-lift face of (RA_free) on
  Ledrappier rows) fails for every group `F` (`algebraic-t1-needs-an-infinite-minimal-subset-of-ledrappier`).
- **Sub-SFTs.** Every nonempty sub-SFT of `X_L` has a periodic point, the refutation form conjectured in
  `free-minimal-triangle-permutive-sft-exists`.

## Evidence

- **For.**
  - `X_L` has no nonzero points of period `2^k Z^2`: `A/(s^(2^k) − 1, t^(2^k) − 1) = 0`, since `t − 1 = s` is a
    unit.
  - Toeplitz rows with 2-power periods force `0` into the orbit closure. Row `2^k` is `r + σ^(2^k) r`, which
    vanishes off the level-`k` holes of `r`; these have density tending to 0, so they leave ever larger zero
    boxes.
  - Regular almost automorphic infinite minimal subsets cannot lie over rotations whose doubling orbit returns
    near `0`, by the Frobenius lemma, item 4 of the reduction node.
  - Exhaustive small-window searches find only periodic sub-SFTs.
  - Kari–Moutot: low-complexity configurations of `X_L` are periodic.
- **Against.**
  - Berend-type rigidity fails in characteristic 2 (Einsiedler 2004).
  - On the leaf `F_2((s))` the acting group `⟨s, 1+s⟩` is too thin for Furstenberg's non-lacunarity argument:
    its orbit closures in the principal units are copies of `Z_2`.
  - The known non-algebraic closed invariant sets are unions of Frobenius subgroups; they contain `0`, so they
    are not counterexamples.

## First tests

1. **Odd Toeplitz.** A Toeplitz point with odd periods `m_k` would need nonzero points of `X_L` vanishing on all
   but a few cosets of `m_k Z^2`. Such points exist only if the corresponding sums of the modules
   `u^c F_2[s^(±m_k), t^(±m_k)]` are proper in `A`. Decide this, starting with `m = 3`.
2. **Bounded-run rotations.** For a two-dimensional rotation `(a, b)` whose doubling orbit stays away from `0`,
   for example `a` and `b` with bounded runs in their binary expansions, does a measurable
   `f : T^d → F_2` with `f(z + b) = f(z) + f(z + a)` exist? This is the only almost automorphic door left
   open.
3. **Minimal self-joinings.** A T1 set needs, beyond (FL) failing, a minimal self-joining `J` of one infinite
   minimal `N ⊆ X_L` with `{a z_1 + b z_2 : (z_1, z_2) ∈ J} = c_0 N` for a Zariski-dense family of `(a, b)`.
   Show this is impossible even when (FL) fails.

## Lesson for general BH

The algebraic face of (RA_free) on Ledrappier rows is decided by a characteristic-2 Furstenberg question for
minimal sets. It needs no free group, no measures and no homogeneous dynamics: it is a question about three-dot
spacetimes.

## Attempts

- **bh-bq2 (2026-09-19): refuted.** `ledrappier-shift-has-infinite-toeplitz-minimal-subsets` builds an explicit
  non-periodic Toeplitz point of `X_L`, with period lattices `2^K{λ : λ_1 ≡ λ_2 mod 3}`:
  - `F_4`-twisted Sierpinski gaskets, `(1 + ζX_1 + ζ^2X_2)^(2^(k+1) − 1)`, are periodic points of the twisted rule;
  - they are shifted by a non-rational 2-adic integer and summed;
  - the sum is untwisted by `Tr(· ζ^(v_1 − v_2))`.

  First test 1 is answered negatively: a point constant on one coset of an odd-index lattice is periodic, so odd
  Toeplitz points are periodic. The mixed 2-power × 3 structure succeeds. Consequence:
  killing algebraic T1 now requires the distal/non-almost-automorphic layers; see that node.
