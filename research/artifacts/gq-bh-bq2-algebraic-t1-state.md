# bh-bq2 state: algebraic T1 on Ledrappier rows after (FL) (2026-09-19)

This is a consolidated handoff for a fresh relaunch. Lane bh-bq2 landed every node below with gqland.sh.
**Setting**:
- `X_L` is Ledrappier's shift; `A = F_2[s^(±1), (1+s)^(-1)]`.
- `X = X_L^2`, with `F ≤ GL_2(A)` free and `Γ = F × Z^2`.
- **T1** asks for an infinite, closed, `Z^2`-minimal, `F`-invariant `M ⊆ X` carrying an `F`-fixed invariant
  measure. It is the algebraic face of (RA_free); see `algebraic-rows-carry-rigid-free-commutants-but-never-minimality`.

## Established results

| node | content | status |
|---|---|---|
| `char-2-benoist-quint-needs-the-homogeneous-form` (dbd5f105f8) | the one-coset (BQ_2) is false (period-3 orbits; a four-subgroup Frobenius measure); (BQ_2') is the correct form; under (NS), (BQ_2') ⟺ infinite-support ergodic measures have infinite translation stabilizers; (BQ_2') still rules out T1 | refereed PASS (87fb554fa7) |
| `algebraic-t1-sets-carry-free-distal-commutator-actions` (dbd5f105f8) | char 2: `F ∩ SL_2(A)` acts freely and uniformly distally on `M`; `[F,F]` acts freely inside every fibre over the maximal equicontinuous factor (MEF); `M` is not a proximal extension of its MEF; module form of T1 | refereed PASS (d6b432dada) |
| `algebraic-t1-needs-an-infinite-minimal-subset-of-ledrappier` (e85f22f6f9) | row projections `N_w = π_w(M)` are infinite minimal subsets of `X_L`, constant on `F^T`-orbits; after an isogeny `M` becomes a minimal self-joining `J ⊆ N × N` with `{a_γ z_1 + b_γ z_2} = c_0 N` along an infinite `F`-orbit of `[a_γ : b_γ]` | refereed PASS (5ff06562e7) |
| `ledrappier-shift-has-infinite-toeplitz-minimal-subsets` (0d5291ca00) | **(FL) is false**: an explicit non-periodic Toeplitz point of `X_L` (twisted gaskets, a non-rational 2-adic shift, untwisted by `Tr(·ζ^(v_1−v_2))`); odd-index lattices are coset-rigid; 2-power Toeplitz points accumulate on 0; the period must mix 2 with some odd prime | refereed PASS (a7b6ad0f7b), no prior found |
| `ledrappier-shift-has-only-finite-minimal-subsets` | the (FL) crux, now marked REFUTED | — |

## New lemma (this artifact; lane proof, not reviewed)

**T1 needs a minimal subset of `X_L` that is not almost automorphic.** In the setting of the table, the minimal
set `N = N_w` of `X_L` is not almost automorphic. Moreover every fibre of `J` over its MEF is infinite.

*Proof.*
- **Joinings of almost automorphic systems are almost automorphic.** Let `N` be almost automorphic, with MEF
  `π_N : N → K_N` and residual set `G ⊆ K_N` of one-point fibres.
  - The image `K_J` of `J ⊆ N × N` in `K_N × K_N` is minimal and equicontinuous, a coset of a closed subgroup.
  - Its coordinate projections are open continuous surjections onto `K_N`, so the points of `K_J` with both
    coordinates in `G` form a residual set.
  - Over those points `J` has one-point fibres. So `J` is an almost 1-1 extension of `K_J`, hence of its own
    MEF.
- **Finite fibres upstairs.** `P : M → J` has finite kernel, so over the same residual set the fibres of `M`
  over `K_J` have at most `|ker P|` points. `K_J` is a factor of the MEF of `M`, so the fibres of `M` over its
  own MEF are finite there.
- **Contradiction.** By `algebraic-t1-sets-carry-free-distal-commutator-actions`, every such fibre contains an
  infinite free `[F,F]`-orbit.
- **The same argument for `J`.** A finite fibre of `J` over its MEF would give a finite fibre of `M`. ∎

## What remains

T1 on Ledrappier rows now needs, in order:
1. **An infinite minimal subset `N ⊆ X_L` that is not almost automorphic.** Its fibres over its MEF must be
   large enough that every fibre of some minimal self-joining `J ⊆ N × N` is infinite.
   - *Excluded so far:*
     - all Toeplitz, 2-adic, odd, mixed and other almost automorphic sets;
     - finite sums and joinings of almost automorphic sets, because factors and joinings of almost automorphic
       minimal systems stay almost automorphic.
   - *Candidates, all unchecked:*
     - weakly mixing minimal subsets (trivial MEF);
     - minimal subsets that are non-trivial distal extensions of a Toeplitz set inside `X_L`. Finite group
       extensions give finite fibres, which are excluded. Infinite ones would need compact-group cocycles
       realized linearly;
     - proximal-but-not-almost-1-1 constructions over odometers.
2. **The linear-equation self-joining.** `{a z_1 + b z_2 : (z_1, z_2) ∈ J} = c_0 N` must hold for an infinite
   `F`-orbit of `[a : b]`, which is Zariski dense.
3. **An `F`-fixed invariant measure,** for example unique ergodicity.

## Dead ends, with where they died

- **(FL) as a kill switch:** refuted (0d5291ca00).
- **The isometric-tower route:** subshifts are never distal, and nothing forces an isometric layer (e85f22f6f9,
  §"Why the isometric-tower route does not apply directly").
- **Lévy-measure and finite-orbit-limit constructions of non-Haar measures:** `X_L` has no nonzero homoclinic
  points, and generic finite orbits equidistribute.
- **Furstenberg's ×2 ×3 argument:** the acting group `⟨s, 1+s⟩` is too thin on the leaf `F_2((s))`.

## Suggested first tests for a relaunch

1. **Weak mixing.** Does `X_L` contain a weakly mixing infinite minimal subset? One route is a "random Toeplitz"
   construction that shifts twisted gaskets by independent non-rational 2-adic integers in different directions,
   destroying the common odometer.
2. **Infinite fibres by twisting.** Twist by characters of order 7, 15, … (`F_8`, `F_16`, …), where the
   Frobenius cancellation `ℓ^(2^k) = ℓ(1)` needs `1 + ζ + ζ^2 = 0`-type identities. Check whether the resulting
   Toeplitz sets can be combined into a non-almost-automorphic set with infinite fibres.
3. **The self-joining equations for the Toeplitz examples.** They cannot give T1, but the computation shows how
   `F` must act on rows.
