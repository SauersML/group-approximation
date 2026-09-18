---
rg: 2
id: twisted-integral-affine-full-group-is-finitely-presented
kind: claim
title: The twisted integral-affine Brin-Thompson group W on Z_2^D is finitely presented and simple, and contains every GL_n(Z)
distinct_from:
  one-fp-simple-group-contains-every-brin-thompson-subgroup: that is DV_F, where only prefix replacements and coordinate permutations are allowed; this adds integral linear maps on finitely many coordinates, which DV_F is not known to contain.
  fp-self-similar-groups-embed-in-fp-simple-groups: that is Zaremsky's theorem for one self-similar group on one tree; this contains every GL_n(Z) at once, over infinitely many coordinates twisted by F.
---

**ESTABLISHED** (lane proof, not reviewed; **load-bearing, referee review requested**).
- Finite presentation: route `twisted-integral-affine-group-fp-via-stein-complex`, a
  step-by-step transfer of Belk–Zaremsky arXiv:2001.04579 §§5–7 and Zaremsky
  arXiv:2405.18354 §§3–4.
- Simplicity: `twisted-integral-affine-brin-thompson-group-is-simple`.
- No priority claimed; no literature search for this specific group was done beyond the
  sources above.

**The group.** Identify `C^D` with `X = Z_2^D` (binary digits), where `D` is the dyadic
rationals in `(0,1)` and `F` is Thompson's group acting on `D`. Let `W` be the group of
homeomorphisms `h` of `X` with a finite partition into pieces `P_i` such that on `P_i`:
- each `P_i` is a coset of an open subgroup of `Z_2^{T_i}` (finite `T_i ⊆ D`), defined by
  integral congruences, times the other coordinates;
- `h` permutes coordinates by some `f_i ∈ F`;
- on the coordinates in `T_i`, `h` is affine `x ↦ M_i x + b_i` with `M_i ∈ GL_{T_i}(Z[1/2])`
  and `b_i ∈ Z[1/2]^{T_i}`.

**Claim.** `W` is finitely presented and simple.

**What it contains.**
- `DV_F` (`one-fp-simple-group-contains-every-brin-thompson-subgroup`), hence every nV,
  every virtually special group, `Q` and `BS(1,3)`.
- The structure group `Γ_X = (Z^(D) ⋊ GL(Z; D)) ⋊ F`, and in particular
  `E(Z; D) ⋊ F ⊇ Σ = E(Z) ⋊ Z ⊇ GL_n(Z)` for every `n`
  (`finitary-steinberg-extensions-by-oligomorphic-actions-are-fp`,
  `elementary-shift-group-contains-every-integral-linear-group`).
- The odometer `τ × id` together with `2V`, hence `2V_τ ⊇ BS(1,2)`
  (`odometer-2v-is-fp-simple-and-contains-bs12`).

**Consequence.** `W` is one finitely presented simple group containing every finitely
generated subgroup of every `GL_n(Z)`: every polycyclic, finitely generated nilpotent, finite
and finitely generated virtually special group, `SL_n(Z)` for every `n`, and every `GL_n(O_K)`.
Route: `integral-linear-one-host-via-twisted-integral-affine-full-group`.

**Where the proof could fail** (for referees).
- Step 1 of the route: forest partitions and their common refinements, for non-box cosets.
- Step 7 of the route: the F_2-linear replacement for BZ22 Lemma 7.6, in particular the
  "full" dichotomy and the homotopy equivalence of the nerve.
- The two classical inputs in `integral-affine-halving-stabilizers-are-finitely-generated`
  (Bass–Milnor–Serre, and relative elementary generation for `n ≥ 3`).
- Generation by small-support elements in the simplicity proof.
## Attempts

1. **2026-09-18 (lane bh-universal): the index obstruction is not an obstruction for `W`.**
   `integral-affine-splitting-types-have-finitely-many-tuple-orbits`: the global affine
   group `Γ_X` has finitely many orbits on ordered `k`-tuples of halving directions,
   because halvings only see `X/2X = F_2^D`.
   - The proposed proof shape is a Stein–Farley complex of expansions of `X` by
     halvings, as for `nV`, `SV_G` and Röver–Nekrashevych groups. Here the vertex
     stabilizers are built from `Γ_X`, which is finitely presented by the method of
     `finitary-steinberg-extensions-by-oligomorphic-actions-are-fp` (add translations).
   - The pair-orbit count is the one the twisted criterion uses.
   - **Still missing:**
     - finite generation of the stabilizers of halving pairs;
     - simple connectivity of descending links, where halvings of different directions
       may cross (unlike coordinate halvings, two directions `φ ≠ ψ` need not commute
       as partitions of a piece);
     - the Morse bookkeeping itself.
   Not attempted beyond this reduction.
2. **2026-09-18 (lane bh-universal): settled, as a lane proof.** The missing items of attempt 1
   are closed.
   - Stabilizer finite generation: `integral-affine-halving-stabilizers-are-finitely-generated`.
   - Descending links: the crossing of halvings is harmless. BZ22's analysis only uses the
     lattice of partitions, and the one new point is the F_2-linear nerve,
     `non-spanning-subsets-of-an-f2-space-are-highly-connected`.
   - Morse bookkeeping: verbatim from Zaremsky 2405.18354 §4.
   - Simplicity was upgraded from the derived subgroup to `W` itself.
