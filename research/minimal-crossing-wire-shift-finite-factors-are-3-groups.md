---
rg: 2
id: minimal-crossing-wire-shift-finite-factors-are-3-groups
kind: claim
title: Every finite factor of the minimal crossing-wire fixed-point shift (zooms N_k = 3^(C^k)) has 3-power order, so nZ^2 acts minimally on it whenever 3 does not divide n
distinct_from:
  minimal-crossing-wire-fixed-point-shift-is-quantum-rigid: that proves the shift minimal, free and rigid for Z^2; this bounds its rational spectrum, which decides minimality of finite-index subactions (used by Busemann transplants with a phase skeleton).
---

**ESTABLISHED (2026-09-18).** Lane proof (bh-g2-fixedpoint-a), elementary, not independently reviewed. The
same proof applies to the SW-deterministic layout and to any variant whose zooms are powers of 3. The full
maximal equicontinuous factor is **not** determined here: irrational eigenvalues are not excluded.

## Statement

Let `Ω` be the tiling shift of `minimal-crossing-wire-fixed-point-shift-is-quantum-rigid`, with zooms
`N_k = 3^(C^k)` and `L_k = N_1 ⋯ N_k`. Let `f : Ω → Z^2 / Λ` be a continuous equivariant map onto a finite
transitive `Z^2`-set. Then `[Z^2 : Λ]` is a power of 3. Consequently, for every `n` prime to 3, the subgroup
`nZ^2` acts minimally on `Ω`.

## Proof

1. **Locality.** `f` is locally constant, so there is `r` with `f(x)` determined by `x|_(B_r)`. Since `Z^2`
   is abelian and acts transitively on the target, `Λ` is the stabilizer of every value. So if
   `x|_(B_r) = (T^v x)|_(B_r)`, then `v ∈ Λ`.
2. **Blank level-`K` positions.** At every level the layout (wires, box, zone, slots) occupies `o(N_(K+1)^2)`
   of the positions of a rank-`(K+1)` macrotile. So some block `c` of `3 × 3` positions has role BLANK in
   every rank-`(K+1)` macrotile. A BLANK rank-`K` tile is determined by its coordinates and `K`, and so is
   its expansion to ground level.
3. **Return vectors.** Choose `K` with `L_K > 2r`. By minimality there is `x ∈ Ω` whose origin lies in the
   central rank-`K` macrotile of `c`, inside some rank-`(K+1)` macrotile. Then `B_r` lies inside the rank-`K`
   macrotiles of `c`. For `v ∈ L_(K+1) Z^2`, the macrotile of the same rank at offset `v` has the same blank
   block `c`, at the same coordinates, so `(T^v x)|_(B_r) = x|_(B_r)`. By step 1, `L_(K+1) Z^2 ⊆ Λ`, and
   `L_(K+1)` is a power of 3.
4. **Subactions.** For `n` prime to 3, the `nZ^2`-minimal subsets of the `Z^2`-minimal system `Ω` are
   finitely many clopen sets, permuted transitively by `Z^2`. They give a finite factor whose order divides
   `n^2` and, by step 3, is a power of 3. So there is only one such set, and `nZ^2` is minimal.

## Lesson for general BH

The hierarchy's zooms control which finite-index subactions stay minimal: blank regions at every level
make each level's grid the only source of finite factors. So transplants that need a phase skeleton of
modulus `n` should take `n` prime to the zoom primes. That is a free design choice.
