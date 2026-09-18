---
rg: 2
id: slit-origami-z2-pair-needs-logarithmic-rank-to-commute
kind: claim
title: Unitary bounded-rank stability of Z^2 fails at commutator rank two; the slit origami needs rank at least ln(L/2+1)/256 to commute
distinct_from:
  deligne-cover-bounded-rank-sector-tuples-have-bounded-dimension: that is the bounded-rank rung for Deligne sector tuples, whose proof attempt asked for a dimension-free C(k) for commuting pairs; this refutes that dimension-free input for Z^2 itself and pins its correct form at C(k) log d.
  heisenberg-irrational-center-has-rank-one-sector-tuples: that refutes the rung for the Heisenberg group through an interval truncation with boundary two; this is a genus-two flat surface with a monodromy defect, for the abelian relator system, where no exact obstruction such as a determinant is available.
  almost-commuting-permutations-are-near-commuting: that is normalized Hamming stability of Z^k in permutations; this is unnormalized rank and Hilbert--Schmidt distance to commuting unitary pairs, where the normalized statement gives no bound.
artifacts:
  - research/slit-origami-z2-pair-needs-logarithmic-rank-to-commute-proof.md
  - experiments/slit-origami-rank-2026-09-17/check_slit_origami.py
  - experiments/slit-origami-rank-2026-09-17/check_slit_origami.out
---

**ESTABLISHED (unreviewed)** (`slit-origami-z2-pair-needs-logarithmic-rank-to-commute-proof`).
This answers bus need `e4b93e48` from sw-124 in the negative.

**Setting.** Fix `L >= 2` and put `s = floor(L/2)`, `rho = floor(L/2)`. The squares are
`(i, x, y)` with `i` in `{0,1}` and `x, y` in `Z/L`, so `n = 2L^2`. The **slit origami** is the
pair of permutations

```text
sigma(i,x,y) = (i, x+1, y),
tau(i,x,y)   = (1-i, x, 1)   if y = 0 and 0 <= x < s,
             = (i, x, y+1)   otherwise.
```

It is two `L x L` tori glued crosswise along a horizontal slit of length `s`. Let `b, c` in `U(n)`
be the permutation matrices of `sigma` and `tau`.

**Theorem.**

1. **Defect.** `rank(bcb^(-1)c^(-1) - I) = rank(bc - cb) = 2`.
2. **Hilbert--Schmidt lower bound.** Let `m >= 0`, let `beta, gamma` be in `U(m)`, and let
   `b', c'` be commuting unitaries on `C^n (+) C^m`. Then
   ```text
   ||b' - b (+) beta||_HS^2 + ||c' - c (+) gamma||_HS^2  >=  ln(rho + 1) / 64.
   ```
3. **Rank lower bound.** In the same situation,
   `rank(b' - b (+) beta) + rank(c' - c (+) gamma) >= ln(rho + 1) / 256`.
4. **The Hilbert--Schmidt bound is sharp in order.** There are commuting unitaries `b', c'` on
   `C^n` with `||b' - b||_HS^2 + ||c' - c||_HS^2 = O(log L)`. They come from a dipole flat
   connection. The script prints the value `3.34 ln L` at `L = 512`.

**Consequences.**

- **No dimension-free `C(k)`.** There is no function `C` with the following property: whenever
  `rank(bcb^(-1)c^(-1) - I) <= k`, there are commuting unitaries within rank `C(k)`. Take `k = 2`
  and let `L -> infinity`. This holds even allowing enlarged dimension and arbitrary padding.
  - `k = 2` is the first possible value. If `rank(U - I) <= 1` for the unitary `U = bcb^(-1)c^(-1)`,
    then `U = I + uv^*` with `det U = 1 + v^*u = 1`. So `(U - I)^2 = 0`, and a unipotent unitary is `I`.
- **The loss is logarithmic, and that is the target to aim at.** Any stabilizing function must be
  `>= c log n` at `k = 2`. A bound of the form `C(k) log d` is not refuted. It would still serve the
  joint-spectrum step of the Deligne rung, because (LOC) is linear in `d`. Then
  `d <= (1+A_g)k + N_g C(k) log d` gives `d = O_g(C(k) log C(k))`.
- **Normalized HS rate of Z^2 is not linear.** The pair has normalized commutator defect
  `eps = ||bc - cb||_2 = sqrt(8/n) = 2/L`. Its normalized distance to commuting pairs is
  `>= sqrt(ln(rho+1)/(64 n))`. So any modulus `delta(eps)` for HS stability of `Z^2` satisfies
  `delta(eps) >= c eps sqrt(log(1/eps))` along this family. We have not checked whether this is in
  the literature.

**Mechanism.** The flat surface has genus two. Around one slit endpoint, every ring of squares
at distance `r` carries a loop word `w_r` with zero exponent sums. It lifts to a path that
swaps the sheets. So `w_r(b,c) != I` on every basis vector of the ring, while `w_r(b',c') = I`.
- Telescoping `w_r(b',c') - w_r(b,c)` charges the error of each letter to one square of the ring.
  So the per-square perturbation mass `F` has ring sum `>= 1/sqrt 2`.
- Cauchy--Schwarz on the `8r - 4` squares of the ring gives ring energy `>= 1/(16 r)`.
- The rings are disjoint, so the harmonic sum gives `ln(rho+1)/16`. This is the extremal length
  of the annulus. It is the discrete form of the `log`-divergent energy of a vortex.
- A rank-`D` perturbation carries energy at most `4D`. Its mass may be spread over all
  coordinates, which is why a local cutting argument does not apply and the extremal-length
  count is needed.

**What this kills.** It kills any argument that forms joint spectra of commuting pairs inside rank-`k`
tuples by first rounding the pair to an exactly commuting one at rank cost independent of the
dimension. Such an argument must pay `log d`. It must also use that the defect of the pair sits in a
tuple with further relations. The slit origami has no such relations.
