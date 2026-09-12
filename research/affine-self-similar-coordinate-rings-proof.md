---
rg: 2
id: affine-self-similar-coordinate-rings-proof
kind: route
title: Section closure makes the maximal ideal principal in the localization, which forces transcendence degree zero
target: affine-self-similar-coordinate-rings-are-one-dimensional
requires: []
---

Let `v` be the normalized valuation of `O`, and `k = O/pi O` the finite residue
field, of characteristic `p`. Put `P = R ∩ pi O`.

1. **`P` is maximal.** `R/P` embeds in `k`, so it is a finite domain, hence a
   field.
2. **An element of valuation one.** `p` lies in `R` and in `pi O`, since `p = 0`
   in `k`. Let `e = v(p) >= 1`. Applying (SC) `e - 1` times to `p` gives
   `b = p/pi^(e-1) in R` with `v(b) = 1`. Applying (SC) once more gives
   `u = b/pi in R` with `v(u) = 0`, so `u` is not in `P`.
3. **`P R_P` is principal.** `u` is a unit of `R_P`, so `pi = b u^(-1) in R_P`,
   and `pi R_P <= P R_P`. Conversely, if `a in P` and `s in R \ P`, then (SC)
   gives `a/pi in R`, so `a/s = pi (a/pi) s^(-1) in pi R_P`. Hence
   `P R_P = pi R_P`, a nonzero principal maximal ideal.
4. **`R_P` is a DVR.** `R` is a finitely generated `Z`-algebra, so `R_P` is a
   noetherian local domain. Its maximal ideal is principal and nonzero, so by
   Krull's principal ideal theorem `dim R_P = 1`, and `R_P` is a discrete
   valuation ring. In particular `ht P = 1`.
5. **The dimension formula.** `Z` is universally catenary, `R` is a finitely
   generated `Z`-algebra domain, and `P ∩ Z = pZ` has height one. The equality
   case of the dimension formula (Matsumura, *Commutative Ring Theory*,
   Theorem 15.6) gives

   ```text
   ht P = ht(pZ) + trdeg_Q Frac(R) - trdeg_(F_p)(R/P) = 1 + trdeg_Q Frac(R) - 0.
   ```

   With `ht P = 1` from step 4, `trdeg_Q Frac(R) = 0`, so `Frac(R)` is a number
   field. QED
