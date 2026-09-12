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
   field. This proves part (a).

**Part (b).** Let `x in R` with `R/xR` finite and `∩_k x^k R = 0`.

1. **`x` is a nonzero nonunit.** If `x` were a unit, then `∩_k x^k R = R != 0`. If
   `x = 0`, then `R/xR = R` would be infinite, since `R` contains `Z`.
2. **A height-one maximal ideal.** Let `Q` be a minimal prime over `xR`. By
   Krull's principal ideal theorem, `ht Q = 1`. `R/Q` is a quotient of the finite
   ring `R/xR`, so it is a finite field, of some characteristic `p`. Then
   `Q ∩ Z = pZ`, which has height one.
3. **The dimension formula at `Q`,** exactly as in step 5 of part (a):
   `1 = ht Q = 1 + trdeg_Q Frac(R) - trdeg_(F_p)(R/Q) = 1 + trdeg_Q Frac(R)`.
   So `trdeg_Q Frac(R) = 0`. QED
