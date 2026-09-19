
## CORRECTION (added the same day): the searched words could never produce a hit

Found while tabulating the near misses. Every generator `σ_2^j M σ_2^-j` with `M in GL_2(Z)` preserves the
content `c(w)`, the positive generator of `Z w_1 + Z w_2`. The reason: `c(σ_2 w) = σ(c(w))` and
`c(M w) = c(w)`. So every searched word lies in the content-preserving subgroup `C`.
- **Test 1 is vacuous.** Suppose `V_1 = L V_2` with `V_1, V_2 in C`. Then `L in C` is linear. A linear map
  preserving content sends primitive vectors to primitive vectors, so it lies in `GL_2(Z)` and
  `|det L| = 1`. If `p` divides `det L`, some primitive `w` has `L w in p Z^2`.
- **Test 2 is vacuous.** Suppose `V = L r V'` with `V, V' in C`. Then `L r in C`. That forces `L` to be
  integral with primitive columns. But `r(1,1) = (168,-10)` has content 2, so `L r(1,1)` has content at
  least 2.
- **So "0 hits" is a theorem, not evidence.** The runs above say nothing about whether `r in N`. The
  calibration found hits only because it added `e`, which is not in `C`.
- **The correct search space.** `N = <σ_2^j SL_2(Q) σ_2^-j, D : j in Z>` (Attempt 5 of the node). Its
  generators include `σ_2^j x_12(q) σ_2^-j` for rational `q`, which do not preserve content. A meaningful
  search must use them, for example `q in {±1/2, ±2, ±1/3, ±3}`. That is not run here.
- **Tabulation (run `tab`, 55 s).** On the extra lines `(1,1)`, `(1,2)`, `(2,1)`, `(1,3)`, `(3,1)`, `(2,3)`,
  `(1,-2)`, all 185 near misses (length <= 5, `|j| <= 1`):
  - preserve content, with ratio exactly 1, as they must;
  - keep none of those lines.

  `r` keeps none of them either. It changes content by 2 on `(1,1)` and `(1,3)`, and by 1 on the other five.
