---
rg: 2
id: fpbs-lattice-amenable-subgroup-critical-finiteness-no-gap-proof
kind: route
title: Sum the Fitzner--van der Hofstad critical asymptotics over the sublattice, and use Burton--Keane plus Harris above p_c
target: fpbs-lattice-amenable-subgroup-critical-finiteness-no-gap
requires:
  - fpbs-hp-relative-burton-keane
artifacts:
  - research/artifacts/fpbs-lattice-critical-relative-finiteness-2026-09-17.md
---

**Imported input (verbatim).** R. Fitzner and R. van der Hofstad,
arXiv:1506.07977, *Mean-field behavior for nearest-neighbor percolation in
d>10*, read from the arXiv HTML on 2026-09-17:

> Theorem 1.4 (Two-point function asymptotics). For nearest-neighbor
> percolation with $d\geq 11$, there exists a constant $A(d)$ such that, as
> $|x|\rightarrow\infty$,
> $\tau_{p_{c}}(x)=\frac{a_{d}A(d)}{|x|^{d-2}}(1+O(|x|^{-2/d}))$, with
> $a_{d}=\frac{d\Gamma(d/2-1)}{2\pi^{d/2}}$. (1.15)

Only the upper bound is used. It gives `R, C_0 < infinity` with
`tau_(p_c)(x) <= C_0 |x|^(-(d-2))` for `|x| >= R`, and `tau <= 1` always.

**Step 1 (fibre bound).** Fix `q in Z^m` and put `a = (d-2)/2`, so `2a - k = m - 2 >= 1`.
Split the sum over `h in Z^k` according to whether `|(h,q)| < R`. At most
`(2R+1)^k` terms have `|(h,q)| < R`, and each is at most 1. The other terms
contribute at most `C_0 sum_{h : |(h,q)| >= R} (|h|^2 + |q|^2)^(-a)`.

* If `|q| >= 1`, compare with the integral over unit cubes. For
  `y in h + [0,1)^k` we have `|y|^2 <= 2|h|^2 + 2k <= 2|h|^2 + 2k|q|^2`, so
  `|y|^2 + |q|^2 <= (2+2k)(|h|^2+|q|^2)`. Hence
  `(|h|^2+|q|^2)^(-a) <= (2+2k)^a int_{h+[0,1)^k} (|y|^2+|q|^2)^(-a) dy`,
  and the sum is at most `C_1 int_{R^k} (|y|^2+|q|^2)^(-a) dy` with
  `C_1 = C_0 (2+2k)^a`.
  Substituting `y = |q| z` gives
  `C_1 |q|^(k-2a) int_{R^k} (|z|^2+1)^(-a) dz`. The integral is finite because
  `2a > k`.
* If `q = 0`, the sum is at most `C_0 sum_{h != 0} |h|^(-2a)`, which is finite
  because `2a > k`.

Adding the terms gives `sigma_(p_c)(q) <= C (1+|q|)^(-(m-2))` (item 1).

**Step 2 (l^r).** `sum_{q in Z^m} (1+|q|)^(-r(m-2)) < infinity` if and only if
`r(m-2) > m`. For `m >= 5`, `2(m-2) = 2m - 4 > m`. This proves item 2.

**Step 3 (no gap).** Let `p > p_c(G)`, so `theta(p) = P_p(|K_0| = infinity) > 0`.
Apply `fpbs-hp-relative-burton-keane` with `Gamma = H' = Z^d`, which is amenable.
A cluster is `Z^d`-infinite exactly when it is infinite, so a.s. there is at most
one infinite cluster. Hence, for each `h in H`, the event
`{0 <-> infinity} ∩ {h <-> infinity}` is contained a.s. in `{0 <-> h}`. Both
events are increasing, so Harris--FKG gives

```text
tau_p(0,h) >= P_p(0 <-> infinity) P_p(h <-> infinity) = theta(p)^2 > 0.
```

`H` is infinite, so `chi^H_p = sum_{h in H} tau_p(0,h) = infinity` (item 3).

**Closedness.** `chi^H_p` is nondecreasing in `p`, by monotone coupling. With
items 1 and 3 this gives `{p : chi^H_p < infinity} = [0,p_c]` when `m >= 3`.
