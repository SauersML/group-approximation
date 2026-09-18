---
rg: 2
id: thompson-f-norm-bound-from-epg-32-term-moments-proof
kind: route
title: A rational vector with negative 16x16 localizing form theta*H - H_shift on 32 moments
target: thompson-f-norm-bound-from-epg-32-term-moments
requires: []
artifacts:
  - experiments/thompson-f-cogrowth-2026-09-17/epg_certify.py
  - experiments/thompson-f-cogrowth-2026-09-17/epg_certify.json
  - experiments/thompson-f-cogrowth-2026-09-17/trend_analysis.py
  - experiments/thompson-f-cogrowth-2026-09-17/trend_analysis.json
  - experiments/thompson-f/out15.json
  - experiments/thompson-f/hhr_certify.json
---

1. **Measure.** `mu_2` is the spectral measure of `P^2` at `delta_e`: a probability measure on
   `[0, ||P||^2]` with moments `M_j = <P^{2j} delta_e, delta_e> = c_j/16^j`. Here `c_j` is the number
   of trivial words of length `2j`, since `P^{2j} = 16^{-j} (sum of the 4^{2j} words)`.
   Moreover `sup supp mu_2 <= ||P^2|| = ||P||^2`.

2. **Moments.** `c_0..c_31` come from Elvey Price–Guttmann, arXiv:1706.07571, abstract l.42: "We
   have also given an improved algorithm for the coefficients of Thompson's group $F,$ giving 32
   terms of the cogrowth series", with the table at `Group-growth23-6.tex` l.296–333.
   `epg_certify.py` embeds the list and re-parses the TeX; the result is equal (JSON field
   `tex_parse_matches_embedded`).

   Independent agreement:
   - rows `0..15` equal `experiments/thompson-f/out15.json`, computed in this repository by exact
     PL-map arithmetic;
   - rows `16..24` equal the HHR arXiv:1409.1486 Case 2 table.

3. **Localizing form.** For rational `theta` put `A(theta)_{ij} = theta M_{i+j} - M_{i+j+1}` for
   `0 <= i,j <= 15`, which uses `M_0..M_31`. For `q(x) = sum_i v_i x^i`,

       v^T A(theta) v = int q(x)^2 (theta - x) dmu_2(x).

   If `mu_2` were supported in `[0, theta]`, the integrand would be `>= 0` everywhere.

4. **Certificate.** `epg_certify.py`:
   - finds `theta = 41466679/50000000` by bisection with exact `Fraction` LDL^T factorization;
   - extracts the vector `v` with `v^T A v = d_15 <= 0`;
   - scales `v` to an integer vector (printed in `epg_certify.json`, `N31_epg_full[0]`);
   - re-evaluates the quadratic form directly and asserts it is `< 0`.

   Hence `mu_2((theta, infinity)) > 0`, so `||P||^2 >= sup supp mu_2 > theta`.

5. **Bound.** `r = 910677/1000000` satisfies `r^2 <= theta` (asserted), so `||P|| > 0.910677`, and
   `mu = 16 ||P||^2 > 13.26933728`. The shifted form (`s = 1`, `x q^2 (theta - x)`, 15×15) gives
   the weaker `909579/1000000`. On `c_0..c_24` the script reproduces the graph's earlier HHR
   certificates `449939/500000` and `225383/250000` exactly.

6. **Density corollary (elementary Cheeger–Mohar).** Let `Gamma` be the Cayley graph. It is
   4-regular without loops or multi-edges, and bipartite, because trivial words have even length
   (abelianization `Z^2`). So `rho = ||A|| = 4||P||` equals `sup <Af,f>/<f,f>` over finitely
   supported `f`. Put `h = inf |dS|/|S|` over finite `S`, counting boundary edges.

   Take finitely supported `f`, sum over undirected edges, and put `g = f^2`.
   - Coarea: `sum |g(x)-g(y)| = int_0^inf |d{g>t}| dt >= h sum g`.
   - Cauchy–Schwarz: `sum |f(x)^2 - f(y)^2| <= (sum (f(x)-f(y))^2)^{1/2} (sum (f(x)+f(y))^2)^{1/2}
     = ((4||f||^2 - <Af,f>)(4||f||^2 + <Af,f>))^{1/2}`.

   So `h <= sqrt(16 - (<Af,f>/||f||^2)^2)`, and hence `h <= sqrt(16 - rho^2) = 4 sqrt(1-||P||^2)`.
   The average inner degree of `S` is `4 - |dS|/|S|`, so its supremum is `4 - h`, which is
   `>= 4 - 4 sqrt(1 - r^2)`. `trend_analysis.py` computes a rational upper bound for the square root
   and reports `2.347523...`.
