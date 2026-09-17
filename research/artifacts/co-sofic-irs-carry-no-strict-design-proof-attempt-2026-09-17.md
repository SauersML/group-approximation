# Count image patterns on a finite Schreier graph with forward-bad and reverse-bad sites and pass to the limit

*Attempt artifact (2026-09-17), formerly route `co-sofic-irs-carry-no-strict-design-proof` into `co-sofic-irs-carry-no-strict-design`, requires []. Demoted from the graph because referee lenses 1 and 2 returned *refuted* at the level of the statement: `r` names both the rank of `F_r` and `R_tau + R_sigma`, so `d_k` read literally counts balls in the `2(R_tau+R_sigma)`-regular tree and the stated constant is too small (counterexamples on `F_20` with `R_tau = 0`, `R_sigma = 1`). Both lenses found steps 1-5 sound once `d_k` is the ball size in the `2*rank`-regular tree. Restore it as a route once the statement uses a separate rank variable and a full referee pass survives.*

Source: `research/artifacts/irs-surjunctivity-heretic-2026-09-17.md`, Section 4.

Drafted direct proof: artifact Section 4. Take a finite `F_r`-set `X` with `|X| = N`, forward-bad
fraction `eps`, reverse-bad fraction `delta`, and forward-good set `G`.

1. **Lower bound.** `x|G = (sigma tau x)|G` is read from `tau x`, and `y -> (sigma y)|G` is onto
   `A^G`. So `|tau(A^X)| >= |A|^((1-eps)N)`.
2. **Excluded patterns.** Let `v` be reverse-bad with witness `p_v`, and suppose
   `B_(R_tau)(v) ⊆ G`. Then `y = tau x` has `sigma y = x` on `B_(R_tau)(v)`, so
   `tau sigma y(v) = y(v)` and `y|B_r(v) != p_v`. At most `eps N d_(R_tau)` reverse-bad vertices fail
   the hypothesis.
3. **Separation.** A greedy `2r`-separated subset `D'` has at least
   `(delta - eps d_(R_tau)) N / d_(2r)` elements, and its `r`-balls are disjoint. Hence
   `|tau(A^X)| <= |A|^N (1 - |A|^(-d_r))^|D'|`.
4. **Combine.** `ln(1-u) <= -u` gives `|D'| <= eps N |A|^(d_r) ln|A|`, and so
   `delta <= (d_(R_tau) + d_(2r)|A|^(d_r) ln|A|) eps`.
5. **Limit.** Forward-bad and reverse-bad are clopen shape events, so `eps_D` and `delta_D` are
   continuous and affine in `mu`. The inequality holds on the closed convex hull of the finite-set IRS,
   which contains every co-sofic IRS.
