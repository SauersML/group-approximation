# Harnack and Montel bounds on log a_(n,R), then the identity theorem carries lambda=rho around p_c

*Attempt artifact (2026-09-17), formerly route `fpbs-zero-free-connectivity-gives-flat-rate-proof` into `fpbs-zero-free-connectivity-gives-flat-rate`, requires [`fpbs-integrated-pivotal-rate-identity`]. Demoted from the graph at salvage: the worker lane (swarm-0917 b-t-pivot) was cut off before any referee pass, so the proof is unrefereed. No mathematical error has been reported. Restore it as a route once a full referee pass survives.*

Complete written proof in Section 2 of the artifact. No computation is used.
The required node supplies `lambda(p_c)=rho` (Schramm's lemma), hence
`lambda=rho` on `(0,p_c]` by monotonicity.

1. **Real lower bound.** Opening the walk path gives `a_(n,R)(w) >= w^n` for
   real `w` in `(0,1)` and `R>=n`.
2. **Uniform local bounds.** By (Z), `F_(n,R)=log a_(n,R)` is analytic on
   `U`. `M - n^(-1) log|a_(n,R)|` is nonnegative harmonic by (G) and bounded
   at a real base point by step 1, so Harnack bounds it on compacts.
   Borel–Carathéodory, with `Im F_(n,R)=0` at the base point, bounds
   `F_(n,R)/n` on compacts, uniformly in `(n,R)`. Montel gives normality.
3. **R to infinity.** Limits agree with `n^(-1) log a_n` on `I_-`, so by the
   identity theorem `F_(n,R)/n -> g_n` locally uniformly.
4. **n to infinity.** Any limit `g` equals `log rho` on `I_-`, hence on `U`.
   On `I_+`, `log lambda = lim Re g_n = log rho`. This is (a).
5. **Nonuniqueness.** By (a), `a_n(p) -> 0` on `I_+`. Uniqueness with
   `theta(p)>0` gives `tau_p >= theta(p)^2` by Harris–FKG, a contradiction.
   By Newman–Schulman there are infinitely many infinite clusters. This is (b).
6. **Budget.** Cauchy estimates give `|F'_(n,R)| <= B_K n / r` on `J`, and the
   finite Russo identity `p F'_(n,R)(p)=E_p[N_(n,R)|E_(n,R)]` gives (c).
