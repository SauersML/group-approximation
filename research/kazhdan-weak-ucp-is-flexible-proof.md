---
rg: 2
id: kazhdan-weak-ucp-is-flexible-proof
kind: route
title: Average the Stinespring corner over a Kazhdan set to an invariant finite-rank projection of the same normalized rank
target: kazhdan-weak-ucp-stability-is-flexible-stability
requires: []
---

`(b) => (a)`: a finite-dimensional representation on `C^(D_n) supseteq
C^(d_n)` is a dilation; nothing to prove.

`(a) => (b)`.  Fix a Kazhdan pair `(S, kappa)` for `Gamma`, `S = S^(-1)`
finite generating.  Let `phi_n : Gamma -> U(d_n)` be a hyperlinear
approximation and `pi_n : Gamma -> U(H^_n)`, `P_n` the projection onto
`H_n = C^(d_n) subseteq H^_n`, with
`|| phi_n(g) - P_n pi_n(g) P_n ||_(2,d_n) -> 0` for all `g`, as `(a)`
provides.  `|| . ||_HS` is the unnormalized Hilbert--Schmidt norm.

**Step 1 (the corner almost commutes).**  For every `g`,
`|| P^perp pi(g) P ||_HS^2 = d_n - || P pi(g) P ||_HS^2` and
`|| P pi(g) P ||_HS >= || phi_n(g) ||_HS - o(sqrt d_n) = sqrt d_n - o(sqrt d_n)`,
so both off-diagonal blocks of `pi(g)` relative to `P` have `HS`-norm
`o(sqrt d_n)`:

```text
|| [pi_n(g), P_n] ||_HS = o(sqrt d_n)   for every g in Gamma.       (F1)
```

**Step 2 (Kazhdan averaging on `HS(H^_n)`).**  `Ad pi_n` is a unitary
representation of `Gamma` on the Hilbert space `HS(H^_n)`, and by `(F1)`
the unit vector `xi_n = P_n / sqrt d_n` is `(S, delta_n)`-invariant with
`delta_n := (1/kappa) max_(s in S) || Ad pi_n(s) xi_n - xi_n || -> 0`.  Let
`M = (1/2)(1 + |S|^(-1) sum_(s in S) Ad pi_n(s))` (lazy Markov operator).
Property (T) gives `spec(M) subseteq [0, 1 - kappa^2/(4|S|)]` on the orthogonal
complement of the `Ad pi_n(Gamma)`-invariant vectors, so `M^k xi_n`
converges in `HS` to the orthogonal projection `P_inv xi_n` of `xi_n` onto
the invariant vectors, and `|| xi_n - P_inv xi_n || <= delta_n`
(Bekka--de la Harpe--Valette Prop. 1.1.9).  Every `M^k` is a convex
combination of conjugations by unitaries, so it maps positive contractions
to positive contractions, and `HS`-limits of positive contractions are
positive contractions.  Hence

```text
Q_n := sqrt(d_n) P_inv xi_n  is a positive contraction in pi_n(Gamma)',
|| Q_n - P_n ||_HS <= delta_n sqrt d_n.                              (F2)
```

**Step 3 (spectral projection of the same normalized rank).**  With
`D = Q_n - P_n` (`|| D ||_op <= 2`, `|| D ||_HS <= delta_n sqrt d_n`) one
has `Q_n^2 - Q_n = PD + DP + D^2 - D`, so
`|| Q_n^2 - Q_n ||_HS <= 5 delta_n sqrt d_n`.  The pointwise inequality
`| 1_([1/2,infinity))(x) - x | <= 2 | x^2 - x |` (all real `x`) and the
functional calculus give, for `E_n := 1_([1/2, infinity))(Q_n)`,

```text
|| E_n - P_n ||_HS <= 11 delta_n sqrt d_n.                            (F3)
```

`E_n` is a spectral projection of the compact operator `Q_n` away from `0`,
hence of finite rank `d'_n`, and `E_n in pi_n(Gamma)'` as a function of
`Q_n`; for projections `|| E - P ||_HS^2 >= | rank E - rank P |`, so
`| d'_n - d_n | <= 121 delta_n^2 d_n` and `d'_n / d_n -> 1`.  Thus
`rho_n := pi_n|_(V_n)`, `V_n := ran E_n`, is a GENUINE finite-dimensional
unitary representation of `Gamma`, and for every `g`

```text
|| E_n pi_n(g) E_n - P_n pi_n(g) P_n ||_HS <= 22 delta_n sqrt d_n.     (F4)
```

**Step 4 (coordinates as in Def 1.2).**  Let `X = E_n P_n = W_n |X|` be the
polar decomposition, `|X| = (P E P)^(1/2)`; since `0 <= PEP <= P`,
`|| PEP - P ||_HS <= 11 delta_n sqrt d_n` and `0 <= 1 - sqrt y <= 1 - y` on
`[0,1]`, one gets `|| W_n - P_n ||_HS <= 22 delta_n sqrt d_n`, so
`W_n : H_n -> V_n` is a partial isometry with initial projection `q_n`,
`|| q_n - 1_(H_n) ||_(2,d_n) -> 0`.  Put

```text
C^(D_n) := V_n (+) (H_n (-) ran q_n),   D_n = d'_n + (d_n - rank q_n),
J_n : H_n -> C^(D_n),  J_n xi = W_n xi (+) (1 - q_n) xi   (an isometry),
pi'_n := rho_n (+) 1.                                                 (F5)
```

Then `D_n / d_n -> 1`, `pi'_n` is a genuine finite-dimensional unitary
representation of `Gamma`, and

```text
J_n^* pi'_n(g) J_n = W_n^* rho_n(g) W_n + (1 - q_n),
|| J_n^* pi'_n(g) J_n - phi_n(g) ||_(2,d_n)
   <= || W_n^* E_n pi_n(g) E_n W_n - P_n pi_n(g) P_n ||_(2,d_n)
      + || P_n pi_n(g) P_n - phi_n(g) ||_(2,d_n) + || 1 - q_n ||_(2,d_n) -> 0,
```

using `(F3)`, `(F4)`, `|| W_n - P_n ||_(2,d_n) -> 0` and the hypothesis.
After the unitary change of coordinates on `C^(D_n)` that carries `J_n` to
the inclusion of the first `d_n` coordinates, this is exactly `(WF1)`.
