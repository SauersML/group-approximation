---
rg: 2
id: schur-kernel-winding-invisibility-proof
kind: route
title: Solve the equation exactly in U(d), then read the winding off a cancelling commutator expansion
target: schur-kernels-are-invisible-to-matricial-windings
requires:
  - nonsingular-adjunction-never-enlarges-schur-multiplier
  - nonsingular-equations-preserve-matrix-certificates
---

Notation as in the target claim. Norms are operator norms, and `log` is the
principal logarithm on `Omega_d = {U in U(d) : ||U - I|| < 2}`. On `Omega_d`
no eigenvalue is `-1`, so `U -> log U` is continuous, `exp(Tr log U) = det U`,
`log(g U g^{-1}) = g (log U) g^{-1}` and `log(U^{-1}) = -log U`. For
`V in U(d)` write `V = exp(i H)` with `H = -i log V`; then
`||H|| = 2 arcsin(||V - I|| / 2) <= (pi/2) ||V - I||`.

## Lemma 1 (log additivity along short products)

Let `V_1, ..., V_M in U(d)` with `||V_j - I|| <= eta` and `(pi/2) M eta < 2`.
Then `V_1 ... V_M in Omega_d` and

    Tr log(V_1 ... V_M) = sum_j Tr log V_j.

*Proof.* Write `V_j = exp(i H_j)` as above and put
`P(s) = prod_j exp(i s H_j)` for `s in [0,1]`. Since
`||exp(i s H) - I|| <= s ||H||`, subadditivity of `||AB - I||` gives
`||P(s) - I|| <= sum_j ||H_j|| <= (pi/2) M eta < 2`, so `P(s) in Omega_d`.
The two functions `a(s) = Tr log P(s)` and `b(s) = i s sum_j Tr H_j` are
continuous and satisfy `exp a(s) = det P(s) = exp b(s)`. Their difference is
continuous with values in `2 pi i Z`, and it vanishes at `s = 0`. Hence
`a(1) = b(1) = sum_j Tr log V_j`. ∎

**Relator expressions.** An *expression* of `u in F'` over a relator set `Q`
is a factorization `u = prod_{j=1}^M g_j q_j^{eps_j} g_j^{-1}` with `q_j in Q`
and `eps_j = ±1`. We call `M` its length. Since
`||rho(g q^eps g^{-1}) - I|| = ||rho(q) - I||`, Lemma 1 and the conjugation
rules give:

**Corollary 2.** If `u` has an expression of length `M` over `Q` and
`(pi/2) M max_{q in Q} ||rho(q) - I|| < 2`, then `rho(u) in Omega_d` and

    Tr log rho(u) = sum_j eps_j Tr log rho(q_j).

**Cancelling expressions.** For `f in F'` and `u` with an expression
`u = prod_{l=1}^m k_l q_l^{eps_l} k_l^{-1}`, both `[f, u] = (f u f^{-1}) u^{-1}`
and `[f, u]^{-1} = u (f u^{-1} f^{-1})` have expressions of length `2m`. In
each, `(f k_l) q_l^{eps_l} (f k_l)^{-1}` or `k_l q_l^{eps_l} k_l^{-1}` occurs
once, together with a conjugate of `q_l^{-eps_l}`. So
`sum_j eps_j Tr log rho(q_j) = 0` over such an expression, for every `rho`.

## Step 1 (the Schur kernel is a product of relator commutators)

Put `F' = F * <t>`, let `R_Y` be the normal closure of `R_0` in `F'`, and fix
a lift `w~ in F'` of `w`. Inclusion `F -> F'` identifies
`H_2(Gamma) = (R cap [F,F])/[F,R]` with the Hopf description of
`H_2(Gamma * <t>) = (R_Y cap [F',F'])/[F', R_Y]`. By
`nonsingular-adjunction-never-enlarges-schur-multiplier`, `x in K_2(Gamma, w)`
gives

    h in [F', R_Y] . [F', <<w~>>_{F'}].

Choose once and for all a factorization
`h = prod_{i=1}^p [f_i, u_i]^{eta_i}` with `eta_i = ±1`. Each `u_i` lies in
`R_Y` or in `<<w~>>`, and has an expression of length `m_i` over
`R_0 cup {w~}`. By the cancelling-expression rule, `h` has an expression of
length `M = 2 sum_i m_i` over `Q = P cup {w~}`. Here `P subset R_0` is the
finite set of relators that occur, and the signed contributions of each
relator cancel. Put `delta = 4 / (pi M)`. Both `P` and `delta` depend only
on `h`, `w~` and the chosen factorization, and not on `d`.

## Step 2 (exact root in U(d))

Let `rho : S -> U(d)` satisfy `delta_P(rho) < delta`. By
`nonsingular-equations-preserve-matrix-certificates`, the unitary word map
of `w~` in `t` is onto `U(d)`. So there is `T in U(d)` with `rho(w~) = I`
once `rho(t) = T`. The extension leaves `rho(h)` unchanged, since `h in F`
has no `t`-letters. Now `max_{q in Q} ||rho(q) - I|| < delta`, so
`(pi/2) M max_Q ||rho(q) - I|| < 2`. Corollary 2, applied to the expression
from Step 1, gives `rho(h) in Omega_d` and

    2 pi i kappa(rho, h) = Tr log rho(h) = sum_j eps_j Tr log rho(q_j) = 0.

This proves the Theorem. ∎

## Step 3 (class-level form)

*Additivity.* Let `h, h'` be Hopf words with expressions over `R_0` of
lengths `M, M'`, and let `P` contain their relators. If
`(pi/2)(M + M') delta_P(rho) < 2`, Corollary 2 applies to `h`, to `h'` and
to the concatenated expression of `h h'`. So
`kappa(rho, h h') = kappa(rho, h) + kappa(rho, h')`. Likewise,
`kappa(rho, h^{-1}) = -kappa(rho, h)`.

*Boundaries.* Let `c in [F, R]`, written as a product of commutators
`[f, u]^{±1}` with `u in R`. It has a cancelling expression, so
`kappa(rho, c) = 0` once `delta_P(rho)` is below the corresponding threshold.

Along an asymptotic homomorphism every finite threshold is eventually met.
Hence:

- two Hopf words for one class give the same `kappa(rho_n, -)` for large
  `n`, since `h' = h c` with `c in [F, R]`;
- `Rig(Gamma)` is a subgroup;
- if `N x = 0`, then `h^N in [F, R]`, so
  `N kappa(rho_n, h) = kappa(rho_n, h^N) = 0` eventually, and torsion is
  rigid;
- `kappa(rho_n, h^m) = m kappa(rho_n, h)` gives the divisor property.

By the Theorem, `K_2(Gamma, w) <= Rig(Gamma)`.

*Matricial stability.* Suppose `pi_n : Gamma -> U(d_n)` are homomorphisms
with `||rho_n(s) - pi_n(s)|| -> 0` for `s in S`. Put
`rho_n^u(s) = pi_n(s) exp(u log(pi_n(s)^{-1} rho_n(s)))` for `u in [0,1]`.
Then `||rho_n^u(h) - I|| <= |h| (pi/2) max_{s in h} ||rho_n(s) - pi_n(s)||`,
which is `< 2` uniformly in `u` for large `n`. So `u -> kappa(rho_n^u, h)` is
continuous and integer-valued, hence constant. At `u = 0` we have
`pi_n(h) = I`, so the constant is `0`. Therefore `Rig(Gamma) = H_2(Gamma; Z)`
for matricially stable `Gamma`.
