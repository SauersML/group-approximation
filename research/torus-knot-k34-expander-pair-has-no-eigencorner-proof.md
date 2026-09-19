---
rg: 2
id: torus-knot-k34-expander-pair-has-no-eigencorner-proof
kind: route
title: An eigencorner of the phase commutes with the regular action, the Selberg gap flattens its diagonal, and the phase has vanishing trace
target: torus-knot-k34-expander-pair-has-no-eigencorner
requires: []
---

Notation is as in the target.  `tau` is the normalized trace of
`M_(k_p)`, `||·||_2` is the unnormalized Hilbert--Schmidt norm, and `rk` is
rank.  `L(g)` is the left-regular unitary of `g in G_p`, with
`L(g) e_h = e_(gh)`.  So `alpha_p = L(S)` and
`beta_p = L(B)`, and `D_p` is diagonal in the basis `(e_h)`.

## Imported: Selberg's theorem as a uniform Kazhdan constant

Imported with credit, not reproved.  A. Lubotzky, *Expander graphs in pure
and applied mathematics*, Bull. Amer. Math. Soc. 49 (2012), 113--162,
arXiv:1105.2389.  It was read from arXiv on 2026-09-19, and the quotations
are verbatim from the PDF text.  Matrices were flattened by the extraction,
so `(1±1 0 1)` is the matrix `[[1,±1],[0,1]]`.

Definition 1.9: "Let G be a group and Σ a subset of G. We say that ε′ > 0 is
a Kazhdan constant of G w.r.t. Σ if for every unitary representation ρ : G→
U(H), where H is a Hilbert space and U(H) the group of unitary operators,
without a non-zero ﬁxed vector, and for every 0 ≠ v ∈ H, there exists s ∈
Σ such that ‖ρ(s)v−v‖≥ ε′‖v‖."

Proposition 1.11 (ii): "For every k∈ N and every 0<ε ∈R, there exists
ε′ =f2(k,ε ), such that if G is a ﬁnite group with a symmetric set of k
generators Σ with ε(Cay(G; Σ))≥ε, ε′ =f2(k,ε ) is a Kazhdan constant for G
w.r.t. Σ."

Theorem 2.12 (Selberg): "For every m∈N, λ1(Γ(m)\H) ≥ 3/16."

Corollary 2.13: "For a ﬁxed set of generators Σ of Γ = SL2(Z), e.g., Σ
={(1±1 0 1), (1 0 ±1 1)}, the Cayley graphs Cay(SL2(Z/mZ); Σ) are all
ε-expanders for some ε> 0 which may depend on Σ but not on m."

**Consequence (K).**  Apply Corollary 2.13 to the symmetric generating set
`Sigma = {S, S^(-1), B, B^(-1)}` of `SL_2(Z)`.  It is a generating set by
step 0 below.  Then apply Proposition 1.11 (ii) with `k = 4`.  This gives
one `kappa > 0` with the following property.  For every prime `p`, every
unitary representation `rho` of `G_p = SL_2(Z/pZ)` without non-zero fixed
vectors, and every `v != 0`,

```text
max_{s in Sigma} ||rho(s) v - v|| >= kappa ||v||.
```

## Step 0: the group theory

In `SL_2(Z)` the following hold, checked by hand and by
`experiments/torus-knot-expander-eigencorner-2026-09-17/check.py`:
- `S^2 = -I`, so `S^4 = I`;
- `ST = [[0,-1],[1,1]]` and `(ST)^3 = -I`, so `B^3 = (ST)^6 = I`;
- `ST = (ST)^(-2) (ST)^3 = B^(-1) S^2`;
- `T = S^(-1)(ST)`.

So `<S, B> = <S, T> = SL_2(Z)`.  Reduction mod `p` is onto `G_p`, so
`Sigma` generates `G_p`, and `alpha_p^4 = L(S^4) = 1` and
`beta_p^3 = 1`.  The script also checks that `S` has order `4` and `B` has
order `3` in `G_p`, and that `Sigma` generates `G_p`, for
`5 <= p <= 31`.

## Step 1: the phase is Lipschitz and has vanishing trace

Write `R = R_p` and `phi = phi_p`.  For `s in Sigma` and `h in G_p` we
have `| |s h| - |h| | <= 1`.  So `|phi(s h) - phi(h)| <= pi / R`.
- `L(s) D L(s)^*` is the diagonal matrix with entries
  `exp(i phi(s^(-1) h) / 12)`.  Hence
  `||[D, L(s)]|| = ||D - L(s) D L(s)^*|| <= pi / (12 R)`.
- Moving `alpha` past `D^3` costs at most `3 ||[D, alpha]||`.  Collecting the
  four factors of `X^4 = D^3 alpha D^3 alpha D^3 alpha D^3 alpha` to the left
  costs at most `(3 + 6 + 9) ||[D, alpha]||`.  Since `alpha^4 = 1`, this
  gives `||X_p^4 - D_p^12|| <= 18 pi / (12 R) = 3 pi / (2 R)`.
- In the same way, `||Y_p^3 - D_p^12|| <= (4 + 8) pi / (12 R) = pi / R`.
- `R_p -> infinity`, because `k_p -> infinity`.  So in `Q`,
  `X^4 = Y^3 = u := [(D_p^12)]`.
- `D_p^12 = diag(exp(i phi))`, and `phi(e) = pi`.  So
  `||D_p^12 - 1|| = 2` for all `p`, and `||u - 1|| = 2`.

Let `w_p = |D_p^12 - 1|^2`.  It is diagonal, with `0 <= w_p <= 4`, and it
is supported on the ball of radius `R - 1` about `e`.  `Sigma` has four
elements, so that ball has at most `sum_(j < R) 4^j < 4^R <= k_p^(1/2)`
elements.  Hence

```text
tau(w_p) <= 4 k_p^(-1/2) -> 0.                                   (1)
```

## Step 2: an eigencorner commutes with the regular action

Suppose `P in {X, Y}' ∩ Q` is a nonzero projection, `lambda in C`, and
`u P = lambda P`.  Since `P != 0`, `u - lambda` is not invertible, so
`lambda in sp(u)`.  Also `|lambda| = 1`.
- **Spectral arc.**  `sp(D_p^12)` lies in the arc
  `A = {e^(i theta) : 0 <= theta <= pi}`, so `sp(u)` lies in `A` too.
- **A function carrying `u` to `D`.**  Define `g` on the circle by
  `g(e^(i theta)) = e^(i theta / 12)` for `0 <= theta <= pi`, and
  `g(e^(i theta)) = e^(i (2 pi - theta) / 12)` for `pi <= theta <= 2 pi`.
  It is continuous, and `g(D_p^12) = D_p` exactly.  Continuous functional
  calculus of normal elements commutes with the quotient map, so
  `g(u) = D := [(D_p)]`.
- **`D` acts on `P` by a scalar.**  From `u P = lambda P` we get
  `u^* P = conj(lambda) P`.  Taking adjoints gives `P u = lambda P`.  Hence
  `f(u) P = P f(u) = f(lambda) P` for every Laurent polynomial `f`, and by
  uniform approximation for every continuous `f` on the circle.  Put
  `mu = g(lambda)`.  Then `D^k P = P D^k = mu^k P` for all `k in Z`.
- **`P` commutes with `alpha` and `beta`.**  In `Q`, `X = D^3 alpha`, so
  `alpha = D^(-3) X` and
  `alpha P = D^(-3) X P = D^(-3) P X = D^(-3) P D^3 alpha = P alpha`,
  where the last step uses `D^(-3) P D^3 = mu^(-3) mu^3 P = P`.  In the same
  way `beta P = P beta`, using `Y = D^4 beta`.

**Lift.**  Lift `P` to projections `P_p in M_(k_p)`.  Then

```text
eta_p := max_{s in Sigma} ||[L(s), P_p]|| -> 0,
||(D_p^12 - lambda) P_p|| -> 0,
P_p != 0 for infinitely many p.
```

The first line uses `alpha^* = alpha^(-1)` and `beta^* = beta^(-1)`, which
also commute with `P`.  The second line holds because `D_p^12` lifts `u`.
The third holds because `||P|| = limsup ||P_p|| = 1`.

## Step 3: the spectral gap flattens the diagonal of an almost-invariant projection

Fix `p` and write `P = P_p`, `r = rk P >= 1`, `eta = eta_p`, `G = G_p`,
`k = k_p`.  The group `G` acts unitarily on the Hilbert space
`HS = (M_k, ||·||_2)` by `g · A = L(g) A L(g)^*`.  Let `E` be the
orthogonal projection onto the fixed vectors.  For a finite group it is the
average, `E(A) = |G|^(-1) sum_g L(g) A L(g)^*`.

1. **Almost invariance in `HS`.**  For `s in Sigma`,
   `s · P - P = [L(s), P] L(s)^*`.  Here `[L(s), P] = L(s) P - P L(s)` has
   rank at most `2r`, and `||A||_2 <= rk(A)^(1/2) ||A||` for every `A`.  So
   `||s · P - P||_2 <= (2r)^(1/2) eta`.
2. **Gap.**  The restriction of the action to `(1 - E) HS` is a unitary
   representation of `G` with no non-zero fixed vector.  So consequence (K)
   applies to `v = P - E(P)`.  Since `E` commutes with the action,
   `s · v - v = (1 - E)(s · P - P)`, and so
   `kappa ||P - E(P)||_2 <= max_s ||s · P - P||_2 <= (2r)^(1/2) eta`.
3. **The average has flat diagonal.**  For `h in G`,
   `E(P)_(hh) = |G|^(-1) sum_g P_(g^(-1) h, g^(-1) h) = tr(P) / k = r / k`.
   Also `0 <= E(P) <= 1`, being an average of projections, so
   `E(P)^2 <= E(P)`.

Now let `w = w_p` be the diagonal matrix of Step 1, with `0 <= w <= 4`.  Then
`tr(P w P) = ||w^(1/2) P||_2^2`, and

```text
||w^(1/2) E(P)||_2^2 = tr(w^(1/2) E(P)^2 w^(1/2)) <= tr(E(P) w)
                     = sum_h E(P)_(hh) w_h = r tau(w),
||w^(1/2) (P - E(P))||_2 <= 2 ||P - E(P)||_2 <= 2 (2r)^(1/2) eta / kappa.
```

By the triangle inequality, after dividing by `r^(1/2)`,

```text
( tr(P w P) / r )^(1/2)  <=  tau(w)^(1/2) + 2 sqrt(2) eta / kappa.      (2)
```

The bound (2) holds for every nonzero projection `P` in every `M_(k_p)`.
Its constant does not depend on `p` or on `r`.

## Step 4: contradiction

Run over the infinitely many `p` with `P_p != 0`.
- By Step 2, `||(D_p^12 - 1) P_p - (lambda - 1) P_p|| -> 0`.  Multiply by the
  adjoint.  This gives `||P_p w_p P_p - |lambda - 1|^2 P_p|| -> 0`.
- `P_p w_p P_p - |lambda - 1|^2 P_p` has rank at most `r_p`, and
  `|tr(A)| <= rk(A) ||A||`.  Hence
  `tr(P_p w_p P_p) / r_p -> |lambda - 1|^2`.
- On the other hand the right side of (2) tends to `0`, by (1),
  `eta_p -> 0` and `kappa > 0`.

So `|lambda - 1| = 0`.  That is, every eigencorner of `u` in
`{X, Y}' ∩ Q` has eigenvalue `1`, which is the claim.  ∎

## Remarks

- **What the proof uses.**  It uses only three things: `D` is a continuous
  function of `u`; the regular action has a uniform Kazhdan constant; and
  `tau(|u - 1|^2) -> 0`.  It uses nothing about `X` and `Y` beyond
  `X = D^3 alpha` and `Y = D^4 beta`.
- **Approximate corners die too.**  Suppose `q in {X, Y}' ∩ Q` is a nonzero
  projection with `||(u - lambda) q|| <= epsilon`.
  - `g^k` is `|k|/12`-Lipschitz on the circle.  For normal `u`, the spectral
    measure of each vector then gives `||(D^k - mu^k) q|| <= |k| epsilon / 12`.
  - `||N xi|| = ||N^* xi||` for normal `N`, so the same bound holds for
    `||q (D^k - mu^k)||`.
  - Step 2 then gives `||[alpha, q]||, ||[beta, q]|| <= C epsilon` with an
    absolute `C`, and so `limsup eta_p <= C epsilon`.
  - Now (2) and Step 4 give `|lambda - 1| - epsilon <= 2 sqrt(2) C epsilon / kappa`.

  So every approximate eigencorner has its eigenvalue within
  `O(epsilon / kappa)` of `1`.  This refutes the approximate
  (contrapositive) form of `commutant-projection-extraction` directly, for
  `H = K(3,4)` and `eps = x^4`, with `delta = 2`.
- **Every projection of the relative commutant is corner-invisible.**  The
  first form of `commutant-projection-extraction` fails as well.
  - Every `q in B = {X, Y}' ∩ Q` commutes with the unitary `u = X^4`, and
    hence with `C*(u)`, which contains `D = g(u)`.  So `q` commutes with
    `alpha = D^(-3) X` and with `beta = D^(-4) Y`, with no eigen-hypothesis
    at all.
  - Step 3 therefore applies to the projection lifts `q_p` of any nonzero
    projection `q in B`.  By (2) and (1),
    `tr(q_p w_p q_p) / rk(q_p) -> 0` along the `p` with `q_p != 0`.
  - That is, `||(u - 1) q||_2 = 0` in the corner `q Q q` for every limit
    normalized trace, and so `||q u q - q||_2 = 0`.
  - Yet `u != 1`.
  So `(K(3,4), x^4, Theta)` satisfies the hypothesis of
  `commutant-projection-extraction` and violates its conclusion.
- **Numerics.**  The script checks, for `5 <= p <= 31`:
  - the Step 1 commutator bounds, and the budgets `18 ||[D, alpha]||` and
    `12 ||[D, beta]||`;
  - `||u - 1|| = 2` and the value of `tau(w)`;
  - that the numerical spectral gap stays positive, with
    `kappa_num = sqrt(2 (1 - mu_2))` between `0.16` and `0.34`.

  These numbers are consistent with the proof but prove nothing asymptotic.
  At these sizes `R_p <= 3`, so `||X_p^4 - Y_p^3||` is still of order `1`.
