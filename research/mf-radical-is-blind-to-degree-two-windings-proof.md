---
rg: 2
id: mf-radical-is-blind-to-degree-two-windings-proof
kind: route
title: Realify the approximation, split it into its two conjugate halves by one fixed unitary, and read the winding as w - w
target: mf-radical-is-blind-to-degree-two-windings
requires: []
---

Notation is as in the claim. Every step is elementary linear algebra. The only import is the
formula for the winding, which is taken as its definition here. Dadarlat, arXiv:2111.05755,
Thm 1.1, is cited in `exel-loring-mark-quantization` and is used only to name the invariant.

**Step 1: `r` is an isometric unital real `*`-homomorphism.**
- Identify `C^k` with `R^(2k)` by `xi = a + ib |-> (a, b)`. Then `r(X)` is the matrix of the
  real-linear map `xi |-> X xi`.
- So `r` is additive, real-linear, multiplicative and unital.
- The adjoint: for `X = A + iB`, `r(X^*) = r(A^T - i B^T) = [[A^T, B^T], [-B^T, A^T]] = r(X)^T`.
  Since `r(X)` is real, `r(X)^T = r(X)^*`. So unitaries go to orthogonal matrices.
- The norm: `||r(X) v|| = ||X xi||` for the real vector `v` corresponding to `xi`. The operator
  norm of a real matrix on `C^(2k)` equals its norm on `R^(2k)`. So `||r(X)|| = ||X||`.

**Step 2: the conjugate splitting.** Put
- `V_- = {(xi, -i xi)}` and `V_+ = {(xi, i xi)}` for `xi in C^k`, inside `C^(2k)`.

They are orthogonal, since `<(xi, -i xi), (eta, i eta)> = <xi,eta> + <-i xi, i eta> = <xi,eta> - <xi,eta> = 0`,
and together they span `C^(2k)`. For `X = A + iB`:
- `r(X)(xi, -i xi) = (A xi + i B xi, B xi - i A xi) = (X xi, -i X xi)`;
- `r(X)(xi, i xi) = (A xi - i B xi, B xi + i A xi) = (Xbar xi, i Xbar xi)`, where `Xbar = A - iB`.

So the unitary `W_k : C^k (+) C^k -> C^(2k)`, `(xi, eta) |-> 2^(-1/2) ((xi, -i xi) + (eta, i eta))`,
satisfies `W_k^* r(X) W_k = X (+) Xbar` for every `X`. `W_k` depends only on `k`.

**Step 3: (R1).**
- Multiplicativity of `r` and Step 1 give
  `||r(pi_n(st)) - r(pi_n(s)) r(pi_n(t))|| = ||pi_n(st) - pi_n(s) pi_n(t)||`.
- Likewise `||r(pi_n(g)) - 1|| = ||pi_n(g) - 1||`.
- So `r o Pi` is an MF approximation. Moreover `g in ker (r o Pi)'` iff
  `||pi_n(g) - 1|| -> 0` iff `g in ker Pi'`.

**Step 4: (R2).** The defect of `r o rho` on the window equals that of `rho` (Step 3), so
`I(r o rho)` is defined. Then

```text
I(r o rho) = I(W^* (r o rho) W)     by (a)
           = I(rho (+) rhobar)      by Step 2
           = I(rho) + I(rhobar)     by (b)
           = 0                      by (c).
```

**Step 5: (R3).** Fix `x = [prod_i [a_i, b_i]] in H_2(G; Z)`, with the word trivial in `G`.
- Once the defect on the finite window of all prefixes is small, `Y_rho = prod_i [rho(a_i), rho(b_i)]`
  satisfies `||Y_rho - 1|| < 1`. This is because the word evaluates to `rho(1)`, and
  `||rho(1) - 1|| = ||rho(1)^* (rho(1) - rho(1)^2)|| <= ` the defect at `(1, 1)`.
- So `log Y_rho` is given by the power series of `log(1 + Z)`, which has real coefficients.
- `det Y_rho = 1`, since it is a product of commutators. So
  `w_rho(x) = (1/2 pi i) Tr log Y_rho` lies in `Z`.

The three properties:
- (a) `Y_(u rho u^*) = u Y_rho u^*`, so `log` and `Tr` are invariant.
- (b) `Y_(rho (+) sigma) = Y_rho (+) Y_sigma`, and `log` and `Tr` respect block sums.
- (c) `Y_rhobar = conj(Y_rho)` entrywise. Real coefficients give `log conj(Y) = conj(log Y)`,
  so `Tr log Y_rhobar = conj(2 pi i w) = -2 pi i w`, and hence `w_rhobar = -w_rho`.

The tracial form. `log Y` is skew-adjoint, so `tau(log Y)` lies in `iR` for a tracial state with
`tau(Xbar) = conj tau(X)`. That property holds for normalized matrix traces and for their limits
on the corona. Then `tau(log conj Y) = conj(tau(log Y)) = -tau(log Y)`. For block sums of equal
size, normalized traces average, so `r o rho` gets `(v - v)/2 = 0`.

Apply Step 4 to `rho = pi_n` for all large `n`. Every winding and every tracial winding of
`r o Pi` vanishes, and by Step 3 its corona kernel is `ker Pi'`.

**Step 6: conjugation-natural operations.** For `O` as in the claim, Step 2 and naturality give

```text
O(r o Pi)  ~  O(Pi (+) Pibar)  ~  O(Pi) (+) conj O(Pi).
```

Step 4 applies to this last approximation, so its winding vector is `0`. Therefore (i) applied to
`r o Pi`, together with (ii), contradicts the assumption `g notin ker Pi'` for every `Pi` at
once. QED.
