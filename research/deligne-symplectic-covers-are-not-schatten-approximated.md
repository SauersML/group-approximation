---
rg: 2
id: deligne-symplectic-covers-are-not-schatten-approximated
kind: claim
title: For g >= 3 the finite Deligne covers of Sp_2g(Z) kill their invisible mark in every unnormalized Schatten norm with p <= 2
distinct_from:
  deligne-central-mark-hs-collapse: that is the open normalized-HS collapse at g = 2; this proves the unnormalized Frobenius and Schatten-p collapse at g >= 3, which in dimension d gives only a normalized sector floor of order d^(-1/2).
  bdl-deligne-type-two-norm-inapproximability: that is the published two-norm theorem for an order-two finite-residual element, applied there to the degree-four cover; this handles finite-residual elements of any order, every degree n >= 3, and adds a dimension-free sector gap.
  schatten-one-models-retaining-mark: that asks for unnormalized Schatten-one models retaining a mark in a Kun--Thom candidate; this proves that no Schatten-p model with p <= 2 retains the Deligne mark at g >= 3.
---

**ESTABLISHED** (`deligne-symplectic-covers-are-not-schatten-approximated-proof`).
Unreviewed. The inputs are citations, and the new part is short.

Let `g >= 3` and `n >= 3`. Let `Gamma_n` be the preimage of `Sp_(2g)(Z)` in the
connected `n`-fold cover of `Sp_(2g)(R)`, with covering generator `z` and
`J = z^2`. `J` is central of order `m = n / gcd(n, 2) >= 2`. Norms are the
unnormalized Schatten norms `||A||_p = tr(|A|^p)^(1/p)`, so `||.||_2` is the
Frobenius norm and `||A||_HS = d^(-1/2) ||A||_2` on `M_d(C)`.

1. **Stability.** `Gamma_n` is Frobenius stable.
2. **Collapse.** Let `1 <= p <= 2`. Every `||.||_p`-asymptotic homomorphism
   `phi_k : Gamma_n -> U(d_k)` satisfies `||phi_k(J) - 1||_p -> 0`. So
   `Gamma_n` is not `||.||_p`-approximated for any `p` in `[1, 2]`. For odd
   `n`, `J` generates the kernel, so every `||phi_k(z) - 1||_p -> 0`.
3. **Dimension-free sector gap.** Fix a finite presentation `<S cup {z} | R>`
   of `Gamma_n`. There is `delta_n > 0` with the following property. Let `d >= 1`,
   let `zeta` be a complex number with `zeta^n = 1` and `zeta^2 != 1`, and let
   `rho : S cup {z} -> U(d)` have `rho(z) = zeta I`. Then

   ```text
   max_(r in R) ||rho(r) - I||_2 >= delta_n,
   max_(r in R) ||rho(r) - I||_HS >= delta_n d^(-1/2).      (SG1)
   ```

   So in every nontrivial sector of `J`, the relator defect is bounded below
   by an absolute Frobenius constant, uniformly in the dimension.

**What this adds to the Deligne lane.**
- For `n = 3` at `g >= 3`, item 2 is the unnormalized analogue of `(DCM1)` in
  `deligne-central-mark-hs-collapse`.
- `(SG1)` makes the fixed-size constants of `maslov-bounded-block-sector-gap`
  explicit at `g >= 3`: a block of size `K` has normalized defect at least
  `delta_n K^(-1/2)`.
- The open HS problem is exactly the gap between exponent `1/2` and exponent `0`
  in `(SG1)`: a normalized floor independent of `d`.
- A lower bound `c d^(-b)` with some `b < 1/2`, valid for all tuples, would
  already be new.

**What it does not do.**
- It says nothing at `g = 2`. `Sp_4(R)` has real rank 2, and
  `blsw-real-lattice-frobenius-stability` needs rank at least 3. The graph's
  witness `E_3` over `Sp_4(Z)` is not covered, and Frobenius stability of
  `Sp_4(Z)` is open.
- It says nothing about hyperlinearity. A normalized-HS microstate of dimension
  `d` has Frobenius defect `eta d^(1/2)`, which need not tend to zero.
- The proof uses the Frobenius submultiplicativity behind De Chiffre--Glebsky--
  Lubotzky--Thom. That inequality has no normalized analogue.

**Model tests.**
- For `n = 2`, `J = 1` and the statement is empty. This is correct: the
  metaplectic cover is residually finite and has exact finite-dimensional models
  retaining `z`.
- A residually finite group with a nontrivial central element, such as
  `Sp_(2g)(Z) x C_3`, retains its mark in exact representations. So the
  finite-residual hypothesis is used, not decorative.
- The conclusion is metric-specific. Operator-norm and normalized-HS versions of
  item 2 are open.
