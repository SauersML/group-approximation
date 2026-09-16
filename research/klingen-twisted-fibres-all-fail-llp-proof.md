---
rg: 2
id: klingen-twisted-fibres-all-fail-llp-proof
kind: route
title: Twisted ISW estimate with rational approximating twists separates max and min on every Klingen fibre
target: klingen-twisted-fibres-all-fail-llp
requires: []
artifacts:
  - research/artifacts/klingen-central-quotient-2026-09-16.md
---

The full proof is in `research/artifacts/klingen-central-quotient-2026-09-16.md`:

- §0: the extension `E = Z x_c Lambda`;
- §1: the fibre `A_t`;
- §2: standard facts (K), (MN);
- §3A: Steps 1', 3', 4';
- §4A: Theorem 3.

ISW citations are by source line of arXiv:2006.01874.

1. **Twisted blocks.**
   - Pick rationals `s_n = p_n/k_n -> t` with `0 < |s_n - t| < 1/2`.
   - `c mod k_n` factors through `(Z/k_n)^2 x| SL_2(Z/k_n)`, so `E` reduces to a
     finite group in which `z` has order `k_n`.
   - The `e^{2 pi i s_n}`-eigenspace of `z` in its regular representation is
     nonzero.  It gives a representation `rho_n` of `E` with
     `rho_n(z) = e^{2 pi i s_n}`.
   - `pi_n = rho_n(0, .)` satisfies
     `pi_n(x) pi_n(y) = sigma_{s_n}(x,y) pi_n(xy)`.

2. **Element.**
   - Let `B = prod_n M_{d_n}`, and let `g_1, ..., g_m` (with `e` among them) and
     `D = sqrt(m^2 - delta^2/2)` come from ISW Claim `gap` (lines 695–704).
   - Put `y = sum_i W_t(g_i) (x) (conj pi_n(g_i))_n` in `A_t (.) B`.

3. **min <= D.**
   - `||y||_min = sup_n ||sum_i W_u(g_i) (x) conj(pi_n(g_i))||`, where `W_u` is the
     universal `sigma_t`-representation.
   - Each `x -> W_u(x) (x) conj(pi_n(x))` is projective with cocycle
     `sigma_{t - s_n}`.
   - Take `x = (e2, e)` and `y' = (f2, e)`.  Then
     `sigma_{t - s_n}(x, y') / sigma_{t - s_n}(y', x) = e^{4 pi i (t - s_n)} != 1`,
     because `0 < |2(t - s_n)| < 1`.  Coboundaries on an abelian group are
     symmetric, so this is not a coboundary on `Z^2`.
   - Claim `gap` holds for all projective representations on any Hilbert space
     with cocycle non-coboundary on `Z^2`.  It is derived from Theorem `NPS`, ISW
     line 552, which is stated for arbitrary projective representations, and it
     uses `pi(e) = 1`.  So each block is at most `D`.

4. **max >= m.**
   - In `Q = prod_n (M_{d_n} (x) M_{d_n}) / c_0`, let
     `alpha_0(x) = [(pi_n(x) (x) 1)_n]`.  It satisfies
     `alpha_0(x) alpha_0(y') = sigma_t(x,y') alpha_0(xy')` exactly, because
     `|sigma_{s_n}(x,y') - sigma_t(x,y')| -> 0`.
   - By universality, `alpha_0` gives a *-homomorphism `alpha : A_t -> Q`.
   - `beta(b) = [(1 (x) b_n)_n]` is a *-homomorphism of `B` whose range commutes
     with that of `alpha`.
   - Hence `||y||_max >= ||[(T_n)_n]||`, where
     `T_n = sum_i pi_n(g_i) (x) conj(pi_n(g_i))`.
   - Identify `C^d (x) C^d` with `M_d`.  Then `U (x) conj(U)` acts as
     `X -> U X U^*`, so it fixes the maximally entangled vector.  So `||T_n|| = m`
     and `||y||_max >= m`.

5. **Conclude.**
   - The block-diagonal expectation `P : B(l^2) -> B` is ucp.  Both
     `id (x)_max P` and `id (x)_min P` are contractive and fix `y`.
   - So, in `A_t (x) B(l^2)`, `||y||_max >= m > D >= ||y||_min`.
   - By Kirchberg's criterion ([Ki93], via ISW line 728; not re-fetched), `A_t`
     fails the LLP.
