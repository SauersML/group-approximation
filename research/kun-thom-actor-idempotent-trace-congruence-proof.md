---
rg: 2
id: kun-thom-actor-idempotent-trace-congruence-proof
kind: route
title: Push the idempotent to congruence quotients whose orders avoid a given prime outside P
target: kun-thom-actor-algebraic-idempotents-pass-trace-test
requires:
  - kun-thom-actor-finite-subgroup-ring-equals-z-inverted-p
artifacts:
  - research/artifacts/bc-kun-thom-trace-test-2026-09-12.md
---

The full proof is in the artifact, Section 2. Summary:

1. **Finite-quotient trace.** Let `N ◁ G` have finite index, with `supp(e) ∩ N ⊆ {1}`. The image
   `ebar ∈ M_n(C[G/N])` is an idempotent with `tau_(G/N)(ebar) = tau(e)`. On `C^n ⊗ l^2(G/N)` it
   has integer rank `m`, and `Tr = |G/N| tau`. So `tau(e) = m/[G:N]`.
2. **Congruence quotients.** For a prime `p' != p`, reduce modulo the `SL_d(Z)`-invariant ideal
   `I_(p') = (x^v - 1 : v ∈ p' Z^d)` and modulo `p'` on `SL_d(Z)`. The index is

   ```text
   |SL_r(F_q)| · |SL_r(F_(q^k))|^((p'^d-1)/k) · |SL_d(F_(p'))|,   k = ord_(p')(q),
   ```

   because `F_q[(Z/p')^d] ≅ F_q × F_(q^k)^((p'^d-1)/k)`. Every finite set of nontrivial elements
   avoids the kernel for large `p'`.
3. **Dirichlet.** Fix a prime `l` outside `P`, so `l != p`, `o = ord_l(q) > r` and `l > d + 1`.
   Choose `p'` large with:
   - `p' ≡` a primitive root `(mod l)`;
   - `p' ≢ 0, 1 (mod s)` for every odd prime `s | o`;
   - if `o` is even, `p' ≡ 3 (mod 4)` with `q` a square mod `p'`, which is a congruence condition
     mod 8 or mod `p`.
   These are compatible, the one overlap `s = p` included. Then `gcd(k, o) = 1` and
   `ord_l(p') = l - 1 > d`, so `l` divides none of the three factors of the index.
4. **Conclusion.** Write `tau(e) = a/b` in lowest terms. Then `b | [G : N_(p')]` for such `p'`, so
   `l ∤ b`. Hence `tau(e) ∈ Z[1/P]`, and this ring is `Lambda^G` by the required claim.
5. **Corollary.** For finite spectrum, `prod (a - lambda_i) = 0` already in `M_n(C[G])`, because
   `lambda` is injective on `C[G]`. Spectral projections are Lagrange polynomials in `a`. QED
