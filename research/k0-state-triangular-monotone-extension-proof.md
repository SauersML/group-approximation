---
rg: 2
id: k0-state-triangular-monotone-extension-proof
kind: route
title: Define the state on idempotent classes of the triangular Grothendieck group and extend it by Zorn's lemma
target: k0-state-extends-to-rank-function-iff-triangular-monotone
requires:
  - sylvester-rank-functions-iff-no-triangular-certificate
artifacts:
  - research/artifacts/separated-triangular-certificates-flatten-2026-09-12.md
---

Section 4 of the artifact.
1. **Only if.** A rank function is `<=_T`-monotone and additive.
2. **Setup.** Work in the Grothendieck group `G` of matrices modulo mutual `<=_T`-domination, with cone `P`
   and order unit `u = [I_1]` (steps 2–3 of Theorem 2.1 of the kill-test artifact). `H` is the subgroup
   of idempotent classes, and `phi([e] - [f]) = s(e) - s(f)`.
3. **Well defined.** `e (+) f' (+) K ~ e' (+) f (+) K` and monotonicity applied both ways give equality.
4. **Positive.** `[e] - [f] = [N] - [M]` with `M <=_T N` gives `f (+) M (+) K <=_T e (+) M (+) K`.
5. **Extend.** Extend one element at a time. The lower bounds `phi(h)/n` over `h <= n x` never exceed the
   upper bounds `phi(h')/n'` over `n' x <= h'`, and Zorn's lemma finishes. This is the extension lemma of
   `anti-central-state-exists-iff-lifted-trace-relatively-positive`.
6. **Conclude.** A positive functional on `G` with value 1 at `u` is a Sylvester rank function, by Theorem
   2.1(a) of `sylvester-rank-functions-iff-no-triangular-certificate`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 37.4 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *well-definedness via the hypothesis applied both ways to `e (+) f'` and `e' (+) f`;*
- *positivity with `K' = M (+) K`;*
- *the one-step extension lemma (Section 24), and Theorem 2.1(a).*
