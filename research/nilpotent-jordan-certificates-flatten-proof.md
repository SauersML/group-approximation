---
rg: 2
id: nilpotent-jordan-certificates-flatten-proof
kind: route
title: Induct along powers of u, applying the separated triangular lemma to the Frobenius matrix at each step
target: nilpotent-jordan-certificates-flatten-to-minors
requires:
  - separated-triangular-steps-flatten-to-minors
artifacts:
  - research/artifacts/separated-triangular-certificates-flatten-2026-09-12.md
---

Section 2 of the artifact. Induction on `j`, starting from `f <~ u`.
1. **Frobenius matrix.** For `n x n` matrices `V`, `U`, the matrix `T = [[V, I], [0, U]]` satisfies
   `[[I, 0], [-U, I]] T [[I, 0], [-V, I]] = [[0, I], [-UV, 0]]`. Permuting columns, `T <~ I_n (+) UV`.
2. **Step.** With `V = u^j` and `U = u`, the hypothesis `f^((+)j) <~ u^j (+) I_((j-1)n)` and `f <~ u`
   separate the two diagonal blocks of `T`: the first minor mixes `u^j` only with its own padding, and the
   second sees only `u`. `separated-triangular-steps-flatten-to-minors` gives
   `f^((+)(j+1)) <~ T (+) I_((j-1)n) <~ I_(jn) (+) u^(j+1)`.
3. **End.** At `j = k`, `u^k = 0`, and `I_((k-1)n) (+) 0 <~ I_((k-1)n)`. The retract gives
   `k[f] <= (k-1)n[A]`.
4. **Kill test.** `f = diag(1,1,1,0)` with `n = 4` and `k = 3` gives `I_9 <~ I_8`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 37.2 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *the Frobenius conjugation `[[0, I], [-UV, 0]]`;*
- *Lemma S applied with `A = u^j`, `Z_1 = I_((j-1)n)`, `B = u`, `C = I_n`, where `f^((+)j)` is idempotent;*
- *the end at `u^k = 0`, the `K_0` retract, and `I_9 <~ f^((+)3) <~ I_8`.*
