---
rg: 2
id: kms-configuration-letters-inherit-exponent-p-proof
kind: route
title: Iterating the relation [x_u, A_i] = x_(uA_i) p times and using A_i^p = 1
target: kms-configuration-letters-inherit-exponent-p
requires: []
---

Direct proof from the relations, as printed in arXiv:1204.6506v5, §4.1 (conventions: `u^a = a^(-1) u a`, as printed there; `[x, y] = x^(-1) y^(-1) x y`,
which is implied by the equalities (e00) in the proof of KMS Lemma 4.5 but not printed. The
conclusion holds under either commutator convention.)
- G5 a): if `u` does not contain `A_i`, then `[x_u, A_i] = x_(uA_i)`, that is,
  `x_u^(A_i) = x_u x_(uA_i)`.
- G5 c): if `u'` contains `A_i` and `z in M_i`, then `[x_(u'), z] = 1`. Here `A_i in M_i` for
  `i >= 1`, and `A_0 in M_0`. Applied to `u' = uA_i` and `z = A_i`: `x_(uA_i)^(A_i) = x_(uA_i)`.
- G1: `A_i^p = 1`.

**Induction.** `x_u^(A_i^0) = x_u`. If `x_u^(A_i^n) = x_u x_(uA_i)^n`, then

    x_u^(A_i^(n+1)) = (x_u x_(uA_i)^n)^(A_i) = x_u^(A_i) (x_(uA_i)^(A_i))^n = x_u x_(uA_i) x_(uA_i)^n,

by G5 a) and G5 c), which is `x_u x_(uA_i)^(n+1)` by associativity.

**Conclusion.** Taking `n = p` and using `A_i^p = 1` gives `x_u = x_u x_(uA_i)^p`, so
`x_(uA_i)^p = 1`.
- Every `v in U` other than the `q_j` has the form `q_j w` with `w != 1` a divisor of `A_0 ... A_K`,
  so `v = u A_i` with `A_i` not in `u`.
- The two sides of each G8 relation are built from `x_(q_i A_0)` by the operations `*a_n` and `*A_n`,
  so they are products of conjugates of letters `x_v` with `v` containing `A_0`. By the above, each
  factor has order dividing `p`.

∎
