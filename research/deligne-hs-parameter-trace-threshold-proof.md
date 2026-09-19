---
rg: 2
id: deligne-hs-parameter-trace-threshold-proof
kind: route
title: Tensor powers multiply curvature traces, so a trace error o(|t|) survives k ~ theta/t tensor powers and yields every HS parameter
target: deligne-hs-parameter-trace-threshold
requires:
  - deligne-sep7-norm-parameter-closed-subgroup
  - deligne-sector-gap-is-exactly-nonhyperlinearity
---

Notation as in the target. Two identities are used throughout.
- For a unitary `W` and `|a| = 1`: `||W - a||_2^2 = 2 - 2 Re(conj(a) tau(W))`. **(I1)**
- For `x, y` in the closed unit disc and `k >= 1`: `|x^k - y^k| <= k|x - y|`. **(I2)**

Also `||U(g)U(h) - a U(gh)||_2 = ||D_U(g,h) - a||_2`, because right multiplication by the unitary `U(gh)^*`
preserves `||.||_2`. **(I3)**

**(T1).**
- *Zero.* The trivial map `U = I` has zero defect at `theta = 0`.
- *Sums.* Take models `U` at `theta` and `V` at `phi`. Then `D_(U tensor V) = D_U tensor D_V`. By (I3), and
  since `||X tensor Y||_2 = ||X||_2 ||Y||_2` and unitaries have `||.||_2 = 1`,
  ```text
  ||D_U tensor D_V - c_theta c_phi||_2 <= ||D_U - c_theta||_2 + ||D_V - c_phi||_2 .
  ```
  Also `c_theta c_phi = c_(theta+phi)`. So `theta + phi in P_2`.
- *Inverses.* The entrywise complex conjugate `conj(U)` has curvature `conj(D_U)`, with defect equal to that of
  `U` against `conj(c_theta) = c_(-theta)`.
- *Closure.* Let `theta_j -> theta` with `theta_j in P_2`. Enumerate the pairs of `Gamma`, and let `W_n` be
  the first `n` of them. Choose `j_n` with `2 pi |theta_(j_n) - theta| max_(W_n) |b| < 1/n`, which is possible
  because `b` takes finitely many integer values on `W_n`. Then choose a model at `theta_(j_n)` with defect
  `< 1/n` on `W_n`. The resulting sequence has defect `< 2/n` against `c_theta` on `W_n`. So `theta in P_2`.
- *Comparison.* Since `||X||_2 <= ||X||_op`, `P_op` is contained in `P_2`. By
  `deligne-sep7-norm-parameter-closed-subgroup`, `1/2 in P_op`.
- Closed subgroups of `R/Z` are `R/Z` or finite cyclic `(1/m)Z/Z`. Since `1/2` lies in the group, `m` is even.

**(T2), sufficiency.**
- Let `t_n` and `U_n` be as in (T2). Replacing `U_n` by `conj(U_n)` where `t_n < 0` changes `t_n` to `-t_n`
  and keeps the trace error. So assume `t_n > 0`.
- Fix a target `theta` with representative `theta~` in `[0,1)`, and put `k_n = floor(theta~/t_n)`, so
  `k_n t_n -> theta~` and `k_n t_n <= 1`.
- Let `V_n = U_n^(tensor k_n)`, with `V_n = I` in dimension one if `k_n = 0`. Then `V_n(e) = I`,
  `D_(V_n) = D_(U_n)^(tensor k_n)`, and `tau(D_(V_n)) = tau(D_(U_n))^(k_n)`.
- Fix a pair `(g,h)`. By (I2),
  ```text
  | tau(D_(V_n)) - c_(t_n)(g,h)^(k_n) |  <=  k_n | tau(D_(U_n)) - c_(t_n)(g,h) |
                                        =   (k_n t_n) * o(1)  ->  0 .
  ```
  Moreover `c_(t_n)(g,h)^(k_n) = exp(2 pi i k_n t_n b(g,h)) -> c_theta(g,h)`, because `b(g,h)` is a fixed
  integer.
- So `tau(D_(V_n)(g,h)) -> c_theta(g,h)`. By (I1) and (I3), the HS defect of `V_n` against `c_theta` at
  `(g,h)` tends to `0`. This holds for every fixed pair, so `theta in P_2`. Since `theta` was arbitrary,
  `P_2 = R/Z`.

**(T2), necessity.**
- If `P_2 = R/Z`, put `t_n = 1/n`. Choose `U_n` with HS defect `<= n^(-2)` on `W_n`.
- Then `|tau(D) - c| = |tau(D - c)| <= ||D - c||_2`, which is at most `n^(-2)` on `W_n`.
- Every fixed pair lies in `W_n` for large `n`, so its trace error is `O(t_n^2) = o(t_n)`.

**(T3).**
- By (I1), `Re(conj(a) tau(D)) = 1 - eps^2/2`.
- Hence
  ```text
  |tau(D) - a| = |conj(a) tau(D) - 1| <= eps^2/2 + |Im(conj(a) tau(D))| .
  ```
- If `eps = o(|t|^(1/2))` and the imaginary part is `o(|t|)` on every fixed pair, then the condition of (T2)
  holds.

**(T4).**
- Suppose no triple `(W, C, t_0)` works. Then for each `n`, taking `W = W_n`, `C = 1/n` and `t_0 = 1/n`,
  there are `0 < |t_n| < 1/n` and `U_n` with `max_(W_n) |tau(D_(U_n)) - c_(t_n)| < |t_n|/n`.
- Every fixed pair lies in `W_n` for large `n`. So the sequence satisfies (T2), and `P_2 = R/Z`, a
  contradiction.

**(T5).**
- The multiplier of Deligne's triple cover `E_3`, the quotient of the universal-cover extension by `3Z`, is
  `alpha = omega^(b mod 3) = c_(1/3)`, with `omega = exp(2 pi i/3)`.
- *Pointwise and presentation defects agree.* Fix a finite presentation of `Gamma` and words `w_g` for its
  elements.
  - A pointwise model restricted to the generators has relator defects bounded by telescoping sums of
    finitely many pair defects, which tend to `0`.
  - Conversely, extend a presentation model by `U(g) = U(w_g)`, with `w_e` the empty word. Each fixed
    `w_g w_h w_(gh)^(-1)` is a fixed product of conjugates of relators. The `alpha`-phase it carries is
    `alpha(g,h)`, because the lifted section is fixed. So the pair defect tends to `0`.
- Therefore `1/3 in P_2` if and only if the `alpha`-projective presentation defect has infimum zero. By
  `deligne-sector-gap-is-exactly-nonhyperlinearity` (items 1 and 2), this holds if and only if `E_3` is
  hyperlinear.
- Now combine with (T1):
  - If `P_2 = R/Z`, then `1/3 in P_2`.
  - If `P_2 = (1/m)Z/Z`, then `1/3 in P_2` if and only if `3` divides `m`.
