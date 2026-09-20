---
rg: 2
id: deligne-lattice-norm-models-are-tracially-blind-proof
kind: route
title: Add regular representations of shrinking finite quotients with dominating multiplicity; they separate everything off the finite residual in norm and swamp the trace
target: deligne-lattice-norm-models-are-tracially-blind
requires:
  - deligne-covers-of-sp2g-z-have-finite-residual-2z
---

Notation of the target.

**Step 0. Finite quotients.** `E_q` is finitely generated, so it has only countably many finite-index normal
subgroups. Intersecting them one at a time gives finite-index normal subgroups `N_1 >= N_2 >= ...` with
`cap_j N_j = R_q = Res_fin(E_q)`. Put `F_j = E_q / N_j`, with left regular representation `lambda_j` on `l^2(F_j)`.

For `x notin N_j`, the permutation unitary `lambda_j(x)` has no fixed basis vector. If `x N_j` has order `k >= 2`,
the spectrum of `lambda_j(x)` is the full set of `k`-th roots of unity, so

```text
|| lambda_j(x) - I ||_op  =  max_(0 <= i < k) |e(i/k) - 1|  >=  sqrt 3.                      (R1)
```

Also `tr lambda_j(x) = [x in N_j]`.

The inclusion `<z^2> <= R_q` is (DR2) of the cited node. The inclusion `R_q <= <z>` holds because `Gamma` is
residually finite. Neither is used below beyond the definition of `R_q`.

**Step 1. The padded model.** Let `theta_n : E_q -> U(d_n)` lift `Theta`. Choose `j_n -> infinity` and multiplicities
`r_n` with `r_n |F_(j_n)| / d_n -> infinity`. Put `D_n = d_n + r_n |F_(j_n)|` and

```text
theta'_n(x) = theta_n(x)  (+)  lambda_(j_n)(x N_(j_n))^((+) r_n)      in U(D_n).
```

The second summand is an honest representation. So the defect of `theta'_n` at any pair is the defect of
`theta_n`, placed in the first block. Hence `Theta' = [theta'_n]` is a homomorphism into
`U(prod M_(D_n) / (+) M_(D_n))`. In normalized HS norm, the defect of `theta'_n` is `(d_n / D_n)^(1/2)` times the
normalized-HS defect of `theta_n`, which is at most the operator-norm defect. This proves the third bullet of (TB1).

**Step 2. The kernel.** Let `x in E_q`.
- If `x in R_q`, then `x in N_j` for every `j`. So the padding block is exactly `I`, and
  `||theta'_n(x) - I|| = ||theta_n(x) - I||`. Hence `Theta'(x) = 1` iff `Theta(x) = 1`.
- If `x notin R_q`, then `x notin N_j` for all large `j`, so for all large `n`. By (R1), the operator norm of the
  padding block of `theta'_n(x) - I` is at least `sqrt 3`, so `||theta'_n(x) - I|| >= sqrt 3`. Hence
  `Theta'(x) != 1`.

Therefore `ker Theta' = ker Theta cap R_q`. `[]`

**Step 3. The shadow.** For every `x`,

```text
tr theta'_n(x) = (d_n / D_n) tr theta_n(x)  +  (r_n |F_(j_n)| / D_n) [x in N_(j_n)].
```

The first weight tends to `0` and the second to `1`. The indicator `[x in N_(j_n)]` tends to `[x in R_q]`, as in
Step 2. So every ultralimit gives `tau_w(Theta'(x)) = 1_(R_q)(x)`.

For `x in R_q`, `Theta'^w(x)` is a unitary of trace `1` in a tracial von Neumann algebra, so it equals `1`. Thus
`Theta'^w` factors through `E_q / R_q`. Its character there is `delta_e`, the left regular trace. The generated
tracial von Neumann algebra is therefore `L(E_q / R_q)` with its canonical trace, whatever `Theta` was.

The same computation, with `theta_n` deleted, gives the same shadow for `Lambda`.

**Step 4. The corner.** Let `P_n` be the projection onto the first block `C^(d_n)`. It commutes with every
`theta'_n(x)`, and `P_n theta'_n(x) P_n = theta_n(x)`. Its trace is `d_n / D_n -> 0`. So `P = [P_n]` lies in the
commutant of `Theta'(E_q)`, it compresses `Theta'` to `Theta`, and `tau_w(P) = 0`. `[]`

**Step 5. (TB2).** An invariant that depends only on the tracial ultraproduct data takes the same value on
`Theta'` as on `Lambda`, by Step 3.

For the displayed equivalence:
- Suppose `z^m` lies in the kernel of every model with shadow `1_(R_q)`. Given any `Theta`, it lies in
  `ker Theta' = ker Theta cap R_q <= ker Theta`. So `z^m in Rad_MF(E_q)`.
- The converse is the definition of `Rad_MF`.

For elements outside `R_q`, both sides fail, since `Rad_MF <= Res_fin` through the finite quotients `lambda_j`.
`[]`

**Step 6. Unnormalized data escapes.** The unnormalized Schatten-`p` defect of `theta'_n` equals that of `theta_n`,
because the padding blocks contribute exactly zero. So padding does not affect criteria of the kind in
`deligne-symplectic-covers-are-not-schatten-approximated`. Likewise a corner-extraction argument sees `P`. These
are the survivors named in the target.
