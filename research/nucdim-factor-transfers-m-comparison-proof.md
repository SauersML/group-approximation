---
rg: 2
id: nucdim-factor-transfers-m-comparison-proof
kind: route
title: Push comparison through the order zero colours of an almost order zero approximation of B
target: nucdim-factor-transfers-m-comparison
requires: []
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Full proof: artifact Section 5 (Theorem A), using the lemmas of Sections 1, 2
and 4 of the same artifact, all proved there.

Put `cA = A tensor K` and `E = cA tensor B`, so `E` is the stabilization of
`A tensor_min B` and every Cuntz class is represented in `E_+`.  By
Winter--Zacharias, *The nuclear dimension of C*-algebras*, Adv. Math. 224
(2010), arXiv:0903.4914, Proposition 3.2 (separable `B`), there are finite
dimensional `F_k = F_k^(0) (+) ... (+) F_k^(m)`, c.p.c. `psi_k: B -> F_k` and
c.p.c. order zero `phi_k^(i): F_k^(i) -> B` with `phi_k psi_k -> id` pointwise
and each induced `psibar^(i): B -> prod_k F_k^(i) / (+)_k F_k^(i)` order zero.
Define

```text
Psi^(i): E -> Q^(i) = prod_k cA tensor F_k^(i) / (+)_k ,     Phi^(i): Q^(i) -> E_infty = prod_k E / (+)_k E
```

by `id tensor psi_k^(i)` and `id tensor phi_k^(i)` coordinatewise.

1. `Psi^(i)` is c.p.c. order zero: the trilinear defect of `id tensor psi_k^(i)`
   tends to zero on elementary tensors (because `psibar^(i)` is order zero),
   hence everywhere by the uniform bound; the trilinear identity characterizes
   order zero maps (artifact Lemma 2.1).
2. `Phi^(i)` is c.p.c. order zero (Winter--Zacharias, Munster J. Math. 2
   (2009), arXiv:0903.3290, Cor. 3.3, and artifact Lemma 2.2).
3. `sum_i Phi^(i) Psi^(i)` is the diagonal embedding `iota`.
4. If `(k+1)[a] <= k[b_i]`, the order zero amplification of `Psi^(i)`
   (Winter--Zacharias 2009, Cor. 3.5) gives the same relation in `Cu(Q^(i))`.
   Every `cA tensor F_k^(i)` has Cuntz semigroup a finite product of copies of
   `Cu(A)`, hence almost unperforated, and artifact Lemma P (proved there by
   lifting to coordinates and using almost unperforation coordinatewise) gives
   `Psi^(i)(a) <~ Psi^(i)(b_i)`.  Applying `Phi^(i)` and summing,

   ```text
   iota(a) = sum_i Phi^(i)Psi^(i)(a) <~ (+)_i Phi^(i)Psi^(i)(a) <~ (+)_i iota(b_i)
   ```

   in `M_(m+1)(E_infty)`, and diagonal reflection (artifact Lemma 4.1) gives
   `[a] <= [b_0] + ... + [b_m]`.

Imports: Winter--Zacharias 2010 Prop. 3.2 (with the audit of its constants in
artifact Section 3), Winter--Zacharias 2009 Thm 2.3 and Cors 3.2, 3.3, 3.5
(arXiv numbering), Kirchberg--Rordam, Adv. Math. 167 (2002), Lemma 2.2.
