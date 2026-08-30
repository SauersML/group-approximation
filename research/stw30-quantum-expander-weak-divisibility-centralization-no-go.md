---
rg: 2
id: stw30-quantum-expander-weak-divisibility-centralization-no-go
kind: claim
title: Real rank zero and exact weak divisibility do not centralize matrix blocks
distinct_from:
  perera-rordam-rr0-approximately-divisible: that asks whether simplicity, separability and nuclearity make real-rank-zero weak divisibility central; this theorem shows that the weak-divisibility data and real rank zero alone cannot do so, in a nonseparable non-simple matrix corona.
artifacts:
  - research/artifacts/stw30-quantum-expander-centralization-firewall-audit-2026-08-30.md
---

There are integers `d_j->infinity`, a fixed integer `D`, a constant `c>0`,
and unitaries

```text
u_1,...,u_D in Q=product_j M_(d_j) / direct_sum_j M_(d_j)
```

such that:

1. `Q` has real rank zero;
2. for every `n>=2`, there is a unital injective star-homomorphism

   ```text
   M_n direct_sum M_(n+1) --> Q;
   ```

3. there is no unital star-homomorphism

   ```text
   M_2 direct_sum M_3 --> Q intersect {u_1,...,u_D}'.       (1)
   ```

Quantitatively, if `theta_j:M_2 direct_sum M_3->M_(d_j)` are unital
star-homomorphisms and

```text
h=e_11^(2) direct_sum e_11^(3),
```

then

```text
max_(1<=s<=D) norm([theta_j(h),u_s^(j)]) >= c              (2)
```

at every coordinate of the quantum-expander family.

Thus exact weak divisibility at every scale, even together with real rank
zero and finite-dimensional local models, has no abstract centralization
principle.  Any proof of the Perera--Rordam central question must use at
least one additional structural or uniform-selection input beyond the
existence and projection-refinement data of the weak-divisibility
embeddings.  The example does not decide which extra hypothesis is decisive.
