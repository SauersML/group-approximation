---
rg: 2
id: sl3-re-coprime-face-closes-under-log-rate-proof
kind: route
title: The exact slot has a logarithmic-length representative, and the near-containment defect is subadditive
target: sl3-re-coprime-face-closes-under-log-rate
requires:
  - odd-congruence-lambda-exact-sector-collapses
---

**Step 1 (exact slot, `W = 1`).**  On the coprime `Lambda`-exact face,
`odd-congruence-lambda-exact-sector-collapses` gives `W = V'^* pi(h) = 1`
in the ultraproduct, where `V' = [pi_k(lambda_(h,k))]` for ANY choice of
`lambda_(h,k) in Lambda` with `lambda_(h,k) = h` in `SL_3(Z/n_k)`: two
choices differ by an element of `Lambda(n_k)`, on which `pi_k|_Lambda` is
trivial.  Hence

```text
|| pi_k(h) - pi_k(lambda_(h,k)) ||_2 -> 0   along U.                 (LR2)
```

**Step 2 (logarithmic slot).**  `SL_3(Z)` has Selberg--Kazhdan property
`(tau)` with respect to congruence subgroups (indeed property (T)), so the
Cayley graphs of `SL_3(Z/n)` with respect to the image of `S` form an
expander family, whose diameters are `O(log |SL_3(Z/n)|) = O(log n)`.
Choose `lambda_(h,k)` to be a shortest `S`-word representing the image of
`h` in `SL_3(Z/n_k)`; then `|lambda_(h,k)|_S <= C log n_k` with `C`
depending only on `S`.

**Step 3 (subadditivity).**  Put `delta_k(u) = dist_2(u, B_k) = || u - E_(B_k)(u) ||_2`
for the trace-preserving conditional expectation `E = E_(B_k)`, a
`||.||_op`-contraction.  For unitaries `u, v`, since `E(u) E(v) in B_k`,

```text
delta_k(uv) <= || uv - E(u)E(v) ||_2
            <= || (u - E(u)) v ||_2 + || E(u) (v - E(v)) ||_2
            <= delta_k(u) + delta_k(v),
```

using `|| ab ||_2 <= || a ||_2 || b ||_op` and `|| ab ||_2 <= || a ||_op || b ||_2`.
By induction `delta_k(pi_k(mu)) <= |mu|_S eps_k` for every `S`-word `mu`
(exactness of `pi_k` on `Lambda` makes `pi_k(mu)` the product of the
generator images).

**Step 4 (conclusion).**  By `(LR2)` and Steps 2-3,

```text
delta_k(pi_k(h)) <= delta_k(pi_k(lambda_(h,k))) + || pi_k(h) - pi_k(lambda_(h,k)) ||_2
                 <= C eps_k log n_k + o(1).
```

If `eps_k log n_k -> 0` this tends to `0` along `U`, so
`|| E_(B_k)(pi_k(h)) ||_2^2 = 1 - delta_k(pi_k(h))^2 -> 1`, contradicting
`(LR1)` for `a = h notin Lambda`.  Hence no witness on this face has
`eps_k log n_k -> 0`.
