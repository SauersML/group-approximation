---
rg: 2
id: higman-opnorm-defect-profile-has-dim-twelve-witness-proof
kind: route
title: Pad by the identity, check one stored tuple, and compare spectra of normal conjugates
target: higman-opnorm-defect-profile-has-dim-twelve-witness
requires: []
artifacts:
  - experiments/higman-opnorm-census-2026-09-17/analyze_tuple.py
  - experiments/higman-opnorm-census-2026-09-17/tuple_L12_defect031.txt
---

Notation is as in `(HDP1)`.

*Item 1 (monotone profile).*  Take `U` in `U(L)^4`.  The padded tuple
`U_i (+) 1` in `U(L+1)^4` has the same defect and the same `max_i ||U_i-1||`,
because every relator error is padded by `0` and every `U_i-1` by `0`.  So the
feasible set for `m_c(L+1)` contains a copy of the feasible set for `m_c(L)`
with the same values.  Hence `m_c(L+1)<=m_c(L)`, and the limit in `(HDP2)`
exists and equals `inf_L m_c(L)`.

- **(HMF5) implies (HDP2).**  Suppose `(HMF5)` holds.  Fix `c>0` and let
  `delta=delta(c)`.  A tuple with `def<delta` has `max||U_i-1||<c`.  So every
  tuple feasible for `m_c(L)` has `def>=delta`, which gives `m_c(L)>=delta`
  for all `L`.
- **(HDP2) implies (HMF5).**  Suppose `inf_L m_c(L)=delta_c>0` for every `c`.
  Then in every dimension, `def<delta_c` forces `max||U_i-1||<c`.  This is
  `(HMF5)` with `delta(c)=delta_c`.

*Item 2 (witness).*  This is a direct computation:

```text
python3 experiments/higman-opnorm-census-2026-09-17/analyze_tuple.py \
        experiments/higman-opnorm-census-2026-09-17/tuple_L12_defect031.txt
```

The file stores the real parts of `U_0..U_3` in rows `0-3` and the imaginary
parts in rows `4-7`.  The script reports:

- unitarity error `4.27e-14`;
- defects `0.309828, 0.309192, 0.309802, 0.309377`;
- `||U_i-1||` equal to `1.985418, 1.988714, 1.997066, 1.993284`.

Let `V_i` be the polar parts of the stored `U_i`.  Then `||V_i-U_i||<=4.3e-14`,
so each defect and each `||V_i-1||` changes by at most `1e-12`.  Therefore
`(V_i)` is an honest unitary tuple with `def<=0.3100` and `max||V_i-1||>=1.985`.
Padding by item 1 gives `(HDP3)`.

*Item 3 (spectral floor).*  Put `A=U_(j-1) U_j U_(j-1)^*` and `B=U_j^2`.
Both are unitary, hence normal, with `spec A=spec U_j` and
`spec B=spec U_j^2`.

- Take `lambda` in `spec A` and a unit eigenvector `x` with `Ax=lambda x`.
  Then `||A-B|| >= ||(B-lambda)x|| >= dist(lambda, spec B)`, where the second
  inequality holds because `B` is normal.
- Exchanging the roles of `A` and `B` bounds `dist(mu, spec A)` for every
  `mu` in `spec B`.

Hence `def(U)>=||A-B||>=d_H(spec U_j, spec U_j^2)`.

Now suppose `spec U_j` is the set of `L`-th roots of unity, with `L` even and
`omega=exp(2 pi i/L)`.  Then `spec U_j^2` is the set of `(L/2)`-th roots, which
is the even powers of `omega`.  The odd power `omega` lies in `spec U_j`.  Its
nearest even powers are `1` and `omega^2`, both at chordal distance
`|omega-1|=2 sin(pi/L)`.  So `def(U)>=2 sin(pi/L)`.
