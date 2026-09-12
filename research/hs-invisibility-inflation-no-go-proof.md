---
rg: 2
id: hs-invisibility-inflation-no-go-proof
kind: route
title: Inflate a corona model by a trivial block
target: hs-invisibility-inflation-no-go
requires: []
artifacts:
  - non_mf_groups_exist.tex
---

## Why sufficient

By the coordinate presentation of MF (`countable-group-mf-conventions`) a
faithful corona representation on `(m_n)` is an operator-norm asymptotic
representation `U_n: H -> U(m_n)` with
`‖U_n(g) U_n(h) - U_n(gh)‖_op -> 0` and, for each `h != 1`,
`limsup ‖U_n(h) - 1‖_op >= c_h > 0`.

Put `V_n(h) = 1_{N_n} oplus U_n(h)` on `d_n = m_n + N_n`.  Then

- `‖V_n(g) V_n(h) - V_n(gh)‖_op = ‖U_n(g) U_n(h) - U_n(gh)‖_op -> 0`, so
  `V` is again an operator-norm asymptotic representation and defines a
  homomorphism `Theta` into the corona on `(d_n)`;
- `‖V_n(h) - 1‖_op = ‖U_n(h) - 1‖_op`, so `Theta` separates exactly the
  same elements and is faithful whenever the original is;
- `‖V_n(h) - 1‖_2^2 = (1/d_n) ‖U_n(h) - 1‖_F^2 <= 4 m_n / d_n -> 0`, so
  `‖Theta(h) - 1‖_2 = 0` for every `h`, uniformly on the group.

The dimensions may be taken strictly increasing, so the inflated model
satisfies the normalized variant of the MF definition as well.  The first
consequence is immediate: the inflated model realizes the hypothesis
"`x` is HS-invisible in every corona representation" simultaneously with
faithfulness, so that hypothesis alone is consistent with MF-ness.  The
second consequence is the definition of a sofic approximation, whose
separation requirement `d_Hamming(sigma_n(h), id) -> 1` is a statement in
the same metric as its defect.
