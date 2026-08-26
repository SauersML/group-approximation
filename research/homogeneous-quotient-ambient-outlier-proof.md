---
rg: 2
id: homogeneous-quotient-ambient-outlier-proof
kind: route
title: Feed the homogeneous spherical leak into the intrinsic torus-coordinate inequality
target: homogeneous-quotient-ce-forces-ambient-extension-outlier
requires:
  - homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse
  - unbalanced-torus-extracts-near-central-denominator-coordinate
---

Let `P` be one `SL_3(Z_p)`-orbit in `X` and put

```text
U=1-2 . 1_P in M_p.
```

The homogeneous-quotient theorem gives

```text
[U,u_c]=0  (c in C),
1-|tau([U,u_h])|^2 = epsilon_0 > 0.                    (HQOP1)
```

If `M_p` embeds into a tracial matrix ultraproduct, lift `U`, the fixed
lattice generators, and `u_h` to unitaries `U_n`, `X_(n,s)`, and `H_n`.
The crossed-product relations and `(HQOP1)` give

```text
delta_n -> 0,
q_n=sum_(s in S)(1-|tr([U_n,X_(n,s)])|^2) -> 0,
1-|tr([U_n,H_n])|^2 -> epsilon_0.                      (HQOP2)
```

The fixed unbalanced torus word is a relation of `A`, so its lifted defect
also tends to zero.  Therefore `(X_n,H_n,U_n)` is exactly a
projective-transfer enemy in the sense of
`unbalanced-torus-extracts-near-central-denominator-coordinate`.

If `(HQO1)` failed, after passing to an ultrafilter-large subsequence there
would be exact representations `sigma_n:A->U(d_n)` whose restrictions to
`S` approach `X_n`.  The perturbative form `(NCD5)` of the required theorem
would then force

```text
1-|tr([U_n,H_n])|^2 -> 0,
```

contradicting `(HQOP2)`.  Hence the infimum in `(HQO1)` has positive
ultralimit lower bound.
