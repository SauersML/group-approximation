---
rg: 2
id: two-source-gram-alignment-proof
kind: route
title: Polar-align two sources and exhibit the adjacent-mode firewall
target: two-source-gram-alignment-pays-frequency-not-mode-purity
requires: []
---

Write `B_1^*B_2=A V`, where `A=(B_1^*B_2B_2^*B_1)^(1/2)` and extend the
polar partial isometry `V` to a unitary of the finite source.  After replacing
`B_2` by `B_2V^*`, its cross Gram with `B_1` is `A>=0`.  For

```text
C=(B_1+B_2V^*)/2,   H_0=((1+A)/2)^(1/2),   W=C H_0^(-1),
```

one has `H_0>=2^(-1/2)`, `C^*C=H_0^2`, and hence `W^*W=1`.  Functional
calculus and `sqrt((1+a)/2)>=(1+a)/2` on `[0,1]` give

```text
sum_i ||B_i'-W||_F^2
 =4 Tr(1-H_0)
 <=2 Tr(1-A)
 =||B_1-B_2V^*||_F^2.
```

Moreover, right multiplication by `V^*` preserves Frobenius norm, while
`||H_0^(-1)||<=sqrt(2)` and the parallelogram inequality give

```text
||(R-1)W||_F^2
 <=||(R-1)B_1||_F^2+||(R-1)B_2||_F^2.
```

This proves the alignment and common frequency ledger.

For sharpness, on a return-one scalar cycle of length `m` take
`w_m=(f_0+f_1)/sqrt(2)` in the first two Fourier modes and set both sources
equal to `w_m`.  The Gram defect is zero and its frequency energy is
`|exp(2 pi i/m)-1|^2/2=O(m^-2)`.  Fixed vectors of weighted return-one cyclic
shifts are exactly the flat vectors in the coordinate basis, so

```text
inf_(z flat) ||w_m-z||^2
 =2-(2/sqrt(m))||w_m||_1
 ->2-4sqrt(2)/pi>0.
```

Thus the two paid quantities cannot control mode purity with a
dimension-independent constant, exactly as asserted.
