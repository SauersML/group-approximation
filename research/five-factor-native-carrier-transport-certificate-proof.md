---
rg: 2
id: five-factor-native-carrier-transport-certificate-proof
kind: route
title: Telescope the two native carrier factorizations through conditional expectations
target: five-factor-native-carrier-transport-certificate
requires:
  - separate-d8-carriers-cannot-recover-in-commuting-descendants
  - transported-coefficient-corners-share-flat-quarter-carrier
---

Let `E_A,E_B` be the trace-preserving conditional expectations and set

```text
q_A=E_A(q),       t_i=E_A(T_i),
c=E_B(C),         Q_B=E_B(Q).
```

Conditional expectation is contractive in operator norm, so these five
operators are contractions.  Moreover they realize the five distances in
`(FFT2)`.  Put `p_i=t_i q_A t_i`.  Telescoping only contraction factors gives

```text
||T_i q T_i-p_i||_2
 <= ||(T_i-t_i)qT_i||_2
    +||t_i(q-q_A)T_i||_2
    +||t_iq_A(T_i-t_i)||_2
 <= 2 eta_i+eta_q.                                    (1)
```

Both `P_i` and `p_i` are contractions.  Since `p_0p_1` belongs to `A`, a
second telescope gives

```text
dist_2(F,A)
 <= ||P_0P_1-p_0p_1||_2
 <= ||P_0-p_0||_2+||P_1-p_1||_2
 <= 2 eta_q+2 eta_0+2 eta_1.                          (2)
```

Similarly `c^*Q_Bc` belongs to `B`, and

```text
||C^*QC-c^*Q_Bc||_2
 <= ||(C^*-c^*)QC||_2
    +||c^*(Q-Q_B)C||_2
    +||c^*Q_B(C-c)||_2
 <= 2 eta_C+eta_Q.                                    (3)
```

Adding `(2)--(3)` and applying
`separate-d8-carriers-cannot-recover-in-commuting-descendants` yields `(FFT4)`.
If every error is at most `eta`, the left side of `(FFT4)` is at most
`9 eta`, proving `(FFT5)`.
