---
rg: 2
id: word-telescoping-transfers-the-endpoint-conjugacy-proof
kind: route
title: Compare an arbitrary tuple to the two conjugate endpoint words
target: head-retention-forces-macroscopic-carrier-motion
requires:
  - toeplitz-folner-compressions-cannot-retain-jacobson-head
---

For unitary tuples `U,A` and a word
`q=s_1^(epsilon_1)...s_l^(epsilon_l)`, insert one changed letter at a
time. Unitary invariance and

```text
||U_s^(-1)-A_s^(-1)||_2=||U_s-A_s||_2
```

give the standard telescoping estimate

```text
||q(U)-q(A)||_2 <= length(q) eta(U,A).                  (WTE1)
```

Let `q_0` be the fixed consequence word expressing the Steinberg
relation which uses `TS=1`. A fixed van Kampen filling of `q_0` by
defining relators gives a constant `B_0` such that

```text
||q_0(U)-I||_2 <= B_0 delta(U).                         (WTE2)
```

Under the literal Toeplitz section, `q_0(A)` is the top endpoint
transvection and `w(A)` is the bottom endpoint transvection. They are
conjugate inside `GL_(28N)(F_2)`, so every unitary representation
`rho` satisfies

```text
||w(A)-I||_2=||q_0(A)-I||_2.                            (WTE3)
```

Apply `(WTE1)` first to `w` and then to `q_0`:

```text
||w(U)-I||_2
 <= ||w(U)-w(A)||_2+||w(A)-I||_2
 <= length(w) eta(U,A)+||q_0(A)-I||_2
 <= (length(w)+length(q_0))eta(U,A)+||q_0(U)-I||_2
 <= (length(w)+length(q_0))eta(U,A)+B_0 delta(U).       (WTE4)
```

Thus `(HMC1)` holds with

```text
C_0=B_0,                  C_1=length(w)+length(q_0).
```

No commutation, block structure, or finite-dimensional representation
theory was used. If `U_s=A_sZ_s`, then
`||U_s-A_s||_2=||Z_s-I||_2`, so `(HMC2)` is directly a lower bound on
the size of at least one relative gauge.

For a scalar two-sheet rotation

```text
Z_s=R(theta_s) tensor I,
```

its normalized Hilbert--Schmidt distance from the identity is the
two-dimensional distance of `R(theta_s)` itself. Hence a head-retaining
sequence forces one rotation angle to remain bounded away from zero.
This is the promised raw coefficient lower bound. It leaves open
macroscopic rotations, whose carrier-coefficient cancellations cannot be
linearized around the identity.
