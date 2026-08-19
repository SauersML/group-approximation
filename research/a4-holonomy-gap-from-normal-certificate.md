---
rg: 2
id: a4-holonomy-gap-from-normal-certificate
kind: route
title: An opaque five-edge conjugacy star around 19243 forces complete chart-frame collapse
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-normal-certificate-compiler
  - unitary-star-conjugacy-hs-collapse
  - atlas-a8-six-transvection-commutant-gap
---

Use the six raw covariance opcodes defined by `(A4-STAR-0)` and abbreviate

```text
B_n=V_n(t23),
T_(n,s)=V_n(s),       s in S\{t23}.
```

The compiler supplies five opaque transport unitaries `A_n(s)` with

```text
max_(s != t23)||T_(n,s)-A_n(s)B_nA_n(s)^*||_2
 <= C_star eta_n,                                       (1)

||B_n-1||_2
 <= C_col (||sigma_n(q_19243)-1||_2+eta_n).             (2)
```

Apply `unitary-star-conjugacy-hs-collapse` directly.  Since neither theorem nor
its proof asks what the `A_n(s)` mean,

```text
max_(s in S)||V_n(s)-1||_2
 <= C_star eta_n
    + C_col (||sigma_n(q_19243)-1||_2+eta_n)
 -> 0.                                                   (3)
```

But by definition `(A4-STAR-0)`,

```text
||V_n(s)-1||_2=||[U_n,lambda_(k_n)(s)]||_2.
```

Use `atlas-a8-six-transvection-commutant-gap`.  Since `|S|=6`,

```text
dist_2(U_n,lambda_(k_n)(A8)')
 <= 15 sqrt(6) max_(s in S)||V_n(s)-1||_2
 -> 0.                                                   (4)
```

Choose a nearest commutant element `Y_n`.  For each fixed raw-S3 covariance
generator `h_a,h_b`,

```text
||[U_n,lambda(h)]||_2 <= 2||U_n-Y_n||_2 -> 0.
```

Hence `a_n^2+b_n^2->0`, stronger than `limsup<1/128`, proving
`atlas-a4-holonomy-coherence-gap`.

The resulting route has a single open mathematical leaf.  The finite compiler
must produce only five approximate **pairwise conjugacies** from the collision
covariance opcode to the other standard transvection covariance opcodes, plus
the collision readout itself.  There is no multiplication table, no frozen
conjugator word, no approximate representation, no semantic register, and no
global decoder left to prove.
