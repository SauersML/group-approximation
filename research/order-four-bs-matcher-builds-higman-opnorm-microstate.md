---
rg: 2
id: order-four-bs-matcher-builds-higman-opnorm-microstate
kind: claim
title: An order-four Baumslag--Solitar matcher builds a full Higman operator-norm microstate
artifacts:
  - research/order-four-bs-matcher-builds-higman-opnorm-microstate-proof.md
distinct_from:
  three-higman-bs-seams-vanish-fourth-is-product-holonomy: that gives the necessary-and-sufficient four-matcher equation for four independently gauged exact packets in normalized Hilbert--Schmidt norm; this gives a direct operator-norm sufficient condition and an explicit four-generator tuple from one packet and one matcher.
  periodic-higman-bs-clocks-have-three-opnorm-small-seams: that proves the 3-power clocks admit matchers with vanishing one-step error but leaves the return unpaid; this shows exactly that a vanishing commutator of the fourth return would finish a countermodel.
---

**ESTABLISHED.**  Let `P,D,K` be finite-dimensional unitaries with

```text
P D P^* = D^2,
epsilon = ||D-K P K^*||_op,
r       = ||K^4 P K^(-4)-P||_op.                      (HOM1)
```

Define

```text
U_i=K^i P K^(-i),                  i=0,1,2,3.          (HOM2)
```

Then the four cyclic Higman relators satisfy

```text
max_i ||U_i U_(i+1) U_i^* - U_(i+1)^2||_op
 <= 3epsilon+3r,                                      (HOM3)
```

where `U_4` in the relator is read as `U_0`.  Also

```text
||U_i-1||_op=||P-1||_op                              (HOM4)
```

for every `i`.

Consequently, if the `q=3^n` periodic clocks admit matchers `K_n` with

```text
||D_n-K_nP_nK_n^*||_op ->0,
||K_n^4P_nK_n^(-4)-P_n||_op ->0,                      (HOM5)
```

then `(U_(0,n),...,U_(3,n))` is a full operator-norm Higman microstate and
every generator stays at distance `2` from the identity.  This would refute
`higman-four-cycle-intrinsic-mf-seed`.  The return condition is commutation
with `P_n`, not `K_n^4 approximately 1`; the latter is sufficient but
strictly stronger.
