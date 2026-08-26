---
rg: 2
id: kt-return-expectation-pays-one-full-edge-principal-angle
kind: claim
title: Vanishing Kun--Thom return expectation costs one full edge-algebra principal angle
distinct_from:
  kt-exact-kun-thom-edge-return-is-algebraically-absorbed: That gives expectation norm one for every exact finite-dimensional vertex representation; this quantifies the only escape for genuinely approximate vertex maps.
  kt-edge-expectation-is-a-moving-coset-gram-supremum: That writes the expectation itself as a moving coefficient supremum; this writes the required escape as forward covariance leakage of the whole generated edge algebra and exposes the Gram conditioning which can amplify small pointwise defects.
  kt-double-shortest-fold-repair-is-a-bare-wall: That extracts a wall from a bounded direct-sum repair of two vertex maps; this is a one-vertex finite-matrix inequality with no block decomposition.
---

Fix a strict Kun--Thom compressor

```text
t Gamma t^(-1)<Gamma,
```

choose `gamma in Gamma minus t Gamma t^(-1)`, and put

```text
h=t^(-1) gamma t notin Gamma.                            (KPA1)
```

Let `phi:G->U(d)` be any unitary table with `phi(1)=1`, not necessarily a
representation.  Set

```text
T=phi(t),       B=C*(phi(Gamma)),       P=E_B
```

on `L2(M_d,tr_d)`, and define the aggregate forward edge leakage

```text
L_B(T)=||(1-P) Ad(T) P||_HS^2.                           (KPA2)
```

Here the last Hilbert--Schmidt norm is the unnormalized Hilbert-space norm
of the finite-rank operator from `L2(B)` to its orthogonal complement.  Put

```text
q=||E_B(phi(h))||_2,
eta_h=||phi(h)-T^*phi(gamma)T||_2.                       (KPA3)
```

Then

```text
L_B(T) >= 1-(q+eta_h)^2.                                (KPA4)
```

In particular, any approximate vertex sequence which realizes the reduced
edge expectation at this return,

```text
q_n->0,             eta_(h,n)->0,
```

must satisfy

```text
liminf L_(B_n)(T_n)>=1.                                 (KPA5)
```

Thus exact edge normalization cannot merely fail by a vanishing aggregate
amount: at least one complete principal-angle direction of the generated
edge algebra must escape.

There is a precise multiplicative-defect form.  Choose any basis
`b_1,...,b_m` of `B` consisting of words in `phi(Gamma)` and their adjoints,
and put

```text
G_ij=<b_i,b_j>,
y_i=(1-P)T b_i T^*,
H_ij=<y_i,y_j>.                                         (KPA6)
```

Then

```text
L_B(T)=Tr(G^(-1)H).                                     (KPA7)
```

If `lambda` is the least eigenvalue of `G` and `||y_i||_2<=epsilon_i`,
then

```text
1-(q+eta_h)^2
   <= L_B(T)
   <= lambda^(-1) sum_i epsilon_i^2.                    (KPA8)
```

For a word `b_i` of length `ell_i`, each `epsilon_i` is at most the sum of
the `ell_i` covariance defects

```text
||T phi(delta) T^*-phi(t delta t^(-1))||_2,             (KPA9)
```

and every term in `(KPA9)`, as well as `eta_h`, is bounded by three ordinary
multiplicative defects of `phi` on the displayed words.  Consequently, if
all covariance defects used by the basis are at most `epsilon`, then

```text
1-(q+eta_h)^2
   <= lambda^(-1) epsilon^2 sum_i ell_i^2.              (KPA10)
```

This is the sharp finite-dimensional tradeoff left after exact models have
been excluded.  A positive reduced-MF construction must let its vanishing
pointwise actor defect be amplified by growing word complexity or a
degenerating edge Gram matrix.  Canonical character convergence alone does
not control either quantity.  The exact calibration
`kt-kazhdan-edge-grams-are-conditioned-only-at-fixed-radius` shows that even
property `(T)` of `Gamma` does not give a moving-radius lower bound for the
Gram eigenvalue in `(KPA10)`.

DERIVATION
kt-return-principal-angle-gram-proof
