---
rg: 2
id: clifford-ce-implies-bernoulli-ce
kind: claim
title: Clifford embeddability implies Bernoulli embeddability, so the Clifford corner decides the cover
distinct_from:
  clifford-bernoulli-central-summands: That claim is the direct-sum structure of `L(Wtilde)` along the central sign projection, and its consequence 1 asserts the two summands are independent; this claim is the cross-summand implication the direct-sum picture misses, proved by diagonal doubling inside a tensor square rather than by cutting, and it corrects that assertion in one direction.
  kun-thom-clifford-crossed-product-ce: That is the open embeddability question for the Clifford corner; this is an unconditional implication between two embeddability questions and decides neither.
artifacts:
  - notes/TRUE_DOUBLE_CLIFFORD_KUN_THOM_REDUCTION.md
  - notes/TRUE_CLIFFORD_LAMP_CENTRAL_SUMMANDS.md
---

Write `N=Cl(X) crossed_product G` and `M_KT=L^infinity({-1,1}^X) crossed_product G`
for the two central summands of `L(Wtilde)`, `X=G/Gamma`.  Then

```text
N Connes embeddable ==> M_KT Connes embeddable.
```

Proof: inside `N tensorBar N` the elements `D_x=c_x tensor c_x` and
`V_g=u_g tensor u_g` are commuting self-adjoint unitaries permuted by `G`
with `tau(D_(x_1)...D_(x_k) V_g)=tau(c_(x_1)...c_(x_k) u_g)^2`, which is the
canonical trace of `M_KT`; so `M_KT` sits trace-preservingly in a tensor
square of `N`.  The two Clifford signs cancel.  This is `(DCK11)--(DCK14)`.

No converse is known: the twisted corner is a square root of the untwisted
one in the cocycle sense, and `sigma tensor sigma` is trivial while `sigma`
is not.

Consequences.

1. With `clifford-bernoulli-central-summands` (both summands embeddable iff
   `Wtilde` hyperlinear): `N` Connes embeddable **iff** `Wtilde` is
   hyperlinear.  The Clifford corner alone decides the whole cover.
2. The lanes are ordered, not independent: refuting `M_KT` embeddability
   refutes `kun-thom-clifford-crossed-product-ce` as well, while establishing
   the Clifford corner establishes the Bernoulli one.  Whoever refutes the
   weaker target closes both.
3. A second, independent derivation of the same implication runs through
   `thom-central-corner-criterion`: `Wtilde` embeds faithfully in `U(N)`, so
   `N` embeddable makes `Wtilde` hyperlinear, and Thom's Lemma 3.3 then gives
   embeddability of every twisted corner, `M_KT` included.
