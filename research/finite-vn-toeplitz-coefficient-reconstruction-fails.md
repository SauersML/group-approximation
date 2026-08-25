---
rg: 2
id: finite-vn-toeplitz-coefficient-reconstruction-fails
kind: claim
title: Finite von Neumann direct finiteness cannot reconstruct the Toeplitz coefficient quotient
distinct_from:
  hs-steinberg-root-kernel-is-linear-sofic: That asks for a decoder using an actual matricial-HS lift; this proves that no decoder internal to the limiting finite von Neumann algebra can work.
  exact-fd-invisibility-has-no-general-hs-robustification: That gives an external sofic counterexample to a generic robustness principle; this firewall occurs inside the exact Toeplitz candidate itself.
  finite-root-algebra-forces-steinberg-triviality: That obtains collapse when one root von Neumann algebra is finite dimensional; here the canonical root algebra is diffuse and the common root kernel is zero.
---

**ESTABLISHED FIREWALL.**  Let `R_f`, `H_f`, and
`w_f=x_12(P_f)` be the packet-headed Toeplitz objects of
`schur-toeplitz-root-mark-is-fd-invisible`.  There is an exact homomorphism

```text
lambda:H_f -> U(L(H_f))                                  (FVR1)
```

into a finite tracial von Neumann algebra such that its common coefficient
root kernel

```text
K_lambda={a in R_f:lambda(x_ij(a))=1 for every i!=j}       (FVR2)
```

is zero.  Consequently

```text
R_f/K_lambda=R_f,
yx=1,                 xy=1-P_f!=1.                        (FVR3)
```

In particular, the quotient decoded from the exact root/Heisenberg and HNN
relations is not directly finite, even though the ambient algebra
`L(H_f)` is finite and therefore directly finite.

It follows that none of the following can be deduced from the exact
rank-five group relations plus finiteness of the target von Neumann algebra:

1. `R_f/K_Phi` is directly or stably finite;
2. `R_f/K_Phi` has a faithful Sylvester matrix-rank function;
3. there is an injective unital multiplicative coefficient map
   `R_f/K_Phi -> M_m(M)` into any matrix amplification of the target;
4. `Phi(w_f)=1`.

Indeed `(FVR1)` is the left regular representation.  The ascending HNN
normal-form theorem embeds `EL_5(R_f)` in `H_f`, and the elementary matrix
formula `x_ij(a)=1+E_ij a` makes every coefficient root map injective.
Faithfulness of the left regular representation therefore gives
`K_lambda=0`.  The coefficient construction has `P_f!=0`, so `(FVR3)` is
not directly finite.

The Sylvester-rank obstruction is equally exact.  A faithful Sylvester
matrix-rank function makes its ring stably finite: from `yx=1`, the Sylvester
inequality gives full rank to `xy`, while additivity on the complementary
idempotents `xy` and `1-xy` gives rank zero to `1-xy`; faithfulness then gives
`xy=1`.  Applied to `(FVR3)` this is impossible.  A faithful coefficient map
to a finite von Neumann algebra or its matrix amplification is also
impossible, because those rings are directly finite.

Thus `hs-schur-toeplitz-root-defect-collapse` cannot be proved by an exact
finite-von-Neumann reconstruction.  A successful proof must use information
which fails for `(FVR1)`: specifically that the target representation is
lifted from matrices (or that its generated trace is Connes embeddable),
together with quantitative control surviving that lift.  Ambient trace
finiteness, the complete Steinberg table, the stable letter, and all exact
group relations are insufficient by themselves.
