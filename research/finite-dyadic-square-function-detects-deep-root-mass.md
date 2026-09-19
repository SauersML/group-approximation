---
rg: 2
id: finite-dyadic-square-function-detects-deep-root-mass
kind: claim
title: A finite dyadic power square function detects exactly the deep root-conductor mass
distinct_from:
  bottom-a2-dyadic-face-obeys-denominator-transfer: that closes the bottom exponent-two A2 face and leaves a qualitative deeper-conductor escape; this gives an explicit positive operator measuring precisely that escape on a finite 2-power torsion packet.
  two-adic-tower-format-of-surviving-lambda-exact-enemy: that describes the congruence-tower enemy representation-theoretically; this is a scalar functional-calculus identity for one root unitary at one fixed depth.
  property-t-hs-adjoint-low-spectrum-budget: that uses spectral projections of a Kazhdan Laplacian to bound low-energy mass; this uses dyadic powers of one unitary and detects root order greater than two.
---

Let `N>=2` and let `P` be a matrix unitary satisfying

```text
P^(2^N)=I.
```

Let `E_<=1` be the spectral projection of `P` onto the eigenvalues
`{1,-1}`, and put `D_>1=I-E_<=1`. Define the positive dyadic square
function

```text
S_N(P)=(1/4) sum_(j=1)^(N-1)
             (P^(2^j)-I)^*(P^(2^j)-I).                 (DSF1)
```

Then the following operator inequalities hold:

```text
D_>1 <= S_N(P) <= (N-1)D_>1.                           (DSF2)
```

Thus normalized trace gives a finite-word detector for the exact mass on
which the root order is greater than two:

```text
tr(D_>1) <= tr(S_N(P)) <= (N-1)tr(D_>1).               (DSF3)
```

Moreover

```text
||P^2-I||_2^2<=4 tr(D_>1).                              (DSF4)
```

For a fixed conductor cutoff `N`, every term is a fixed group word and is
therefore available to a finite presentation microstate with constants
depending on `N` but not matrix dimension. Combined with
`bottom-a2-dyadic-face-obeys-denominator-transfer`, `(DSF4)` says that a
nontrivial target commutator must put positive deep-conductor mass in at
least one of the two opposite A2 chamber roots, up to the already displayed
Steinberg and presentation errors.

