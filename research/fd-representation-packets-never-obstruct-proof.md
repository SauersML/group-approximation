---
rg: 2
id: fd-representation-packets-never-obstruct-proof
kind: route
title: Split the finite-dimensional image algebra over the image ideal and lift the finite-dimensional discrepancy
target: fd-representation-packets-never-obstruct-ucp-sections
requires: []
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
---

Put `rho:=rho_1 (+) ... (+) rho_m`, `B:=rho(A)` (a finite-dimensional
C-star algebra, being a `*`-subalgebra of a finite-dimensional one) and
`J:=rho(I)`, a closed two-sided ideal of `B` because `rho:A->>B` is a
surjective `*`-homomorphism.  Each coordinate compression `p_j:B->rho_j(A)` is
a unital `*`-homomorphism with `p_j o rho = rho_j`.

**Step 1 (the quotient splits, but not unitally).**  `B` is finite-dimensional,
so `J` is a direct summand: `B=J (+) B_0` as C-star algebras, `1_B=1_J+1_(B_0)`,
and the quotient map `B->>B/J` restricts to a `*`-isomorphism `B_0 -> B/J`.
Let `kappa:B/J->B` be its inverse followed by the inclusion; `kappa` is an
injective `*`-homomorphism with `kappa(1)=1_(B_0) != 1_B` whenever `J!=0`, so
`kappa` alone is not a ucp map into `B` and cannot be used as it stands.

**Step 2 (a unital ucp map `E->B` over the quotient).**  Since `rho(I)=J`, the
map `rho` descends to a `*`-homomorphism `rho-bar:Q->B/J` with
`rho-bar o q = (B->>B/J) o rho`.  Pick any state `f` on the operator system `E`
and define

```text
psi:E->B,   psi(x):= f(x) 1_J  +  kappa(rho-bar(x)).        (FPP1)
```

`psi` is unital (`psi(1)=1_J+1_(B_0)=1_B`) and completely positive, being the
sum of the cp maps `x |-> f(x)1_J` (a state times a positive element) and
`kappa o rho-bar|_E` (a `*`-homomorphism restricted to an operator system).
Composing with the quotient map kills the `J`-summand, so

```text
(B ->> B/J) o psi = rho-bar|_E.                             (FPP2)
```

**Step 3 (pull `psi` back through `I`).**  Let `t:E->A` be any unital
self-adjoint linear section of `q` over `E`; one exists because `E` is
finite-dimensional (take a linear section, replace it by
`x |-> (t_0(x)+t_0(x^*)^*)/2`, and correct at `1` using `q(1_A)=1_Q`).  By
`(FPP2)` and `rho-bar o q = (B->>B/J) o rho`,

```text
(B ->> B/J)(psi(x)-rho(t(x))) = rho-bar(x)-rho-bar(q t(x)) = 0,
```

so `psi-rho o t` takes values in `J=rho(I)`.  Choose a self-adjoint basis
`e_1=1,e_2,...,e_n` of `E`.  Then `(psi-rho o t)(1)=1_B-1_B=0`, and for
`i>=2` the element `(psi-rho o t)(e_i)` is self-adjoint and lies in `rho(I)`;
pick `a_i in I` with `rho(a_i)=(psi-rho o t)(e_i)` and replace `a_i` by
`(a_i+a_i^*)/2`, which is still a preimage because `(psi-rho o t)(e_i)` is
self-adjoint and `rho` is `*`-preserving.  Define `d:E->I` linearly by
`d(1):=0`, `d(e_i):=a_i`, and set

```text
s:=t+d.                                                     (FPP3)
```

**Step 4 (conclusion).**  `s` is linear, unital, and self-adjoint (it is
self-adjoint on a self-adjoint basis).  Because `d(E) subset I`,
`q s = q t = id_E`, which is `(FP1)`.  By construction `rho o s = rho o t +
(psi-rho o t) = psi`, which is ucp by Step 2, and therefore
`rho_j o s = p_j o rho o s = p_j o psi` is ucp for each `j`, being a unital
`*`-homomorphism composed with a ucp map.

**Where the depth is lost.**  Step 3 chooses `a_i` as *some* preimage in `I`.
Nothing in the argument bounds it: enlarging the packet enlarges `J`, changes
`psi`, and moves the required `a_i` arbitrarily far into the ideal.  This is
exactly the quantity that `finite-relator-reservoir-repairs-every-fd-packet`
asks to be bounded, and the reason that conjecture is not a corollary of this
route.
