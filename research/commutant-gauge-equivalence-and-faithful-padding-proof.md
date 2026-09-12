---
rg: 2
id: commutant-gauge-equivalence-and-faithful-padding-proof
kind: route
title: Strip every commutant gauge and recover the original microstate problem
target: unbounded-commutant-coherence-is-the-original-gate
requires:
  - bounded-multiplicity-toeplitz-gauges-collapse-head
---

Let `delta(U)` be the maximum defining-relator defect. Sections 1--3 of
`commutator-character-gap-and-endpoint-filling-proof` do not use the
multiplicity bound. They give constants `A_0,A_1`, depending only on the
fixed presentation, such that

```text
||rho(h_N)-I||_2 <= 2A_0 delta(U),                      (CGE1)

delta(Z) <= A_1 delta(U).                               (CGE2)
```

Here `h_N=theta_N(w)` is the bottom endpoint transvection and
`Z=(Z_s)` is the commutant gauge tuple. Equation `(CGE2)` is `(UCC1)`
with `A=A_1`.

Carrier/gauge separation also applies to the head:

```text
w(U)=rho(h_N)Z_w.
```

Therefore the reverse triangle inequality and `(CGE1)` give

```text
| ||w(U)-I||_2-||Z_w-I||_2 |
 <= ||rho(h_N)Z_w-Z_w||_2
 = ||rho(h_N)-I||_2
 <= 2A_0 delta(U).                                     (CGE3)
```

This is `(UCC2)` with `B=2A_0`. In particular, if
`delta(U_n)->0` and `||w(U_n)-I||_2>=epsilon`, then
`delta(Z_n)->0` and

```text
liminf_n ||(Z_n)_w-I||_2 >= epsilon.
```

Thus every countersequence in the commutant-gauged ansatz already contains
an ordinary Jacobson countersequence in its multiplicity variables.

The converse is exact and deliberately simple. Given any finite-dimensional
unitary tuple `V=(V_s)`, choose the trivial representation

```text
rho:F_N -> U(H),              rho(g)=I.
```

Its commutant is all of `B(H)`. Set `Z_s=V_s`. Then

```text
U_s=rho(theta_N(s))Z_s=V_s
```

for every generator, so both the presentation defects and the head defect
are unchanged. This proves the existence equivalence.

For completeness, the trivial-carrier shortcut can be removed without
changing the asymptotic statement. Suppose `V^(n)` is a head-retaining
microstate of dimension `d_n`. Choose any finite-section size `N_n` and
let `lambda_n` be the left regular, hence faithful, representation of
`F_(N_n)`. For an integer `L_n` define

```text
rho_n = lambda_n directSum I_(L_n d_n),

Z_(s,n)=I_(dim lambda_n) directSum (V_s^(n))^(directSum L_n).
```

Every `Z_(s,n)` commutes with `rho_n(F_(N_n))` and `rho_n` is faithful.
Let

```text
alpha_n=dim(lambda_n)/(dim(lambda_n)+L_n d_n).
```

The regular-carrier relator and head distances are at most `2`. Hence

```text
delta(U_n)^2 <= 4 alpha_n+delta(V^(n))^2,                (CGE4)

||w(U_n)-I||_2^2
 >= (1-alpha_n)||w(V^(n))-I||_2^2.                      (CGE5)
```

Choose `L_n` so that `alpha_n->0`. Equations `(CGE4)--(CGE5)` preserve
vanishing relator defect and positive head defect while the carrier remains
faithful. What vanishes is its normalized trace weight.

None of these reductions applies to generator perturbations outside
`rho(F_N)'`. There, evaluation of a word interlaces carrier matrices with
the perturbations, so no tuple `Z` satisfying `(CGE2)` is produced. This
is the exact algebraic distinction between unbounded commutant coherence
and genuine isotype mixing.
