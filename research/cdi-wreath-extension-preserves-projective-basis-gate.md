---
rg: 2
id: cdi-wreath-extension-preserves-projective-basis-gate
kind: claim
title: The CDI wreath extension preserves rather than creates the projective-basis gate
distinct_from:
  cdi-noncartan-bridge-has-two-exact-gates: that states the two abstract gates for the final CDI character; this evaluates the first gate on the actual Proposition 3.8 normal form and identifies the scalar phase group controlling the second.
  cdi-property-t-envelope-has-nonabelian-base: that records the source construction at factor level; this computes its character coefficients and scalar kernel exactly.
---

Use the notation of Chifan--Drimbe--Ioana Proposition 3.8.  Thus
`G in WR(A,B)` is written as a cocycle semidirect product
`A^(B) rtimes_(alpha,v) B`, a homomorphism
`pi:A -> U(M)` is extended to

```text
pi_tilde:G -> U(Q),
Q=M^B rtimes_(beta,w) B,
pi_tilde(x,e)=tensor_(d in B) pi(x_d),
pi_tilde(e,b)=u_b.                                    (CDI-P1)
```

Let `chi_A=tau_M o pi` and `chi_G=tau_Q o pi_tilde`.  Then the actual CDI
construction satisfies

```text
chi_G(x,b)=0                                  if b!=e,
chi_G(x,e)=product_(d in B) chi_A(x_d).       (CDI-P2)
```

Moreover `pi_tilde(x,b)` is scalar exactly when `b=e` and every
`pi(x_d)` is scalar.  Consequently

```text
chi_G vanishes off its scalar kernel
iff
chi_A vanishes off its scalar kernel.                  (CDI-P3)
```

Thus crossed-product Fourier support kills every nontrivial acting-group
coordinate, but the tensor base retains the input character coefficient for
word-for-word single-site elements.  Proposition 3.8 neither forces nor
repairs gate `(G1)` of `cdi-noncartan-bridge-has-two-exact-gates`; it merely
transfers that gate from the chosen three-unitary representation of
`F_3` generating `M_tilde`.

The scalar phase image is also unchanged.  If

```text
S_A=pi(A) intersect T1,
S_G=pi_tilde(G) intersect T1,
```

then `S_G=S_A`: scalar base tensors multiply phases from `S_A`, and a
single-site tensor realizes every phase in `S_A`.  Hence finite `S_A` is a
sufficient source-level condition for the final multiplier to be
finite-valued, while `S_A={1}` makes gate `(G2)` automatic with trivial
multiplier.  CDI's generator lemma asserts only that three unitaries generate
`M_tilde`; it gives no vanishing or scalar-phase condition.  Therefore the
published construction decides neither gate for its chosen `pi`.

