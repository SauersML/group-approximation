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

There is a concrete negative evaluation for a standard allowed choice.
`cdi-standard-generator-choice-fails-projective-gate` takes the Ge--Popa
block generator with `w_1=1` and one non-scalar `w_2`.  Its conditional
expectation onto the hyperfinite tensor coordinate is nonzero while the
generator itself is not in that coordinate.  Fourier density produces one
group word with `0<|chi_A(g)|<1`, so `(G1)` fails before and after the wreath
extension.

## Exact positive specialization: group and twisted-group inputs

The same calculation gives a useful positive theorem, with no extra CDI
hypothesis.  Suppose first that

```text
(M,tau)=(L(K),tau_K),        pi=lambda_K:K->U(L(K)).    (CDI-P4)
```

Use `A=K` in Proposition 3.8.  The input character is regular and has trivial
scalar kernel.  Equations `(CDI-P2)--(CDI-P3)` show that the extended
character is regular.  It is faithful, so the extended representation is
injective and

```text
Q=L(G)                                                    (CDI-P5)
```

for the wreath-like group `G` used in the proposition.  Thus CDI preserves
an existing canonical group-factor realization exactly.  This does not
promote a new source: if `M` is non-CE, `(CDI-P4)` already says that `K` is a
non-hyperlinear group.

More generally let

```text
M=L_omega(K),
S=<range(omega)> <= T,
A=S x_omega K,                                           (CDI-P6)
```

where `S` is countable, and represent the central extension honestly by

```text
pi(s,k)=s u_k in U(L_omega(K)).                          (CDI-P7)
```

Then

```text
tau(pi(s,k))=s delta_(k,e),
pi(A) cap T1=S.                                         (CDI-P8)
```

Hence `(CDI-P3)` and the scalar-phase calculation imply that the final CDI
factor is again a twisted group factor and that its scalar phase group is
**exactly `S`**.  If `S` is finite, `cdi-noncartan-bridge-has-two-exact-gates`
realizes the output as the canonical central-character corner of a finite
central extension.  If `S` is infinite, Proposition 3.8 supplies no positive
central projection selecting that character.

This specialization also rules out a possible infinite-tensor objection.
One need not select the input central projection independently at every
Bernoulli coordinate (whose product trace would vanish).  The tensor base is
the twisted group factor of `K^(B)` with product scalar cocycle, and all
coordinate phases combine into the same global scalar group `S`.  For finite
`S` a **single** central-character projection therefore has trace `1/|S|`,
independent of `|B|`.  What is missing in the general CDI application is not
the infinite tensor bookkeeping; it is the input projective basis and finite
phase group themselves.

Primary-source scope: Proposition 3.8 supplies the crossed-product formula
and the extended representation used above.  The conclusion follows by
computing its trace and scalar kernel; the paper does not claim that an
arbitrary relation or group-measure-space factor has the special form
`(CDI-P4)` or `(CDI-P6)`.
