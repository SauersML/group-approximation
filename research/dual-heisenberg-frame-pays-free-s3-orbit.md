---
rg: 2
id: dual-heisenberg-frame-pays-free-s3-orbit
kind: claim
title: A dual Heisenberg frame pays the free marked S3 orbit by one sixteenth
artifacts:
  - research/dual-heisenberg-free-s3-payment-proof.md
  - experiments/dual_heisenberg_free_s3_payment_audit.py
distinct_from:
  free-s3-atom-has-unit-opnorm-leakage: that permits an arbitrary profile supported on one free six-point orbit of the nine commuting signs; this adds literal dual flips for the same nine signs and proves that such a profile must be accompanied by a fixed one-sixteenth return sector.
  nine-pair-marked-heisenberg-regularization-is-selector-spectator: that puts a Heisenberg frame on auxiliary roots centralized by the native selectors and therefore does not affect their reservoir overlap; this computes the payment when the relative selector actor permutes the very same nine Heisenberg pairs by simultaneous row and column permutation.
  arbitrary-profile-selector-type-menu-dichotomy: that gives the fixed-character criterion for a supplied arbitrary profile; this forces the character profile to be uniform from ordinary root commutators and evaluates the criterion quantitatively.
---

**ESTABLISHED CONDITIONAL FULL-ROOT PAYMENT.**  Let

```text
H=<z,C_ij:1<=i,j<=3> ~= (C_2)^10
```

be the marked sign packet of
`free-s3-atom-has-unit-opnorm-leakage`.  Suppose the finite occurrence
packet is enlarged by nine involutions `D_ij` satisfying the literal
Heisenberg table

```text
[C_ij,D_kl]=z^(delta_(i,k)delta_(j,l)),
[C_ij,C_kl]=[D_ij,D_kl]=[z,C_ij]=[z,D_ij]=1.          (DHP1)
```

Suppose also that an authenticated relative actor `W_sigma`, for
`sigma in S_3`, simultaneously permutes both halves:

```text
W_sigma C_ij W_sigma^(-1)=C_(sigma i,sigma j),
W_sigma D_ij W_sigma^(-1)=D_(sigma i,sigma j).         (DHP2)
```

These are genuine binary-Leavitt Steinberg root relations, not analytic
matrix assumptions.  For example, choose nine spare indices `k_ij`, put

```text
C_ij=x_(1,k_ij)(q),       D_ij=x_(k_ij,3)(q),
q=s_1t_1=q^2,             z=x_13(q),                   (DHP3)
```

and take `W_sigma` to be the constant Weyl permutation of the nine spare
indices induced by `(i,j) |-> (sigma i,sigma j)`.  The ordinary Steinberg
commutator law and `q^2=q` give `(DHP1)--(DHP2)` exactly.

Let `rho` be an arbitrary finite-dimensional unitary representation and
put

```text
P=(1-rho(z))/2.
```

On `PH`, form the `C`-character projections

```text
e_epsilon=P product_(i,j) (1+epsilon_ij rho(C_ij))/2.
```

Every `D_ij` flips exactly the `(i,j)` sign.  It follows, without a trace
hypothesis, that all `512` projections `e_epsilon` have equal rank.  Hence
for every transposition `tau in S_3`,

```text
Q_tau=sum_(epsilon^tau=epsilon) e_epsilon,
rank(Q_tau)=32/512 rank(P)=1/16 rank(P).                (DHP4)
```

The number `32` is exact: simultaneous action of a transposition on the
nine ordered pairs has one fixed coordinate and four two-cycles.  Moreover
`W_tau` preserves every summand of `Q_tau`, so

```text
(1-Q_tau)rho(W_tau)Q_tau=0.                            (DHP5)
```

The same conclusion holds after arbitrary multiplicity amplification and
for every active trace profile.  After fixed-packet operator-norm
exactification, `(DHP4)--(DHP5)` persist with `o(1)` projection and leakage
errors, with a modulus independent of ambient matrix dimension.

Thus the free marked `S_3` type is a countermodel only while the nine signs
are allowed an arbitrary multiplicity profile.  Once the full dual-root
table for those **same signs** and its actor covariance are authenticated,
each adjacent-swap occurrence has a nonzero one-sixteenth identity-action
carrier.  Equivalently, any profile attempting to place all marked mass on
the free six-point orbit must pay a fixed operator-norm packet defect in
one of `(DHP1)--(DHP2)`.

This does not by itself close the native selector theorem.  The repository's
currently established nine-pair frame is auxiliary and commutes with the
native selectors.  What is still required is an ordinary occurrence row
identifying the actual unequal-scale relative selector with `W_tau` on the
same dual frame (or constructing `(DHP1)` for the existing selector signs).
The lemma isolates that missing full-presentation datum and proves that,
once supplied, no arbitrary-profile or free-orbit loophole remains.  No
Property T, canonical trace, literature input, or local computation is used.

DERIVATION
dual-heisenberg-free-s3-payment-proof

