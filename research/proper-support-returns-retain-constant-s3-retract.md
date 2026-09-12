---
rg: 2
id: proper-support-returns-retain-constant-s3-retract
kind: claim
title: Any properly supported return family leaves a split constant-root S3 corner
artifacts:
  - research/proper-support-constant-s3-retract-proof.md
distinct_from:
  endpoint-j1-enlargement-has-native-s3-retract: that verifies the literal endpoint and first prefix Whiteheads on the q corner; this gives the abstract all-family lemma and applies it simultaneously to every zero-prefix partial Whitehead, including J2.
  endpoint-external-subgroup-has-native-s3-retract: that uses the larger complement of one endpoint support; this identifies the exact common-support hypothesis under which arbitrarily many added return words still cannot remove the native constant-root quotient.
  b2-pairs-full-hecke-first-support: that uses B2=s_00t_1, which crosses from the q cylinder into the zero-prefix cylinder and therefore lies outside the proper-support hypothesis; this proves why such a crossing occurrence is qualitatively necessary before the retract can fail.
---

**ESTABLISHED GENERAL CORNER FENCE.**  Let `R` be a unital ring of
characteristic two, let `e` be an idempotent with `r=1-e!=0`, and let
`a!=b` be two matrix coordinates.  Suppose a family of invertible matrices
`(W_i)` obeys

```text
(rI)W_i=W_i(rI)=rI.                                  (PSR1)
```

Put

```text
n=I+E_ab,              m=I+E_ba,
G=<n,m,(W_i)>.                                           (PSR2)
```

Then `N=<n,m>~=GL_2(F_2)=S_3` is a retract of `G`: there is a homomorphism

```text
rho:G -> N,           rho(n)=n, rho(m)=m, rho(W_i)=1. (PSR3)
```

Indeed, `rI` reduces every generator.  Corner restriction kills every
`W_i` and sends `n,m` to the two standard transvections over the prime
subring `{0,r}~=F_2` of `rRr`.  Their corner images form `S_3`, and the
restriction is injective on the original constant subgroup `N`, giving
the split retraction.

For the binary Leavitt ring take

```text
e=p=s_0t_0,                 r=q=s_1t_1.                (PSR4)
```

Every zero-prefix partial Whitehead `What_(u,v;k)`, `k>=1`, differs from
the identity only by coefficients two-sidedly supported under `p`.
Consequently `(PSR1)` holds simultaneously for **any family** of such
Whiteheads.  In particular

```text
<P,J_1,J_2,n,m> -> <n,m>~=S_3                         (PSR5)
```

is a split retraction killing all three literal Whiteheads

```text
P=What_(8,2;2), J_1=What_(7,8;1), J_2=What_(8,9;2).  (PSR6)
```

Thus adding more zero-prefix Whitehead braids cannot close the native
`S_3` seam, regardless of word length.  More generally, a support-based
breaker must contain occurrences whose deviations are not all confined
under one proper idempotent.  This common-support completeness is only a
necessary condition, not a sufficient breaker.

The literal root `B_2=x_84(s_00t_1)` is the first authenticated endpoint
ingredient in the current lane that escapes this **scalar-corner** fence:
its coefficient has right support `q` and left support under `p`, so it
crosses the two scalar corners rather than vanishing on both sides of
`qI`.  This is only the boundary of the scalar `qI` argument, not a genuine
breaker.  `endpoint-native-heads-retain-coordinate-q-s3-retract` replaces
`qI` by `q(E_77+E_88)` and proves that `B_2`, both prefix heads, and the
full endpoint Singer word still leave a split native `S_3` corner.

No Property `(T)`, Kazhdan input, trace profile, stability theorem,
finite-word enumeration, or numerical approximation is used.

DERIVATION
proper-support-constant-s3-retract-proof
