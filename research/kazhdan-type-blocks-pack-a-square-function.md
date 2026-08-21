---
rg: 2
id: kazhdan-type-blocks-pack-a-square-function
kind: claim
title: Kazhdan type blocks pack every scale into one HS square function
distinct_from:
  kazhdan-generators-resolve-all-fd-types: that bounds total off-isotypic transport; this observes that the individual type-pair blocks are Hilbert--Schmidt orthogonal and may therefore be partitioned into arbitrarily many decoded scale layers with no union bound.
  orthogonal-checksum-controls-only-mass-weighted-syndromes: that starts from separately authenticated scale projections and shows Pythagoras alone has no backward actuator; this obtains the entire orthogonal syndrome family canonically from one finite Kazhdan covariance packet.
  folner-multiplicity-atlases-have-vanishing-first-exit: that builds almost invariant finite-stencil multiplicity profiles and refutes contraction from coherent transport alone; this solves only square-function packing and leaves a non-Folner type-transition recurrence explicitly load-bearing.
---

ESTABLISHED.  Let `Gamma` have finite Kazhdan set `S` and squared-sum
constant `kappa>0`.  Let

```text
pi_j:Gamma -> U(H_j),              j=0,1,              (KSP1)
```

be finite-dimensional representations, with central isotypic projections
`P_theta^j`, and let `X:H_0->H_1` be a contraction.  For `sigma!=theta` put

```text
B_(sigma,theta)=P_sigma^1 X P_theta^0.                  (KSP2)
```

The blocks in `(KSP2)` are pairwise orthogonal in Hilbert--Schmidt inner
product.  Indeed distinct source labels give orthogonal right supports and
distinct target labels give orthogonal left supports.  Hence, for **any**
partition of the off-diagonal type pairs into finite or countable scale
layers

```text
{(sigma,theta):sigma!=theta}=disjointUnion_(n>=0) L_n,  (KSP3)
```

the syndromes

```text
s_n^2=sum_((sigma,theta) in L_n)||B_(sigma,theta)||_HS^2 (KSP4)
```

satisfy the exact Pythagorean identity

```text
sum_n s_n^2
 =sum_(sigma!=theta)||P_sigma^1 X P_theta^0||_HS^2.     (KSP5)
```

The twisted Kazhdan transport inequality `(KTR3)` therefore gives

```text
sum_n s_n^2
 <=kappa^(-2) sum_(g in S)||pi_1(g)X-X pi_0(g)||_HS^2. (KSP6)
```

All norms in `(KSP4)--(KSP6)` may use one common ambient normalized-HS
factor.  There is no dependence on the number of scales, representation
types, their dimensions, or their multiplicities.

Thus a finite Kazhdan covariance packet is already an authenticated
matrix-coordinate square function: once a decoder assigns every forbidden
type transition to its first-hit scale, all scale errors are blocks of the
same router and `(KSP6)` packs them without an address-length loss or a depth
union bound.  Combining `(KSP6)` with a recurrence

```text
a_n<=lambda a_(n+1)+C s_n,          lambda<1,           (KSP7)
```

immediately gives the HS floor of
`multiscale-square-function-checksum-forces-hs-floor`.

What remains is exactly `(KSP7)`, not square-function authentication.  It
requires the decoded type-transition graph to be non-Folner on the marked
carrier.  Mere coherent routers do not imply it: one isotypic packet with a
router in its multiplicity commutant has zero right side in `(KSP6)` and no
first exit, while `folner-multiplicity-atlases-have-vanishing-first-exit`
gives large finite-stencil versions of the same escape.  A positive group
construction must therefore combine exact Kazhdan packet decoding with a
branching/type transformation having a uniform isoperimetric inequality.
