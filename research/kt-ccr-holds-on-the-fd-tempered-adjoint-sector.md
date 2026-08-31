---
rg: 2
id: kt-ccr-holds-on-the-fd-tempered-adjoint-sector
kind: claim
title: Kun--Thom commutant collapse holds on the FD-tempered adjoint sector
distinct_from:
  ccr-for-coordinate-collapsing-models: that assumes genuine coordinate representations and uses image collapse level by level; this works for an arbitrary ambient representation whenever the selected adjoint cyclic module is weakly contained in genuine finite-dimensional representations.
  fd-invisibility-of-compression: that proves equality of compressed and uncompressed images in every genuine finite-dimensional representation; this promotes exactly that fact through weak containment using the Kazhdan projection.
  el-r-polynomial-robust-spectral-gap: that controls low spectrum for finite-dimensional almost representations; this identifies the additional finite-dimensional-radical element which robust spectral gap does not annihilate.
  ccr-hard-instance-subfactor-reducible: that rules out irreducible-subfactor flattening at a nontrivial witness; this proves collapse on a large representation-theoretic sector without irreducibility.
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**ESTABLISHED SECTOR THEOREM; FULL (CCR) OPEN.**  Let
`Lambda subset Gamma subset G`, suppose `Lambda` has property `(T)`, and
assume

~~~text
rho(Lambda)=rho(Gamma)                                  (FDT1)
~~~

for every finite-dimensional unitary representation `rho` of `G`.  Let
`pi_FD` be the direct sum of all finite-dimensional unitary representations
of `G`.

If `theta:G->U(H)` is weakly contained in `pi_FD`, then

~~~text
Fix(theta(Lambda))=Fix(theta(Gamma)).                    (FDT2)
~~~

The inclusion from right to left is automatic.  The reverse follows
quantitatively from one Kazhdan pair: a finite-dimensional vector which is
`epsilon`-invariant under a Kazhdan generating set of `Lambda` is within
`epsilon/kappa` of the common fixed space in `(FDT1)`.  Fell approximation
then sends every exactly `Lambda`-fixed vector of `theta` into the
`Gamma`-fixed space.

Apply this to the Kun--Thom compressor
`Lambda=t Gamma t^(-1) subset Gamma`.  Property `(T)` is established, and
`fd-invisibility-of-compression` supplies `(FDT1)`.  For any homomorphism

~~~text
sigma:G->U(M)
~~~

into a finite tracial von Neumann algebra, put
`Theta=Ad(sigma)` on `L^2(M)`.  If
`x in sigma(Lambda)' cap M` and the cyclic representation

~~~text
H_x=closure span{Theta(g)x:g in G}                      (FDT3)
~~~

is weakly contained in `pi_FD`, then `x in sigma(Gamma)' cap M`.
Consequently (CCR) holds on the entire FD-tempered part of the adjoint
representation.

There is an exact C-star formulation.  Let `p_Lambda` be the Kazhdan
projection and let `u_gamma` be the canonical group unitary.  For every
`gamma in Gamma`,

~~~text
a_gamma=(u_gamma-1)p_Lambda                              (FDT4)
~~~

is killed by every finite-dimensional representation of `G`.  Thus
`a_gamma` lies in the finite-dimensional radical ideal of `C^*_max(G)`.
For a `Lambda`-fixed vector `xi`,

~~~text
theta(a_gamma)xi=theta(gamma)xi-xi.                      (FDT5)
~~~

Weak containment in `pi_FD` kills the whole ideal and proves `(FDT2)`.

This also sharpens the shape of any counterexample.  If

~~~text
sigma(Lambda)' cap M not-subset sigma(Gamma)' cap M,
~~~

then there is a unitary `v` in the left relative commutant but not the
right one, and the cyclic module `H_v` is not FD-tempered.  The unitary can
be chosen without loss: take a self-adjoint contraction outside the smaller
commutant and use
`v=a+i sqrt(1-a^2)`; conditional expectation shows that its distance from
the smaller commutant is at least the distance of `a`.

For a trace-faithful matrix-ultraproduct `sigma=[pi_n]`, the enemy is even
more specific.  The adjoint lifts

~~~text
beta_n(g)=Ad(pi_n(g)) in U(d_n^2)
~~~

define another trace-faithful matrix-ultraproduct representation because

~~~text
tr_(d_n^2)(Ad(U))=|tr_(d_n)(U)|^2.                       (FDT6)
~~~

A failure of (CCR) therefore makes one of the finite-dimensional-radical
elements `a_gamma` visible in a trace-faithful representation built from
adjoint lifts of the original microstates.  This is strictly stronger than
saying that some abstract representation detects the FD radical.

Robust `(T;FD)_rob` supplies the stable low-spectrum projection representing
`p_Lambda` for the approximate adjoint coordinates.  It does not force
`(u_gamma-1)p_Lambda` to vanish.  That last product is exactly the
compression-collapse term.  Hence robust spectral gap, finite-dimensional
image collapse, and the op-norm-one unitary reduction leave one sharply
named requirement:

~~~text
trace-faithful adjoint-lift microstates annihilate a_gamma.             (FDT7)
~~~

Proving `(FDT7)` for the Kun--Thom actor proves (CCR).  Refuting it produces
a non-FD-tempered spherical module of the special adjoint-lift form.
Nothing here establishes `(FDT7)`, (CCR), or a nonhyperlinear group.

DERIVATION
fd-radical-kazhdan-projection-ccr-proof
