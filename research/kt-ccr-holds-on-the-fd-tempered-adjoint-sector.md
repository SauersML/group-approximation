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

More quantitatively, let `z_FD` be the orthogonal projection onto the maximal
FD-tempered subrepresentation of `Ad(sigma)` on `L^2(M)`.  For every
`x in sigma(Lambda)' cap M`,

~~~text
dist_2(x,L^2(sigma(Gamma)' cap M))
 <=||(1-z_FD)x||_2.                                      (FDT3b)
~~~

Thus a commutant defect of size `c` forces at least `c` of genuinely
non-FD-tempered adjoint mass; it cannot be hidden in the compact or any other
FD-approximable summand.

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

For a trace-faithful matrix-ultraproduct `sigma=[pi_n]`, the enemy is
more specific at the pointed-vector level.  The adjoint lifts

~~~text
beta_n(g)=Ad(pi_n(g)) in U(d_n^2)
~~~

are trace-faithful microstates because

~~~text
tr_(d_n^2)(Ad(U))=|tr_(d_n)(U)|^2.                       (FDT6)
~~~

A failure of (CCR) supplies distinguished unit vectors
`xi_n=vec(v_n)`, where `v_n` are op-norm-one unitaries, such that the
`Lambda`-generator displacement tends to zero while one
`Gamma`-displacement stays positive.  Equivalently, one of the
finite-dimensional-radical elements `a_gamma` acts nontrivially on this
pointed ultralimit of adjoint microstates.

This pointed conclusion must not be confused with nonvanishing in the
tracial matrix ultraproduct of the `d_n^2 by d_n^2` superoperators.  A
vanishing normalized-rank superoperator can still move one distinguished
unit vector.  The op-norm-one matricial origin of `xi_n` is therefore
load-bearing.

Robust `(T;FD)_rob` supplies stable low-spectrum control for the approximate
adjoint coordinates.  It does not force the low-spectrum vectors of the
special form `vec(v_n)` to be fixed by `gamma`.  The remaining
bounded-vector estimate is exactly

~~~text
max_(s in S)||beta_n(s)vec(v_n)-vec(v_n)|| ->0
and ||v_n||_op=1
imply
||(beta_n(gamma)-I)vec(v_n)|| ->0.                       (FDT7)
~~~

Here vector norms are the normalized Hilbert--Schmidt norms of the matrices
`v_n`.  Proving `(FDT7)` for the Kun--Thom actor proves (CCR).  Refuting it
produces a non-FD-tempered spherical module of the special pointed
adjoint-lift form.  Nothing here establishes `(FDT7)`, (CCR), or a
nonhyperlinear group.


The reversible two-by-two linearization in
`fdt7-is-balanced-bernoulli-projection-transfer` sharpens the special
form of the pointed vectors.  It turns each unitary `v_n` into an exact
trace-half projection `P(v_n)`, preserves every normalized-HS actor defect,
and converts commutator displacement by the exact factor `1/2`.  Conversely,
`v_n=2p_n-I` recovers a self-adjoint unitary from any trace-half projection.
Thus Powers--Størmer, polar decomposition, and spectral cutting do not by
themselves close `(FDT7)`.  Nor does the trace-half rank remove the pointed
firewall: the rank-one support of `P(v_n)` in the adjoint Hilbert space has
normalized trace `1/(2d_n)^2`.  Left multiplication by `P(v_n)` is a
trace-half superoperator projection, but its displacement identity recreates
the same FDT7 witness for the second adjoint representation.  This
self-similar lift supplies no tracial mass for the original
finite-dimensional-radical operator.

That claim also gives an exact finite-tracial boundary model.  The Bernoulli
crossed product for the action of `G` on `G/Lambda` contains a trace-half
projection fixed by `Lambda` and moved by every
`gamma in Gamma minus Lambda`; its orbit signs span
`ell^2(G/Lambda)`, necessarily a non-FD-tempered `G`-module here.
Writing
`W=(direct_sum_(G/Lambda) C_2) semidirect G`, the crossed product is
exactly `L(W)`.  Hence hyperlinearity of `W` would turn this profile into
a literal FDT7 and (CCR) counterexample.  The present hypotheses do not
supply such a generalized coset-wreath model, so this remains conditional.
At `q=2`, `coset-wreath-wall-survives-full-commutant-corners` further
proves that `L(W)` is a factor and every nonzero full relative-commutant
corner of a hypothetical embedding preserves the canonical trace and the
squared wall displacement `1/2`.  Thus multiplicity corners cannot weaken
the conditional refuter.
It proves that the missing input must use matrix approximability, and that
tensoring with the inverse or passing to the adjoint action alone is unsafe
because it erases scalar-phase commutators.

DERIVATION
fd-radical-kazhdan-projection-ccr-proof


**Regular-mask realization of the pointed firewall (2026-08-31).**
`kt-regular-congruence-mask-removes-trace-faithfulness-from-the-commutant-wall`
shows that the warning after (FDT6) is quantitatively sharp in the canonical
KT sector.  Tensor an arbitrary multiplicity microstate with the exact
regular Steinberg congruence carrier of dimension `D_n`.  A fiber witness
`I_(D_n) tensor x_n` has unchanged normalized `2`-norm and unchanged
commutator displacement, while its entire carrier inside the adjoint Hilbert
space has dimension ratio exactly `D_n^(-2)->0`.  The physical leak is
macroscopic but its adjoint spectral band has vanishing normalized rank.
Therefore no normalized low-band density estimate can prove (FDT7); the
pointed op-norm-bounded vector condition is genuinely load-bearing.
