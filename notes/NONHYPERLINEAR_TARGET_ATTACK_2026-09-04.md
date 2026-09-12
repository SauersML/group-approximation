# Nonhyperlinear-group attack: result, proof boundary, and remaining target

Date: 2026-09-04. Starting revision:
`9567b18f0bc63e5378f9779928dc7ec6b723c0fc`.

**The primary problem was not solved in this session.** No explicit group
was proved nonhyperlinear. The completed mathematics is a supporting
implication: the archive's qualitative matrix alpha-plane theorem already
implies its open linear inequality. The implication is proved from first
principles in the accompanying artifact; its application retains the
qualitative theorem as a named dependency. It is not a replacement claim
for `non-hyperlinear-group`.

## The target and the literature boundary

The requested witness must fail approximation in the **normalized
Hilbert--Schmidt norm**. Non-MF in the operator norm, nonsoficity,
non-residual-finiteness, or absence of exact finite-dimensional
representations does not establish that conclusion.

A current primary source checked on 2026-09-04 is Dogon--Vigdorovich,
[Hyperlinearity, stability and asymptotic spectral gap of higher rank lattices,
version 2](https://arxiv.org/html/2506.20843v2), dated 2026-06-23. Its
Question 1.4 and Corollary 1.5 give a conditional arithmetic construction:
an appropriate stability theorem for the modular-group amalgam would yield
a nonhyperlinear finite central extension. The paper does not prove that
stability assumption. The searches in this session did not locate an
unconditional discrete-group witness; this is a dated search result, not
an exhaustive certification of all current literature.

## Direct arithmetic attempt

A concrete candidate already in Cairn is

\[
\Lambda=\mathrm{SL}_3(\mathbb Z),\quad
\Gamma=\mathrm{SL}_3(\mathbb Z[1/11]),\quad
E=\Gamma*_{\Lambda}(\Lambda\times C_2).
\]

Equivalently, adjoin one involution s to Gamma with [s,Lambda]=1. Put
h=diag(11,1,1/11) and w=hsh^{-1}s. The word w is reduced in the
amalgam, because h is outside Lambda and s is outside the amalgamating
subgroup of Lambda times C_2. Thus w is nontrivial. The canonical group
trace satisfies tau(w)=0.

In a canonical tracial model set q=(1+s)/2. Then tau(q)=1/2, and direct
expansion gives

\[
\tau(w)=4\tau(qhqh^{-1})-1.
\]

Consequently the canonical model requires

\[
\tau(qhqh^{-1})=\tfrac14. \tag{A}
\]

In every exact finite-dimensional representation, the finite-dimensional
co-density assertion recorded in Cairn gives rho(Lambda)'=rho(Gamma)'.
The image of s therefore commutes with h. On a balanced sector this instead
forces

\[
\tau(qhqh^{-1})=\tfrac12. \tag{B}
\]

Turning (B) into an asymptotic theorem for the relevant arbitrary matrix
models would contradict (A) and solve the requested problem for E. This is
the substance of `sl3-outliers-carry-no-balanced-free-involution` and
related relative-commutant routes. The archive's large-prime exact-face
analysis confines possible canonical models to lattice outliers. That
analysis was consulted as an existing dependency, not independently
reproved here.

I investigated whether the finite-dimensional conclusion could be moved
through a Kazhdan projection or through tensor amplification. Neither
argument supplied the missing conclusion:

* Property (T) controls an actual unitary representation. The finite matrix
  coordinates here satisfy the lattice relations only approximately in
  normalized Hilbert--Schmidt norm. Identifying their low-energy spaces
  with commutants of honest finite-dimensional lattice representations
  requires the very correction theorem that remains open.
* The norm issue is substantive. For v_d=diag(-1,1,...,1),
  ||v_d-I||_2=2/sqrt(d), whereas Ad(v_d)-I has operator norm 2 on the
  Hilbert--Schmidt space, witnessed by the matrix unit e_12. Thus small
  normalized-HS relator error does not supply small operator-norm error
  for the conjugation action. This example calibrates the attempted
  inference; it is elementary prior knowledge, not a new obstruction claim.
* Tensor amplification can upgrade an already-established vanishing
  implication. It cannot establish the missing implication (A)->(B).
  Moreover, identity dilution changes the canonical actor trace. Applying
  the supporting tensor proof verbatim to a class defined by prescribed
  canonical moments would leave that class unless those moments were
  separately preserved or restored.

No proof of outlier exclusion was obtained.

## Direct Leavitt/atlas attempt

The route `nonhyperlinear-from-linear-energy-domination` targets the
explicit binary Leavitt unit group. Its missing input is

\[
\sum_{s\in\partial}\|\rho(z_s)U\|_2^2
\le C'\sum_{s\in S_0}\|\pi_U(s)-I\|_2^2,\qquad
U\in U(20160k), \tag{L}
\]

uniformly in k. Here S_0 consists of the 234 boundary words and the
interior separator associated with collision word 19243. The archive's
established 1/14 coercivity estimate compares the numerator with the two
raw covariance energies; it does not prove (L).

The tensor result in this session has a different numerator and different
symmetries. In (L), the numerator is a linearized group-algebra energy of
the chart unitary. It is not automatically a single real word correlation
whose tensor powers multiply. No affine action preserving this specific
atlas packet and distributing its errors was constructed. Substituting
the alpha-plane theorem into this route would therefore be unjustified.

The other direct attempt, Taylor expansion near the classical fold, also
does not bridge the gap: ||AB||_2<=||A||_op||B||_2 gives no uniform
quadratic remainder from small normalized-HS norms of A and B. For
example a rank-one projection has ||P||_2=d^{-1/2} but
||P^2||_2=d^{-1/2}, not O(d^{-1}). The known characteristic-two
countermodel further rules out simply dropping the interior separator.
These are checks of the exact missing implication, not new solutions.

No proof of (L), and no replacement all-dimension atlas separator, was
obtained.

## Completed supporting theorem

For D_b(x)=R_(x+b)R_x^*, write E_t for the slope-t energy. The short
estimate which enables the new argument is

\[
E_t\le2F\quad\text{for every slope},\qquad
\mathbb E_tE_t=F.
\]

Affine direct sums make each slope's quartic trace correlation constant
over basepoints and nonzero directions. Conjugate doubling makes these
correlations real. Tensoring then raises them to exact powers. Identity
dilution allows the input energy to be normalized without changing its
ratio to F. A concave-chord estimate prevents the amplified full energy
from vanishing.

The precise theorem is: if a uniform epsilon_*>0 satisfies

\[
I+A\le\varepsilon_*\Longrightarrow F\le\tfrac14,
\]

then

\[
F\le (I+A)/\varepsilon_*.
\]

The proof is in
`research/artifacts/alpha-plane-affine-tensor-linearization-2026-09-04.md`.
The scalar alpha-plane theorem and tensor amplification as a general
method are prior art. The contribution here is their particular averaged
matrix-test linearization, including the slope bound and affine
symmetrization. Global novelty is not certified.

There is a further exact identity for two honest additive actions:
R_x=X(x)Z(x) gives

\[
\|D_b(x)-D_b(x+a)\|_2
=\|X(a)Z(b)-Z(b)X(a)\|_2.
\]

Thus the untwisted two-matching commutator inequality follows without an
orbit-block choice. But this requires the two exact actions to exist on
one Hilbert space already.

That is why it does not solve the occurrence-compiler route. The node
`same-basis-rounding-interface-for-sparse-weyl-sampler` asks for a uniform
decoder from locally named observables into those exact actions, with
bounded dimension loss. The selected-label LDPC version further requires
quantitative exclusion of contextual noncommuting solutions. Neither
statement follows from an estimate whose inputs are coherent tables.

## Verification and graph scope

The standalone replay performs:

* 1,152 exact rational tensor-word evaluations for a noncommuting O(2)
  table over F_4, including repeated-point slopes;
* 36 complex-unitary table checks over F_4, F_8 and F_16, in dimensions
  1, 2, 3 and 5;
* nine pairs of exact additive actions checking the product-table identity.

The largest affine correlation discrepancy in the floating-point checks
was 2.89e-15. Every amplification bound passed. These are sanity checks
for the finite identities; the written proof establishes the implication.
The qualitative premise and nonhyperlinearity cannot be established by
these finite experiments. No Lean verification is claimed.

The new Cairn route requires the existing qualitative matrix theorem.
Its independent proof route goes through scalar alpha-plane soundness,
so the pre-existing converse linear-to-qualitative route is not being
used circularly. The primary `non-hyperlinear-group` claim remains open.

The starting archive already reports 55 unrelated Cairn errors, including
schema errors and historical git-pinned artifacts unavailable in a ZIP.
Replaying the graph with and without the new route and claim edit introduced
no new errors. Its status calculation changes the linear-inequality claim
from OPEN to ESTABLISHED, marks the new route COMPLETE, and leaves
`non-hyperlinear-group` OPEN. A global green Cairn build is not claimed.
The commit is limited
to this proof, its replay, the supporting route/claim, and this account of
the main-target attempt; it does not relabel unsolved main-target inputs.
