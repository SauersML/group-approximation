# Review of the rational AH counterexample and tracial selfless K-stability

Date: 5 September 2026. Internal mathematical review by the coordinating
agent, following distinct construction attacks by separate agents.
The proof checks below are mathematical checks; Cairn validation checks
the research graph and does not constitute formal proof verification.

## 1. Rationally K-stable AH algebra with an integral torsion kernel

The reviewed [full manuscript](stw59-rational-k-stability-torsion-euler-tower-2026-09-05.md)
constructs a simple unital separable nuclear stably finite monotracial
AH algebra \(A\) which is rationally K-stable and satisfies
\[
 \ker\bigl(U(A)/U_0(A)\longrightarrow K_1(A)\bigr)=\mathbb Z/2.
\]
Its matrix algebra \(M_2(A)\) is K-stable. The whole component group
is not identified, and \(K_1(A)\) is not claimed to vanish.

The review checked the following decisive points.

- The one-line gauge fibration and its stable range apply to finite
  CW bases with torsion. The exact sequence computes the stabilization
  kernel without requiring the stable \(K_1\) group to be zero.
- The Euler formula is derived integrally from the clutched virtual
  bundle over \(S^2\times X\), using Newton classes and the integral
  splitting principle. A rational Chern-character calculation alone
  would not suffice on these bases.
- Every stage bundle is four copies of another bundle. The mod-two
  Euler expression is therefore a fourth power for every virtual
  bundle, including torsion classes. On the initial \((\mathbb{RP}^2)^4\)
  factor every positive-degree monomial has zero fourth power.
  The resulting top-degree expression vanishes. Top integral cohomology
  is \(\mathbb Z/2\) and embeds under coefficient reduction, so the
  integral Euler map is zero.
- Integral relative Thom-class multiplicativity sends the old top
  obstruction to its product with the new tautological top Chern class.
  This preserves the \(\mathbb Z/2\) generator without orientability
  of the projective bases. On components the actual evaluation block
  can be contracted, so the actual maps preserve the obstruction.
- Simplicity follows from dense projected evaluation tails; the trace
  maps have an exact one-half contraction. Finite-stage detection of
  both components and stable classes proves that the entire limit
  kernel, rather than only a subgroup, is \(\mathbb Z/2\).
- The rational argument concerns the actual evaluation maps. The
  fiberwise construction in Klein--Schochet--Smith, Lemma 9.1 and
  Corollary 9.2, commutes with restriction to a point. Proposition 5.1
  rationalizes the mapping-space component, and rational acyclicity
  makes evaluation an isomorphism on positive homotopy groups.
  Increasing ranks then give the actual adjacent matrix isomorphisms.

The primary [Klein--Schochet--Smith manuscript](https://arxiv.org/pdf/0811.0771v4)
was inspected at the stated results, including the fiberwise proof.
The [separate literature audit](rational-k-stability-ah-literature-boundary-2026-09-05.md)
fixes Vaidyanathan's AH question and the compact-building-block
convention. The resulting negative answer holds even for simple unital
algebras. No external acceptance or publication priority is inferred.

## 2. Full K-stability for the tracial selfless subclass

The reviewed [full manuscript](stw58-tracial-selfless-k-stability-free-smoothing-2026-09-05.md)
proves K-stability of every tracial selfless C*-algebra in all degrees
and matrix sizes, without nuclearity, exactness, or separability.

The review checked the actual based homotopy
\[
 U_s(x)=u(x)\exp\!\left(is\,t(x)\frac{1+\operatorname{Re}w}{2}\right)
\]
in the existential free extension. Here \(w\) is free Haar and \(t\)
vanishes exactly at the sphere basepoint. Off that point the exponential
has atomless distribution and is free from \(u(x)\). At the basepoint
the product is one. Thus the fixed spectral point \(-1\) has zero
mass throughout the parameter space.

Robert's Theorems 2.6(iv), 3.1(ii), 4.2, and 4.3 were checked in the
[primary manuscript](https://arxiv.org/pdf/2309.14188). They supply
existentiality, free-product permanence, uniqueness of the normalized
2-quasitrace rather than merely the trace, and matrix permanence.
Gould's [Corollary 3](https://arxiv.org/pdf/2606.09654v2) supplies purity.
The atom implication in Belinschi--Bercovici--Ho's
[Lemma 3.1(1)](https://arxiv.org/pdf/2205.07114) was checked, including
its applicability without nonzero first moments. A point-mass first
factor is treated directly by rotation.

Fixed-point spectral squeezing and the already reviewed small-support
theorem therefore contract each stably null image in the extension.
The finite-data existential reflection proof was checked separately:
both approximate-unitarity relations, simplex edge control, polar
vertex repair, barycentric polar interpolation, the exact boundary
collar, and final based normalization are supplied explicitly.
This reflects an actual contraction, not just a stable K-class.
Reviewed stable surjectivity and matrix selflessness complete the proof.

This is a complete theorem for the stated subclass. General LVIII
remains open in the graph because pureness alone does not provide the
existential free extension used by the proof.

## 3. Supporting advances and limits

The [canonical splitting](stw58-canonical-small-support-stable-splitting-2026-09-05.md)
identifies the stable summand with the classes admitting arbitrarily
small quasitrace support. Its support-size gap follows by comparing
any representative below the contraction threshold with a sufficiently
small canonical lift. Naturality includes supported maps of nonunital
homomorphisms and hence matrix corners.

The [fixed spectral-point theorem](stw58-fixed-spectral-point-global-localization-2026-09-05.md)
uses upper semicontinuity of atom mass on the compact parameter and
quasitrace space to choose a single arc. The normalized degree-one
circle function and degree-zero ratio give a genuine based homotopy.
The scalar example correctly shows why this criterion alone cannot
localize every original representative.

The [cutoff restriction boundary](stw99-lxxvi-dense-cutoff-restriction-and-local-control-2026-09-05.md)
proves norm density as a consequence of CEI prior art, with an explicit
approximate-polar estimate. Its CAR example independently disproves
local control near a prescribed larger lift. The diagonal expectation
estimate and its \(3/4\) lower bound were checked. This does not
disprove changing-cutoff or fixed-uniform-error parameterized schemes.

## 4. Status and validation

The named-question count is now **two internally reviewed full-answer
manuscripts**: STW LIX and Vaidyanathan's rational-versus-integral AH
extension question. The new AH construction is not counted a second
time as another LIX solution. The tracial selfless theorem settles a
subclass of LVIII and is not counted as a full solution of LVIII.
General LVIII, LXI, and LXXVI remain open in the graph.

The canonical-splitting and literature-boundary batch was committed
as `460247fec` and pushed. Its MSI Cairn closure check and preview
both passed on 104 nodes (54 claims and 50 routes). The first check
requested an explicit Attempts section on the new open AH root; that
section was added before the successful check and commit.

The full-theorem batch is subject to its own final Cairn and whitespace
checks. No local code or builds were run, and no MSI job is kept alive
between these short validation invocations.
