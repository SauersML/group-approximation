# STW LXIII: literature and proof-boundary audit (2026-08-30)

## Question

Problem LXIII of Schafhauser--Tikuisis--White asks whether, for every unital
C-star algebra `B`, every two unital embeddings `Z -> B` are approximately
unitarily equivalent, or even asymptotically unitarily equivalent.  The cached
v2 text at `tmp/pdfs/stw99.txt`, lines 3079--3109, still states the problem and
records the known `Z`-stable and stable-rank-one/Cuntz-semigroup cases.

## Time-sensitive audit

The following primary sources were checked by exact-title and exact-phrase
searches, followed by inspection of the theorem statements.

1. T. Amrutam, D. Gao, S. Kunnawalkam Elayavalli and G. Patchell,
   *Strict comparison in reduced group C-star algebras*, arXiv:2412.06031,
   published in Inventiones in 2025,
   <https://arxiv.org/abs/2412.06031>.  Its introduction explicitly says that
   it remains open whether a unital C-star algebra can have two inequivalent
   unital embeddings of `Z`.  Its Theorem C proves uniqueness for a large new
   family of reduced group C-star algebras.
2. I. Vigdorovich, *Structural properties of reduced C-star algebras
   associated with higher-rank lattices*, arXiv:2503.12737,
   <https://arxiv.org/abs/2503.12737>.  This adds higher-rank reduced group
   C-star algebras to the positive stable-rank-one/strict-comparison family;
   it does not treat arbitrary codomains.
3. S. Hua and S. White, *Uniqueness for embeddings of nuclear C-star
   algebras into type II_1 factors*, arXiv:2601.08779,
   <https://arxiv.org/abs/2601.08779>.  Theorem 5.2 proves norm approximate
   unitary equivalence for faithful unital nuclear maps from a separable
   unital nuclear UCT algebra into a II_1 factor when the traces agree.
   Applied to `Z`, this closes every II_1-factor codomain.  Appendix A treats
   type III: Theorem A.1 says that for a separable unital exact domain and a
   type-III factor with separable predual, two unital nuclear maps are norm
   approximately unitarily equivalent exactly when their kernels agree.  It
   is derived from Kirchberg's asymptotic uniqueness theorem for simple
   purely infinite codomains (Theorem A.2), which imposes no separability
   hypothesis on the codomain.  Theorem A.1 does not require the UCT.
4. Q. Li, D. Hadwin, and W. Liu, *Approximate Equivalence in von Neumann
   Algebras*, *Operators and Matrices* 17 (2023), 1--23,
   DOI 10.7153/oam-2023-17-01; arXiv:2008.06619,
   <https://arxiv.org/abs/2008.06619>, supplies two broader rank theorems
   relevant to `Z`.  In the published numbering, Theorem 4 says that for an
   algebra relatively LF in its bidual and an arbitrary finite von Neumann
   target, equality after the center-valued trace is equivalent to norm
   approximate unitary equivalence.  Theorem 8 says that equal elementwise
   von Neumann rank implies norm approximate unitary equivalence, with
   compact-relative control, for maps from a separable unital ASH algebra
   into a semifinite von Neumann algebra acting on a separable Hilbert space.
   These theorems do not state LXIII for general C-star codomains.  The new
   graph route verifies their hypotheses for arbitrary Jiang--Su embeddings
   and proves the needed support-rank collapse on the properly infinite
   central piece.
   Their factor-specific Corollary 1 has a broader cardinal scope than
   Theorem 8: for a separable unital ASH domain and a sigma-finite
   type-II-infinity factor, equal elementwise von Neumann rank implies norm
   approximate unitary equivalence modulo the finite-projection ideal.  It
   does not assume a separable Hilbert-space action or separable predual.
5. D. Hadwin, *Nonseparable approximate equivalence*, Transactions of the
   AMS 266 (1981), 203--231, DOI 10.1090/S0002-9947-1981-0613792-6.
   Theorem 2.5 classifies nondegenerate representations of an arbitrary
   C-star algebra on an arbitrary Hilbert space up to norm approximate
   unitary equivalence by equality of the Hilbert-space ranks of every image
   element.  Hua--White restate this exact unrestricted formulation in their
   introduction.  The new graph route checks its cardinal-rank hypothesis
   for Jiang--Su embeddings.
6. E. Blanchard and E. Kirchberg, *Non-simple purely infinite C-star
   algebras: the Hausdorff case*, Journal of Functional Analysis 207 (2004),
   461--513, DOI 10.1016/j.jfa.2003.06.008,
   <https://hal.science/hal-00922863/document>.  The final paragraph of its
   introduction states that an AW-star algebra is type III exactly when it
   satisfies their pure-infiniteness definitions.  More precisely, AW-star
   algebras have real rank zero, and the cited Kirchberg--Rordam chain plus
   their Theorem 4.17 identifies this with strong pure infiniteness.  No
   separability, factoriality, or sigma-finiteness is assumed there.
7. J. Gabe, *Classification of O-infinity-stable C-star algebras*, Memoirs
   AMS 293 (2024), no. 1461; arXiv:1910.06504,
   <https://arxiv.org/abs/1910.06504>.  Theorem 9.7 makes every nuclear map
   from a separable exact domain into a strongly purely infinite codomain
   strongly O-infinity-stable.  Theorem B classifies nuclear, strongly
   O-infinity-stable, full maps from a separable algebra into a sigma-unital
   algebra by nuclear KK, and its unital clause gives asymptotic unitary
   equivalence.
8. Targeted arXiv searches through 2026-08-30 for the exact combinations
   "Jiang--Su", "embedding", "approximately unitarily equivalent", and
   "Problem LXIII" found no later claim resolving the arbitrary unital
   codomain question.  The May 2026 paper arXiv:2605.22585 concerns unitary
   orbits and Wasserstein geometry in regular targets, not LXIII.
9. G. A. Elliott and L. Zsido, *Almost uniformly continuous automorphism
   groups of operator algebras*, Journal of Operator Theory 8 (1982),
   227--277,
   <https://jot.theta.ro/jot/archive/1982-008-002/1982-008-002-004.pdf>.
   In the proof of Lemma 4.2, page 270, they take a maximal orthogonal family
   of central projections whose corners have separable predual and prove
   that its sum is one.  On page 275 they record the exact consequence that
   every countably generated W-star algebra is a direct product of W-star
   algebras with separable predual.
10. A. Ciuperca, T. Giordano, P. W. Ng and Z. Niu, *Amenability and
   uniqueness*, Advances in Mathematics 240 (2013), 325--345;
   arXiv:1207.6741, <https://arxiv.org/abs/1207.6741>.  In the proof of
   Proposition 4.3 they make the same reduction: after replacing the target
   by the W-star algebra generated by countably many map and rank witnesses,
   they state that it is a direct product of von Neumann algebras with
   separable predual.  Their proposition concerns weak-star approximate
   equivalence, so the new graph proof imports only this structural step and
   obtains norm equivalence from the stronger coordinate theorem.
11. I. Kaplansky, *A theorem on rings of operators*, Pacific Journal of
    Mathematics 1 (1951), 227--232.  Theorem 1 proves strong density of the
    norm unit ball of a strongly dense star algebra in the norm unit ball of
    its closure.  Applied to bounded self-adjoint logarithms and exponentials,
    it gives strong density of `U(B)` in `U(B**)` for unital `B`.  The new
    convex-return route uses only this density theorem and Hahn--Banach; it
    does not infer norm density of unitary groups.
12. L. Robert, *Classification of inductive limits of 1-dimensional NCCW
    complexes*, Advances in Mathematics 231 (2012), 2802--2836, DOI
    10.1016/j.aim.2012.07.010; arXiv:1007.1964.  Theorem 1.0.1 classifies
    homomorphisms from sequential limits of one-dimensional NCCW complexes
    with trivial `K_1` into stable-rank-one targets by `Cu_tilde`.  Section
    6.3 computes `Cu(Z)=N disjointUnion (0,infinity]`.  Proposition 6.3.1
    gives an application with a unique 2-quasitrace; the new route removes
    uniqueness only for comparison of two already existing unital embeddings
    by checking equality on every soft class directly.

## Trust boundary

This is a targeted, not bibliometrically exhaustive, audit.  Non-discovery is
not a proof of openness.  The strongest direct status evidence is the explicit
open-problem statement in the published 2025 paper, combined with inspection
of the scopes of the relevant 2026 results.  No literature assertion is used
as a premise in any graph route added with this artifact.

## New internal deductions recorded in the graph

The graph additions isolate seventeen facts which do not depend on the literature
audit.

1. Every possible counterexample is invisible to `KK`, unit-preserving
   K-theory, bounded traces, and ideal maps.  Cuntz-semigroup data is the first
   standard invariant in which the two maps can still separate.
2. A common unital copy of `Z` in the joint relative commutant inside the
   sequence algebra is enough for approximate uniqueness.  This is strictly a
   pairwise condition; it does not assume that `B` is `Z`-stable.
3. Approximate equivalence upgrades to asymptotic equivalence whenever
   sufficiently central transition unitaries can be contracted through
   controlled approximately central paths.  The proof gives the exact
   concatenation mechanism and exposes the remaining obstruction as topology
   of approximate relative commutants, rather than K-theory or traces of the
   embeddings.
4. Every finite von Neumann algebra, without a countability assumption, and
   every separably acting semifinite von Neumann algebra is a positive
   codomain.  On a finite algebra, the center-valued trace of every Jiang--Su
   embedding is forced to be `tau_Z(.)1`.  On a properly infinite semifinite
   central part, fullness forces the support of every nonzero image element
   to be a full properly infinite projection, hence equivalent to the unit.
   Thus every possible counterexample becomes approximately unitarily
   equivalent in every finite shadow and every separably acting semifinite
   shadow.
5. Hua--White Theorem A.1 closes the separable-predual type-III factor case.
   Central disintegration and measurable selection extend this to every
   separable-predual type-III algebra.  Combining its unitary with the
   semifinite-central-summand unitary proves uniqueness in every separably
   acting von Neumann algebra.  Thus no counterexample can be detected in any
   separably acting von Neumann shadow, regardless of type.
6. The separable-predual restriction can be weakened to sigma-finiteness for
   type-III factors.  In such a factor equivalence of nonzero projections
   gives `y*ay=1` for every nonzero positive `a`, and puts an infinite
   projection in every nonzero hereditary subalgebra.  Hua--White Theorem A.2
   then applies because the two Jiang--Su embeddings have equal nuclear KK
   class.  This gives asymptotic uniqueness in every sigma-finite type-III
   factor, and product closure gives approximate uniqueness for arbitrary
   products of such factors.  The argument does not extend to a
   non-sigma-finite factor, where projection cardinalities can differ and
   proper norm ideals can occur.
7. Type-I factors admit a different cardinal argument.  Fullness of every
   nonzero Jiang--Su element makes the ambient Hilbert space embed into
   finitely many copies of its image range.  Infinite-cardinal arithmetic
   forces that range to have the full Hilbert dimension, so Hadwin's theorem
   gives uniqueness in `B(H)` for arbitrary `H`.  Product closure extends
   this to every atomic type-I von Neumann algebra.
8. The sigma-finite restriction on type III can in fact be removed without
   repeating the false projection-cardinality argument.  Arbitrary type-III
   von Neumann algebras are strongly purely infinite as C-star algebras.
   Although they can have proper norm ideals, a unital map from the simple
   algebra `Z` is full.  Gabe's map-level theorem and the equality of the two
   nuclear KK classes therefore give asymptotic unitary equivalence for every
   type-III von Neumann codomain, with arbitrary center and cardinality.
9. Independently, every two Jiang--Su embeddings into every von Neumann
   algebra have equal elementwise von Neumann rank and send each nonzero
   element to a norm-full element.  The finite central part is controlled by
   its center-valued trace; on the complementary central part, finite-sum
   fullness makes each image support properly infinite and equivalent to the
   central unit.  Thus the unresolved von Neumann lane has no cardinal-rank
   or norm-ideal obstruction.
10. Li--Hadwin--Liu's factor-specific corollary, combined with the global
   rank collapse, closes every sigma-finite type-II-infinity factor even when
   its predual is nonseparable.  Product closure also closes arbitrary
   products of these factors.  This is a direct rank-theorem route for a
   large nonseparably acting positive class.
11. In fact every von Neumann target is positive.  The W-star algebra
   generated by the two separable ranges is countably generated, hence is a
   direct product of separable-predual W-star algebras by Elliott--Zsido.
   Separably acting uniqueness applies coordinatewise, and the product norm
   assembles the coordinate unitaries with one common finite-set tolerance.
   This bypasses nonstandard central integration entirely.  The conclusion
   is norm approximate uniqueness; uniform asymptotic paths are not inferred
   from the product argument.
12. The remaining return problem admits an exact relative-sequence-algebra
    formulation.  For `D=M_2(B_infinity) intersect diag(phi,psi)(Z)'`, the
    two coordinate projections are equivalent exactly when `phi` and `psi`
    are approximately unitarily equivalent.  They are always equivalent in
    the analogous algebra over `B**`.  Hence every counterexample is exactly
    a failure of this canonical inclusion to reflect that projection
    equivalence.  Injectivity on `K_0` plus projection cancellation in `D`
    is a sufficient return theorem; stable rank one is required of `D`, not
    merely of `B`.
13. There is also an unconditional norm-level return short of one unitary:
    each embedding lies in the point-norm closed convex hull of the other's
    unitary orbit in `B`.  Kaplansky density returns the bidual unitary only
    strongly, while Hahn--Banach converts that weak convergence into norm
    approximation after finite convexification.  Deconvexifying those
    random-unitary averages is the precise step this argument does not solve.
14. The Cu return theorem yields a wider positive class than Robert's stated
    unique-quasitrace application.  If the unital target has stable
    rank one, a nonempty normalized 2-quasitrace space and strict comparison
    by that whole space, all quasitraces restrict along either embedding to
    the unique normalized trace of `Z`.  Compact Cu classes are fixed by the
    unit.  For a soft class `r`, strict comparison applies to every
    `r_k<r`; taking suprema removes the deliberate strict gap.  This proves
    equality on all of `Cu(Z)` without assuming simplicity or a unique
    quasitrace.
    More generally, Robert's exact map theorem says that for every unital
    stable-rank-one target, with no other target regularity assumption,
    equality of the two `Cu` maps is equivalent to approximate unitary
    equivalence of the Jiang--Su embeddings.
15. A stationary simple AF algebra with incidence matrix
    `[[2,1],[1,2]]` shows why deconvexification cannot follow from generic
    regularity.  Rank-one projections in the two stage summands have equal
    unique trace but distinct persistent `K_0` classes.  They and their
    complements become equivalent in the bidual, hence define exactly
    conjugate maps `C^2->B**`, but their maps into `B` are not approximately
    unitarily equivalent.  Thus even nuclearity, exactness, local reflexivity,
    real rank zero, stable rank one and full corners do not constitute a
    domain-independent bidual-return theorem.
16. In stable rank one, universal von Neumann uniqueness and Robert's exact
    Cu map theorem combine into a direct descent criterion: injectivity of
    `Cu(B)->Cu(B**)` implies Jiang--Su embedding uniqueness in `B`.  Any
    stable-rank-one counterexample must make this map identify two distinct
    classes which occur as values of the two actual Jiang--Su `Cu` maps.
    Arbitrary noninjectivity of the bidual Cu map is not claimed sufficient
    to construct a counterexample.
17. If a unital codomain has no tracial state, its bidual has no finite
    central summand.  Every nonzero spectral cut coming from a Jiang--Su
    matrix is norm-full, and finite fullness forces its bidual support to be
    equivalent to the properly infinite unit.  Consequently
    `Cu(Z)->Cu(B**)` collapses every nonzero compact and soft class to one
    class.  This identifies the exact soft-scale information lost in the
    traceless W-star shadow without claiming that `Cu(Z)->Cu(B)` retains it.
