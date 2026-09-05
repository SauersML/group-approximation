---
rg: 2
id: stw99-problem-lviii-pure-k1-bijective
kind: claim
title: Pure C*-algebras are K1-bijective and K-stable (STW Problem LVIII, Thiel)
root: true
artifacts:
  - research/artifacts/stw99-k1-kk-cluster-2026-08-30.md
  - research/artifacts/stw58-simple-pure-k1-bijectivity-audit-2026-08-30.md
  - notes/stw58-coefficient-unitary-stabilization-2026-09-05.md
  - notes/stw58-soft-module-compression-attempt-2026-09-05.md
  - research/artifacts/stw58-local-factorization-and-overlap-cancellation-2026-09-05.md
  - research/artifacts/stw58-overlap-corrected-word-spaces-and-homotopy-lifting-2026-09-05.md
  - research/artifacts/stw58-degree-one-primary-citation-audit-2026-09-05.md
  - research/artifacts/stw58-compatible-split-stable-surjectivity-2026-09-05.md
  - research/artifacts/stw58-small-projection-support-kernel-contraction-2026-09-05.md
  - research/artifacts/stw58-soft-support-orthogonal-reservoir-contraction-2026-09-05.md
  - research/artifacts/stw58-small-quasitrace-support-kernel-contraction-2026-09-05.md
---

**Problem LVIII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Thiel).  Is every pure C\*-algebra `K_1`-bijective, or even
`K`-stable?  Jiang: `Z`-stable algebras are `K`-stable; STW flag the
non-nuclear case as the interesting one, where pureness does not give
`Z`-stability.

## Established simple slice

Every unital simple pure C-star-algebra is already `K_1`-bijective
(`stw58-simple-pure-k1-bijective`).  Lin's published pure dichotomy puts it
in one of two branches:

- if it has stable rank one, Rieffel's Theorem 10.12 gives the full
  isomorphism `U(A)/U_0(A) -> K_1(A)`, not merely injectivity;
- if it is purely infinite, Cuntz's nonstable K-theory gives surjectivity for
  properly infinite algebras and injectivity in the simple purely infinite
  case.

Thus neither injectivity nor surjectivity remains in the unital simple slice.

## Remaining frontier

The `K_1`-bijectivity question remains for non-simple pure algebras and for
any nonunital formulation not covered by the stated convention.  The stronger
`K`-stability question remains even for simple pure algebras.

The stable-surjectivity half is now established in every positive
degree for the unital simple finite pure slice by
`stw58-simple-finite-pure-split-stable-surjectivity`. A single full
hereditary endpoint matrix piece gives compatible group sections
of every map `pi_k U(M_m(B)) -> K_(k+1)(B)` for fixed k>=1.
The remaining question there is vanishing of the unstable kernels.
This is not a proof that consecutive matrix maps are surjective:
they can still have nontrivial maps between those kernels.

The same theorem proves K1-surjectivity of `C_0(X,B)` for every
locally compact Hausdorff X and every such coefficient B, including
nonmetrizable bases. Finite scalar coordinates reduce each K-class
to a finite-dimensional compact range, where a large endpoint piece
provides a size-one representative. This does not assert K1-injectivity
or purity of the function algebra.

An explicit part of the kernel now vanishes by
[the varying-projection support theorem](stw58-small-projection-support-kernel-vanishing.md).
Over a connected finite CW base of dimension d>=1, a stably null
family supported by a nonzero projection p contracts whenever
d[p]<=[1-p]. For simple finite pure coefficients, proper p and a
uniform normalized quasitrace bound strictly below 1/(d+1)
imply this comparison. The support may vary over the base.
Moving arbitrary families into such supports remains unproved;
the criterion has no nonzero proper supports in projectionless
coefficients and does not settle the general kernel question.

[The soft-support extension](stw58-soft-support-reservoir-kernel-vanishing.md)
removes the projection requirement. For A=C(X,B), dim(X)=d>=1,
and unital stable-rank-one B, a stably null unitary supported in
Her(h) contracts if h is full and has an orthogonal positive
reservoir b with d[h]<=[b]. Cuntz cutdown comparison constructs
actual hereditary matrix copies; a continuous-field stable-rank
bound supplies the contraction. For simple finite pure B,
strict fiber quasitrace size bounds can verify the comparison.
This includes soft supports in projectionless coefficients.

[The uniform quasitrace support theorem](stw58-small-quasitrace-support-kernel-vanishing.md)
now removes the need for an originally full support or a prescribed
reservoir. For simple unital finite pure B with nonempty QT1(B),
a stably null family contracts whenever its support h has
sup_(x,tau) d_tau(h(x))<1/(d+1). A tiny constant full positive
element enlarges h without losing the size bound; complementary
functional-calculus cutoffs then create a full orthogonal reservoir.
In particular this applies directly to h=|u-1|, even when it vanishes
at some parameter points or has zero annihilator before cutoff.
Every representative of a surviving degree-k unstable kernel must
therefore have uniform quasitrace support dimension at least 1/(k+1).
The precise remaining gap is global support localization or
fragmentation of arbitrary stably null families; the general kernel
and LVIII questions remain unresolved here.

The 2025--26 selflessness examples—reduced group algebras of limit groups and
their relatives—remain useful tests for the higher `K`-stability maps:
pureness need not give `Z`-stability in the nonnuclear setting, even though
stable rank one has already settled their scalar-unitary `K_1` map.

## Attempts

The attached coefficient-stabilization notes record a full higher-degree
result under unbounded exact K0 divisibility of the unit and a nonempty
normalized quasitrace space. Strict comparison realizes the unit roots
by projections; stable-rank-one cancellation gives exact large matrix
decompositions, and Rieffel's published bounded-divisibility theorem
applies. This is a consequence of prior art, not a solution of LVIII.

Soft divisibility instead gives a concrete Hilbert-module sandwich
X^n -> B -> X^(n+1). It supplies a large compact corner over K(X),
but its first embedding need not be adjointable. The soft-module note
proves local coefficient-dependent contraction inside sufficiently
large hereditary matrix pieces and their dimension-drop overlap.
Localization of arbitrary sphere families into those pieces remains
unproved. A finite-matrix example rules out unrestricted hereditary
homotopy excision, so an argument must use an explicit stable range.

The local-factorization artifact now proves an exact continuous
factorization on a norm neighborhood of one, using a fullness identity,
a bounded linear commutator decomposition, and a corrected exponential
chart. Separately, a globally factored sphere family contracts whenever
its total stable class vanishes: the full overlap absorbs each factor's
K-class and cancels the sum in the stable matrix range. This also works
for a global factorization approximating the family within distance two.
The outstanding step is a continuous global factorization over the
parameter sphere; local factorization does not automatically supply it.

The subsequent overlap-corrected word-space artifact removes the
raw K-theoretic balancing classes by an explicit overlap-transfer
homotopy quotient. Its homotopy groups map isomorphically to stable
K-theory in the matrix range. It also proves exact lifting of any
compactly parameterized homotopy with an initial lift, after finitely
many identity-valued word blocks are appended. Connectivity of the
remaining corrected fiber is unproved; computing the domain's stable
homotopy groups does not identify the homotopy groups of U(B).

The degree-one source audit separately proves loop surjectivity from
stable rank one. Sarkowicz and CGSTW explicitly assert the stronger
degree-one isomorphism, but their cited Rieffel theorem has an extra
all-torus hypothesis. The audit has not verified the additional
injectivity derivation and does not assert that the published claim
is false or mathematically open.
