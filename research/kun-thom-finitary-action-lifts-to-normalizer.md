---
rg: 2
id: kun-thom-finitary-action-lifts-to-normalizer
kind: claim
title: The explicit Kun--Thom action on the finitary symmetric factor has a trace-correct homomorphic lift to the normalizer of R in its ultrapower
invalidates:
  - nonhyperlinear-from-kun-thom-finitary-normalizer-obstruction
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
distinct_from:
  hyperlinear-wreath-model: that asks directly for canonical microstates of the abelian-lamp wreath; this asks for a homomorphic normalizer lift of the larger finitary-symmetric action, which is sufficient but not known to follow from wreath hyperlinearity.
  invariant-cartan-completion: that tries to recover a normalized abelian lamp algebra from an arbitrary embedding; here the base is already the hyperfinite factor and the unknown is a nonabelian cocycle splitting in its ultrapower normalizer.
  kt-two-positive-compressors-generate-full-obstruction: that identifies why the two one-compressor permutation constructions cannot be pasted; this is the positive lifting statement in which the same incompatibility appears as a cocycle in `U(R' cap R^omega)`.
---

Let `Gamma < G` be the Kun--Thom pair, `X=G/Gamma`,
`Y=X x {0,1}`, and

```text
R = L(Sym_fin(Y)).
```

The permutation action of `G` on `Y` induces an action
`alpha:G->Aut(R)`.  There is a homomorphism

```text
u:G -> N_(R^omega)(R)
```

such that `Ad(u_g)|_R=alpha_g` and

```text
tau(x u_g)=0                    (x in R, g != 1).       (KFL1)
```

Equivalently, by `finitary-extension-ce-iff-action-lifts-to-normalizer`,
the explicit crossed product `R rtimes_alpha G` is Connes embeddable.
For every subgroup on which nonidentity elements move infinitely many
points of `Y`, the action is outer and `(KFL1)` is automatic; on that
subgroup the content is exactly that the pullback of

```text
1 -> U(R' cap R^omega) -> N_(R^omega)(R) -> Aut(R) -> 1
```

splits.  The full claim retains `(KFL1)` so it does not assume that every
actor element has infinite support.

This is OPEN.  Choosing individual lifts costs nothing by approximate
innerness of automorphisms of `R`; making them multiplicative is the entire
nonabelian cocycle problem.  The natural finite-quotient lift of the Kazhdan
subgroup is incompatible with the compressor relations, so a proof needs a
genuinely exotic simultaneous lift for the two named compressors.

Two exact reductions now remove possible ambiguity in that last sentence.
First, `kt-finitary-action-is-outer-mod-scalar-core` proves that for the
valid specialization `q=2` every nonidentity actor automorphism is outer, so
`(KFL1)` is automatic and only cocycle splitting remains.  Second,
`kt-two-compressor-normalizer-cocycle-splits` constructs a trace-correct
normalizer lift on `<A,B>=SL_3(Z)` itself.  Thus the two compressor lifts are
not intrinsically incompatible.  Third,
`kt-one-compressor-normalizer-cocycle-splits` constructs a trace-correct lift
on each full ascending HNN subgroup `<Gamma,A>` and `<Gamma,B>`, acting on
the entire ambient coset set rather than only its distinguished orbit.  Thus
the first possible nonsplit class must use `Gamma` and at least two compressor
directions simultaneously.  A full proof must extend these already split
one-compressor lifts across a genuinely joint mixed
stabilizer/compression relation.

The overlap itself is no longer part of the uncertainty.
`kt-one-compressor-and-sl3-normalizer-lifts-paste` uses amenable-edge
amalgamated-free-product permanence to put the lift of `<Gamma,A>` and the
lift of the whole external `SL_3(Z)` in one matrix ultraproduct with the two
copies of `A` literally equal (and likewise for `B`).  The quotient from
that CE amalgam to `G` first kills the finite family

```text
C gamma C^(-1) alpha_C(gamma)^(-1),   gamma in T,
```

for a finite generating set `T` of `Gamma`.  By
`kt-c-normalization-is-the-first-finite-normalizer-seam`, these words have
squared HS distance exactly two from the identity in the canonical AFP
paste.  Thus the remaining task is a genuinely macroscopic mixed-kernel
closing problem, not alignment of independently chosen subgroup lifts.

The kernel-closing equation is now cohomologically exact.  For a compatible
AFP lift `u`, the discrepancy

```text
k_gamma=(u_C u_gamma u_C^*)u_(alpha_C(gamma))^*
```

is a `U(R' cap R^omega)`-valued one-cocycle, and changing `u_C` by a kernel
gauge changes `k` by a coboundary.  Hence closing the displayed finite seam
is exactly triviality of this cocycle subject to the remaining `SL_3(Z)`
relations.  Moreover `kt-canonical-afp-seam-has-no-internal-gauge-correction`
proves by a Fourier/Bass--Serre argument that no nonzero intertwiner exists
inside the canonical CE amalgam algebra.  Any positive solution must create
the correcting gauge in the larger **extrinsic** relative commutant of its
embedding into `R^omega`; an extrinsic-commutant collapse theorem would give
the negative branch instead.

This internal obstruction is quantitative and stable under every finite
diagonal amplification (`kt-internal-c-seam-has-a-kazhdan-gap`).  Therefore
the usual direct-sum/flip trick does not repair it: that flip exchanges two
different Gamma representations rather than intertwining repeated copies of
the same `H_A` lift, and making the mixed blocks `S`-covariant requires the
infinite coset induction `S/<A>`, not the three-cycle `C^3=1`.
`kt-extrinsic-c-seam-has-a-finite-satisfiability-criterion` now gives the
sharp ultrapower test: a correcting gauge exists exactly when one fixed
finite Gamma seam packet and the finite `SL_3(Z)` relator packet can be made
arbitrarily small while commuting with longer finite subsets of `R`.

Two further fences show how nontrivial such a solution must be.  Passive
McDuff amplification of the AFP paste retains the identical Kazhdan seam
gap, so an independent hyperfinite central-sequence factor cannot supply the
gauge.  In any finite ambient algebra, an exact extrinsic corrector has
conditional expectation zero onto the AFP paste and hence lies at squared
distance one from it; approximate correctors satisfy
`||E_M(z)||_2<=defect/kappa`.  The positive branch therefore needs a wholly
new, dynamically nontrivial Gamma bimodule in the extrinsic relative
commutant, not absorption or small perturbation of the known CE model.

The minimal new module is now intrinsic: an exact corrector generates an
orthogonal index-one correspondence between the two copies
`W^*(R,C Gamma C^(-1))` and `W^*(R,alpha_C(Gamma))`, with an `R`-central
unitary cyclic vector.  Independent Bernoulli, coinduced, or McDuff tensor
actions of the quotient actor do not create it: their actor unitaries already
satisfy the quotient C-normalization identity and cancel from the seam, so
`k_gamma` remains `k_gamma tensor 1`.  Any positive construction must couple
the AFP paste to the new factor non-tensorially; at that point it is exactly
the mixed-kernel correspondence problem rather than a permanence shortcut.
