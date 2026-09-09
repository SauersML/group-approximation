---
rg: 2
id: boone-higman-conjecture
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented simple group
root: true
goal: true
distinct_from:
  boone-final-group-finitely-presented: that is one established fact about one constructed group -- the Boone tower's final group has a finite presentation; this is a universal embedding conjecture over all finitely generated groups with solvable word problem, and it requires the target to be SIMPLE, which that tower's final group is not.
  countable-group-embeds-in-two-generator-simple-group: that is Schupp's classical theorem, which is true and imposes no finiteness on the presentation of the envelope; this asks for the envelope to be finitely PRESENTED, which is exactly the part Schupp does not give and which fifty years of work have not supplied.
  simple-sofic-total-mf-radical: that asks for a countable simple sofic group whose MF radical is everything -- an approximation property of one constructed group; this is a universal embedding statement with no approximation content, and neither implies anything about the other.
  literal-word-problem-solvable: that computes the word problem of one specific group E built in this repository; this quantifies over all finitely generated groups with solvable word problem and asserts an envelope exists for each.
  novikov-boone-fp-group-undecidable-word-problem: that exhibits a finitely presented group whose word problem is undecidable, which is the other side of the same dividing line; this is about the groups on the decidable side and where they can be embedded.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
  - research/artifacts/high-impact-literature-roots-audit-2026-08-31.md
  - research/artifacts/ck-quotient-and-cover-bi-index-obstruction-2026-09-08.md
  - research/artifacts/boone-higman-gpu-pilot-2026-09-08.md
  - research/artifacts/boone-higman-ring-route-repair-2026-09-08.md
  - research/artifacts/boone-higman-steinberg-cover-correction-2026-09-08.md
  - research/artifacts/boone-higman-cover-kernel-dichotomy-2026-09-08.md
  - research/artifacts/boone-higman-lean-preflight-2026-09-08.md
  - research/artifacts/boone-higman-projective-finiteness-gate-2026-09-08.md
  - research/artifacts/boone-higman-zigzag-shift-compiler-2026-09-08.md
  - research/artifacts/boone-higman-finite-ray-compiler-boundary-2026-09-08.md
  - research/artifacts/boone-higman-relative-automorphism-fp-obstruction-2026-09-08.md
  - research/artifacts/boone-higman-wreath-projection-audit-2026-09-08.md
  - research/artifacts/boone-higman-boundary-wreath-germ-construction-2026-09-08.md
  - research/artifacts/boone-higman-finite-state-and-shell-germ-limits-2026-09-08.md
  - research/artifacts/boone-higman-shell-normal-core-criterion-2026-09-08.md
  - research/artifacts/boone-higman-shell-effective-presentation-2026-09-08.md
  - research/artifacts/boone-higman-perfect-shell-route-2026-09-08.md
  - research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
  - research/artifacts/boone-higman-arithmetic-odometer-model-2026-09-08.md
---

For every finitely generated group `G` with solvable word problem there is a
finitely presented simple group `H` and an embedding `G <= H`.

Open since the 1970s.  Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356,
state the two-directional form: "A conjecture of Boone and Higman from the
1970's asserts that a finitely generated group `G` has solvable word problem
if and only if `G` can be embedded into a finitely presented simple group."

Only the direction above is open.  The converse is a theorem and is carried
separately as `simple-envelope-forces-solvable-word-problem`.

## Why it is a root of this graph

It is an explicit program goal, and remains open. Its existing embedding
routes originated when an external resolution attempt was audited against
this repository on 2026-08-17 and turned out to land squarely on machinery this repository
already owns: the missing hypothesis of its near-solution is finite normal
generation of a maximal kernel, which by
`fp-quotient-iff-kernel-finitely-normally-generated` is
*equivalent* to finite presentation of the resulting simple quotient — and
the hard half of that equivalence is already formalized here, in
`GroupApproximation/Algebra/FinitePresentationKernel.lean`.  The attempt also
runs its ring lane straight through this repository's Leavitt formalization,
where one tempting route is killed outright and another is left needing a
theorem nobody has.

Soficity, hyperlinearity and MF-ness are not evidence about this claim in
either direction, and no node here pretends otherwise.

The September 8 construction
`boundary-orbit-cyclic-wreath-has-fp-simple-envelope` handles cyclic
lamps on constant-ray orbits of contracting self-similar groups. Its
proof uses `contracting-srn-rational-stabilizers-are-fp` and a finite
germ extension. It supplies an additional positive family, not a
universal route: no reduction from arbitrary solvable-word-problem
inputs to that construction has been established. The attached
artifact explains the residual-finiteness limit on its input family.

There is a stronger limit on finite-state realizations:
`decidable-fp-groups-need-not-embed-in-rational-group` combines an
explicit single-exponential transducer word-problem algorithm with
the Kharlampovich--Myasnikov--Sapir hardness theorem. Some decidable
finitely presented residually finite inputs embed in no rational
homeomorphism group. Thus a universal proof cannot require every
input to act by finite-state Cantor homeomorphisms.

The route `boone-higman-via-shell-germ-stabilizers` retains arbitrary
Cantor shell homeomorphisms and therefore avoids that restriction.
Its universal faithful finite-germ realization is proved; its OPEN
clause is `decidable-inputs-have-fp-shell-stabilizers`, finite
presentation of three explicitly specified one- and two-point
singularity stabilizers for a suitable enumeration of the input.

`virtually-cyclic-inputs-have-fp-shell-stabilizers` closes these clauses
for virtually cyclic inputs. The normal-core criterion used there is
unavailable for every other input, as the prefix-core classification
proves. For arbitrary inputs the germ group instead has the exact
index-two fiber-product description in
`shell-germ-group-has-index-two-fiber-product`. Finite presentation
of that fiber product is necessary for the open shell clauses; neither
the universal presentation nor a lift back to all three stabilizers
has been supplied.

## What a certificate must contain

The shell route has an additional effective consequence:
`shell-recursive-presentations-compute-enumerations` extracts the
regular enumeration from a recursive presentation of its one-point
stabilizer. A successful enumeration must therefore be computable.
The finite-prefix obstruction for shell groups shows why finite point
samples do not certify a successful presentation, even for Z.

The shorter route `boone-higman-via-fp-shell-envelopes` now asks only
for a finitely presented E_nu. Finite generation of its point stabilizers
holds for every enumeration of every finitely generated input, by
`shell-finite-point-stabilizers-are-finitely-generated`. The three
stronger stabilizer presentation clauses remain sufficient, but the
new route does not assume them or finite presentation of the germ group.

There is also the direct route `boone-higman-via-perfect-shell-envelopes`.
An explicit HNN and amalgam construction embeds every finitely
presented decidable input in an infinite perfect one while preserving
decidable word problem. Its shell envelope is simple for every
enumeration. The remaining OPEN task is finite presentation of that
envelope for a suitable enumeration; this route needs no additional
twisted Brin--Thompson construction.

*Proof.*  It suffices to close any one of the live routes.  The shortest
is `boone-higman-via-ck-maximal-kernel`: by
`boone-higman-thompson-simple-envelope` and
`chatterji-kassabov-normal-generator-embedding` one already has, for every
such `G`, a chain

    G  <=  S  <=  Gamma

with `S` finitely generated, computably presented and simple, and `Gamma`
finitely presented with property (T) and normally generated by an element of
`S`.  By `proper-normal-subgroups-miss-the-normally-generating-core` every
proper normal subgroup of `Gamma` meets `S` trivially, so every maximal
proper normal quotient is simple and still contains `G`.  A certificate is
then exactly a finite normal generating set for one maximal proper normal
subgroup of `Gamma`.

Two routes added 2026-08-24 avoid the normal-lattice machinery entirely and
never require any group to be shown simple, because simplicity is produced at
the end by `type-a-action-gives-boone-higman-for-subgroups`.  A certificate
for either is a construction and nothing else:
`universal-fiber-product-data-for-word-problem-groups` asks for a finitely
presented overgroup with a finitely generated normal subgroup having trivial
centralizer, finitely many conjugacy classes and an `F_3` quotient;
`shift-higman-compiler` asks for finite presentability of one explicit
permutation group built from a chosen enumeration.  Both are shown to force
their input to have solvable word problem
(`compilers-cannot-drop-the-decidability-hypothesis`), so neither can be
proved by an argument uniform in a finite presentation.  See
`research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md`.

*Disproof.*  A finitely generated group with solvable word problem together
with a proof that it embeds in no finitely presented simple group.  No
mechanism for the second half is known; see the diagonalization entry below.

## Attempts

Seven lanes were run against this repository's material on 2026-08-17.
The universal-sandwich ring lemma is valid, but its claimed consequence
that the elementary group is finitely presented was withdrawn on September
8: the cited theorem applies to the Steinberg group. The corrected
construction retains a marked cover. Several shortcuts are recorded as
dead routes with named invalidators; the rest remain at identified gaps.
The August audit and the September correction artifacts carry the arguments.

1. **Take a maximal normal quotient of the finitely presented envelope.**
   *Dies* at `fp-quotient-iff-kernel-finitely-normally-generated`:
   a quotient of a finitely presented group need not be finitely presented,
   and Zorn's lemma supplies a maximal kernel and nothing else.  Recorded as
   `boone-higman-via-maximal-quotient-of-the-envelope`.
2. **Zorn on the finitely normally generated proper normal subgroups.**
   *Dies* on chains: the union of an ascending chain of finitely normally
   generated normal subgroups need not be finitely normally generated, so the
   class has no upper bounds and Zorn does not apply.  Finite generation of
   the ambient group gives properness of the union, not stabilization of the
   chain.  What would rescue it is a Max-n condition on the normal lattice,
   and none was found.  Deferred rather than noded: nothing is refuted.
3. **Property (T) as a source of that Max-n condition.**  *Dies as a general
   principle.*  By
   `kazhdan-hyperbolic-continuum-non-fng-maximal-kernels`, one torsion-free
   finitely presented word-hyperbolic property-`(T)` group has continuum many
   maximal normal subgroups that are not finitely normally generated.  Hence
   even those combined hypotheses do not imply normal-lattice Noetherianity.
   The construction-specific possibility that the Chatterji--Kassabov
   elementary-matrix envelope has one specially chosen compact maximal kernel
   remains open.
4. **Make the coefficient ring simple.**  Split in two.  The naive form —
   the one-relation universal sandwich already gives a simple ring — *dies*
   at `one-sided-sandwich-leaves-an-ideal-missing-the-core`, by an explicit
   Toeplitz counterexample; recorded as
   `boone-higman-via-sandwich-ring-simplicity`.  The serious form survives as
   the open route `boone-higman-via-projective-ring-host`. Its predecessor
   `boone-higman-via-finitely-presented-simple-ring-quotient` is invalidated:
   its universal ring premise fails in composite characteristic, and its
   unquotiented elementary group has a nontrivial central involution.
5. **Use this repository's finitely presented strongly simple Leavitt algebra
   as a universal host.**  *Dies* at
   `weyl-algebra-blocks-a-universal-leavitt-host`: Bilich--Hazrat--Nam prove
   the first Weyl algebra does not embed in `L_K(1,2)`, so no blanket
   embedding theorem for countable algebras is available.  Recorded as
   `boone-higman-via-universal-leavitt-host`.
6. **Compress the infinite Boone--Higman HNN tower into finitely many
   relators**, by a shift `t_i = z^{-i} t z^i` encoding the enumeration.
   *Deferred at an identified step.*  Encoding the recursive list is
   Higman's theorem and is not the difficulty; the difficulty is that every
   nontrivial element of the *final* group must normally generate it,
   including the new machine and stable letters, and forcing that with extra
   relations endangers the base embedding.  Finite compression that preserves
   simplicity is the conjecture restated, so nothing is invalidated.
7. **Diagonalize for a counterexample.**  *Deferred, no mechanism.*
   Cardinality separates nothing — both the finitely presented simple groups
   and the computably presented finitely generated groups are countable.
   Higman's embedding theorem forbids diagonalizing against all finitely
   presented targets, so simplicity must be used essentially, and finite
   presentations defining *simple* groups are not available as an effective
   list with the semantic guarantees a priority construction needs.  No
   hereditary separating property was found beyond solvable word problem,
   which the candidate has by hypothesis.  Non-uniformity is not a disproof
   either: the conjecture is existential, so incomputability of
   `presentation |-> simple envelope` is consistent with it.

An eighth non-attempt, recorded because it looks tempting from inside this
program: Schupp's envelope
(`countable-group-embeds-in-two-generator-simple-group`) is two-generator but
not computably presented, so Higman's theorem does not apply to it;
`boone-higman-thompson-simple-envelope` restores computable presentability
but then Higman destroys simplicity.  That route rotates between the
conjecture's two halves without narrowing either.

## A strictly easier subproblem, unsolved

If a maximal proper normal `M <| Gamma` could be chosen *recursively
enumerable as a normal subgroup* relative to a finite presentation of
`Gamma`, then `Gamma/M` would be a finitely generated computably presented
simple group with decidable word problem — not finitely presented, but an
effective simple envelope produced directly from the construction.  The
obvious effective-Zorn attack needs to decide `<<M, x>> ∩ S = 1`, and the
clean criterion of `proper-normal-subgroups-miss-the-normally-generating-core`
(`N` proper iff `N ∩ S = 1`) is not effective in the required direction.

## August 2026 property-(T)-free normalization

`bht-trivial-normal-intersection-envelope`, imported from
Fournier-Facio--Wu--Zaremsky Appendix A, shows that the near-solution does not
intrinsically need the Chatterji--Kassabov property-`(T)` envelope.  Every
finitely generated solvable-word-problem group embeds in a finitely presented
`P` while missing **every** proper normal subgroup of `P`; equivalently every
nontrivial quotient of `P` preserves the input.  Thus the simple-core survival
part is a theorem in a property-`(T)`-free form.  The remaining obstruction is
unchanged and exact: a maximal kernel supplied by Zorn need not be finitely
normally generated, so its simple quotient need not be finitely presented.

## September 8: the canonical coset repair fails for every quotient

`ck-quotient-corner-has-infinite-bi-index` strengthens the direct-corner
obstruction: every nontrivial quotient retains a root subgroup isomorphic
to the additive group of the infinite quotient ring at its elementary
level, and that subgroup supplies distinct simple-core double cosets.
Marked covers inherit infinite bi-index by the surjection of double-coset
sets. Finite-index enlargements of the stabilizer cannot repair it either.

This refutes `ck-quotient-coset-repair` and disables
`boone-higman-via-ck-quotient-cosets`. Other embeddings and infinite
stabilizer enlargements remain candidates. The maximal-simple-quotient
route does not require finite bi-index and remains open.

The GPU pilot is an operational experiment attached to this goal, not a
mathematical prerequisite or a proof of any route. Its artifact records the
$20 spending cap, the provider's GPU-quota rejection, and the prepared neural
proposal/checker pipeline. Positive Lean calibration subsequently passed
on a cached remote CPU runner; the separate preflight artifact records
the exact scope and connects its normalization lemma to the quotient proof.
The dedicated research workflow checks source syntax, the exact `S3`
counterexample used as a negative control, and Cairn's graph structure.

## September 8: the ring route needs a projective target

`ring-simple-envelope-characteristic-obstruction` refutes the unrestricted
finite-fullness premise using `Z/6Z` and characterizes which coefficient
rings admit abstract simple unital envelopes. Integral group rings pass
that test, but the construction supplies no finite presentation.

`rank-four-elementary-center-obstructs-simplicity` shows that `EL_4(L)`
cannot be the proposed simple group whenever `L` contains `Z`: it contains
the proper central subgroup `{I_4,-I_4}`. The repaired conditional route
`boone-higman-via-projective-ring-host` proves the simple core survives
projectivization. Its missing hypothesis explicitly asks for a finitely
presented, simple projective target. That existence problem remains open.

## September 8: finite presentation belongs to the Steinberg cover

`steinberg-finite-presentation-and-kazhdan-theorem` pins the imported
finite-presentation result to `St_4(U)`. It does not make `EL_4(U)`
finitely presented. `finite-marking-normal-generator-cover` proves that
finitely many added relators preserve a finitely presented marking and
force the prescribed normal generator while retaining a map to the matrix
group. Applied to the Steinberg source, this gives
`ck-steinberg-marked-cover`.

The maximal-kernel route remains valid for this finitely presented cover.
The matrix level-ideal screen cannot automatically be applied to its
arbitrary maximal kernels. The quotient-and-cover double-coset obstruction
still applies in its stated scope, independently of finite presentation
of the matrix group. No finite normal generating set for a maximal kernel
has been supplied.

## September 8: a coset repair must come from the covering kernel

`ck-cover-quotient-kernel-dichotomy` settles the scope of quotients that
escape the matrix map. Write `K=ker(Gamma->EL_4(U))`. Any proper quotient
`Gamma/M` in which the inherited core has finite bi-index must satisfy
`Gamma=MK`; equivalently K surjects onto the whole quotient. For maximal
M this is the alternative to containing K and descending to a simple
matrix quotient. No suitable quotient of K has been constructed, and no
finite normal generating set for M follows from this dichotomy.

## September 8: projectivization retains the presentation requirement

`projective-elementary-fp-kernel-criterion` gives an exact version of the
ring host's finite-presentation clause. It requires finite normal
generation of the unstable Steinberg kernel and finite generation of the
elementary center. A finitely generated group with finitely presented
central quotient is itself finitely presented, so passing to the
projective group does not repair failure of elementary-group finite
presentation. The ring-host route now uses the equivalent generating-data
formulation. Projective simplicity also forces the ring itself to be
simple. Neither the required generating data nor a universal host has
been constructed.

## September 8: an explicit positive cyclic shift compiler

`zigzag-cyclic-shift-envelope-is-finitely-presented` identifies a concrete
E_nu(Z) as an index-12 subgroup of E_4. Its finite presentation follows
from the four-ray Houghton group's finiteness theorem. The universal
infinite-input compiler remains open.

The same analysis shows a limit on testing enumerations by finite point
values: for Z every finite prescription extends to both a finitely
presented envelope and a non-finitely-presented one. The positive example
works because a global four-ray rule controls the relations. No analogous
global rule has been supplied for arbitrary decidable inputs.

The finite-ray generalization is now classified by
`finite-ray-shift-envelopes-require-virtually-cyclic-input`: it is possible
exactly for virtually cyclic inputs. In particular, Z^2 cannot be handled
by merely increasing the number of periodic rays. Its regular enumeration
also has unbounded generator displacement, as quantified by
`regular-enumeration-displacement-bounds-growth`. The shift route remains
open with these construction restrictions recorded explicitly.

## September 8: the universal computable-core automorphism upgrade fails

`relative-automorphism-fp-host-reflects-base-presentation` proves that a
finitely presented subgroup of Aut_G(G*F_n) containing the canonical
translation copy of a finitely generated G forces G itself to be finitely
presented. The proof lifts finitely many automorphisms, their inverses,
and their presentation relators using only finitely many base relators.

For MIF simple cores the evaluation action is faithful. Thus its action
image is finitely presented exactly when the core already is. The regular
cyclic twisted Brin--Thompson group supplies an infinite, decidable,
finitely generated simple MIF core which is not finitely presented.
This refutes `bffhz-action-image-is-finitely-presented` as universally
stated here and disables `boone-higman-via-bffhz-action-image`.

The published BFFHZ Question 3.2 assumes a finitely presented core and is
not answered by this counterexample. Selecting special non-MIF cores or
using other actions is not excluded. No proof or disproof of Boone--Higman
follows from this obstruction.

## September 8: a new wreath-product source needs a projection repair

The source audit in
`research/artifacts/boone-higman-wreath-projection-audit-2026-09-08.md`
examines arXiv:2609.01868v1. Its proposed finite-presentation proof appeals
to a coefficient-forgetting projection toward another Cantor full group.
`cantor-prefix-subgroup-detects-every-normal-kernel` rules out a map
which both kills a nonidentity localized coefficient and preserves the
prefix subgroup faithfully. The coefficient projection of an ordinary
wreath product does not supply such a full-group map.

If the intended projection is only on a localized coefficient subgroup,
it exists but cannot detect the exponents of the lamps it kills. The audit
separates these interpretations explicitly.

This is a proof-step obstruction, not a counterexample to Theorem D of
that source. Its finite-presentation conclusion has not been imported as
an established premise. A repair would need to derive cancellation of all
lamp coordinates from the finite relations directly. No such repair has
been supplied here.
