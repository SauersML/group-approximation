# Boone–Higman: September 20 Cairn integration

This integrates three manuscripts supplied in the conversation on 2026-09-20:
*Boone–Higman: Cairn audit, direct kernel construction, and the remaining
breakthrough*, *Polynomial valuation germs and new Boone–Higman envelopes*,
and *Beyond polynomial germs*.
It is an edited integration and dependency map, not a byte-for-byte copy of
the downloadable files. The `sandbox:/mnt/data/` downloads were not available
in this workspace; the supplied text is the source. None of the manuscripts is a
Lean proof, an independently refereed result, or a publication-priority claim.

A third supplied draft, [Beyond polynomial germs](beyond-polynomial-germs/beyond_polynomial_germs.md),
is now integrated alongside them. It proposes a common compact-core SingFix
criterion for observed automorphism mapping tori, recurrent scalar profiles,
and noncommuting recurrence-matrix profiles, plus an exact scalar germ
finite-presentation criterion. Its detailed proof artifacts and separate
formula checker are linked from that index. It does not assume the earlier
polynomial theorem as an established premise.

The new [compact-core gate](../compact-core-singfix-finiteness.md) supports
the proposed [observed mapping-torus theorem](../observed-mapping-tori-have-simple-fk-hosts.md)
and its [larger twisted V-lamp source](../observed-twisted-v-lamps-have-simple-fk-hosts.md).
The [Jordan free-product example](../jordan-free-product-tori-have-simple-f-infinity-hosts.md)
records the noninjective-observation application separately. The
[fresh replay](beyond-polynomial-germs/REPLAY.md) passes 5,678 formula
assertions and matches the supplied script hash; its note hash identifies the
edited integration index, not the unavailable original manuscript.

**Full Boone–Higman remains unresolved.** The first manuscript strengthens an
obstruction to taking simple quotients of a chosen envelope. The second proposes
simple F∞ embeddings for specific polynomially twisted solvable groups. The
third extends the proposed mechanism to observed mapping tori and recurrent
profiles. None proves the universal BH embedding theorem. The existing
[Lean progress report](../../notes/BOONE_HIGMAN_LEAN_PROGRESS_2026-09-20.md) and
[single-submission plan](../../notes/BOONE_HIGMAN_PALOMAR_PLAN.md) remain the
formalization and release records.

## Integration and dependency policy

**Updated submission decision:** the user has selected the strongest results
from all three manuscripts for the single Palomar package and instructed us to
use the supplied arguments as correct working proofs, repairing details during
formalization. The [exact selected scope](../../notes/BOONE_HIGMAN_PALOMAR_SELECTED_SCOPE.md)
records the headline statements, question answers and grouped corollaries.
An independent-referee approval is not a prerequisite for beginning or
continuing that work. The OPEN construction gates below still identify proof
obligations not discharged by checked Lean declarations or the formula tests.

Cairn computes claims from routes, not from prose status labels. In particular,
an empty prerequisite list asserts a complete proof. Substantive unreviewed
construction lemmas are therefore exposed as unresolved mathematical claims;
downstream routes state their actual conditional implications. An OPEN result
can have a detailed proposed proof attached. Previously established alternative
derivations are retained, without treating their graph status as a certificate.

The [direct RN proof artifact](padded-abstract-rn-manuscript-integration-2026-09-20.md)
and [strengthened claim](../padded-abstract-rn-perfect-decidable-nonrecursive-kernel.md) strengthen
[`fp-relatively-simple-pair-with-unsolvable-simple-quotient`](../fp-relatively-simple-pair-with-unsolvable-simple-quotient.md)
by aiming to obtain, in one example, decidability, perfectness, a finitely
presented normally generating simple core, and a non-recursively-presentable
unique simple quotient. Its finite-presentation and formal-support arguments
avoid the abstract twisted Brin–Thompson finite-presentation input. The source
still uses the finite-recursion simulation and Higman–Thompson finiteness facts.

The [polynomial proof artifact](polynomial-germ-unitriangular-manuscript-2026-09-20.md)
starts from the existing OPEN
[`q-difference-lamplighter-satisfies-boone-higman`](../q-difference-lamplighter-satisfies-boone-higman.md).
It proposes embeddings of UTₘ(Z[1/q])^(Z) ⋊ (P_d ⋊ Z), and their specified
extensions, into two-generated simple F∞ groups. Its new normal polynomial
germ filtration addresses the old cyclic-germ obstruction; the finite-point
stabilizers, punctured-space induction, and finite-forest restriction arguments
remain explicit review targets. SZ, BHM and BZ are literature dependencies,
not new Lean axioms. The supplied formula checker is in
[`polynomial-germs/`](polynomial-germs/REPLAY.md); arithmetic agreement does
not verify the infinite-group finiteness theorem.

The new construction targets are visible as Cairn roots in their own right;
they are not encoded as implications proving the universal BH root.

## Current-checkout validation

The [saved Cairn validation report](boone-higman-cairn-validation-2026-09-20.json)
records a fresh MSI compile of the streamed research snapshot using this
checkout's vendored Cairn parser, linter and graph compiler. All **67 scoped
nodes** passed reference, duplicate, Attempts and expected-status checks.
The compiled snapshot has 34,409 nodes (17,576 claims and 16,833 routes),
zero global compile errors, and 46 warnings outside this integration.
Scoped duplicate checking covers the 52 newly added nodes; it is not a
whole-repository duplicate audit. The run took 17.24 seconds on one MSI CPU,
with a 55-second wall limit and a 2 GiB virtual-memory cap. No local Python
or Lean build was run for this integration.

The [current declared BH dependency inventory](boone-higman-current-dependencies-2026-09-20.txt)
contains 244 claims and 257 routes, with all 43 direct BH routes and no
unresolved identifiers. These are current-checkout figures, distinct from the
historical source archive audit below. The generated research frontier is
refreshed from this same compiled snapshot. New construction claims remain
OPEN; the two inverse-diagonal routes remain INVALIDATED. Earlier independent
derivations retain their prior statuses. This is graph validation, not
mathematical verification, independent refereeing, or a Lean certificate.

The two saved arithmetic replays passed **26,296** and **5,678** finite formula
checks respectively. Their separate replay records give source hashes,
commands and limitations. They do not discharge the OPEN proof obligations.

## Integrated construction map

| Construction or gate | Cairn node |
| --- | --- |
| Direct decidable perfect quotient obstruction | [Padded RN witness](../padded-abstract-rn-perfect-decidable-nonrecursive-kernel.md) |
| Formal-support and clopen stabilizer theorem | [RN structural gate](../padded-abstract-rn-local-derived-normal-subgroup-theorem.md) |
| Affine marked-point stabilizers | [Base stabilizer gate](../affine-rn-groups-and-rational-fixers-are-f-infinity.md) |
| Punctured-space successor step | [Simultaneous induction gate](../polynomial-valuation-germ-induction-preserves-marked-finiteness.md) |
| All degrees and finite forests | [Polynomial tower](../polynomial-valuation-germ-towers-are-f-infinity.md) |
| Faithful oligomorphic actor and restriction groups | [Clopen action gate](../polynomial-germ-clopen-action-structure.md) |
| Explicit injective lamp representation | [Lamp embedding gate](../polynomial-unitriangular-lamps-embed-in-polynomial-germ-groups.md) |
| Two-generated simple F∞ envelope | [Polynomial unitriangular family](../polynomial-unitriangular-lamps-have-simple-f-infinity-hosts.md) |
| Independent ends, multiple dilations, finite products/extensions, fixed periods | [Extended families](../eventual-quasipolynomial-lamps-have-simple-f-infinity-hosts.md) |
| Noncontracting self-similar RN finiteness | [Radial recursion family](../noncontracting-polynomial-rn-groups-are-f-infinity.md) |
| Independent arithmetic dilations and vector profiles | [Multiscaling envelope family](../multiscaling-lamps-have-simple-f-infinity-hosts.md), with its own [uniform actor gate](../multiscaling-polynomial-germ-towers-have-f-infinity-actors.md) |
| All finite singularity-constrained stabilizers without germ normality | [Compact-core gate](../compact-core-singfix-finiteness.md) |
| Bilaterally observed automorphism mapping tori, with two endpoint species | [Mapping-torus family](../observed-mapping-tori-have-simple-fk-hosts.md) |
| Exact recurrence / finite-rank / FP / F∞ equivalence for scalar germs | [Scalar germ criterion](../recurrence-scalar-germ-fp-iff-recurrent.md) |
| Independently recurrent ends and nonabelian nilpotent lamps | [Recurrence lamp family](../recurrence-nilpotent-lamps-have-simple-f-infinity-hosts.md) |
| Noncommuting upper-unitriangular matrix profiles | [Matrix profile family](../recurrence-matrix-lamps-have-simple-f-infinity-hosts.md) |
| Three generators, derived length three, nonlinearity over every field | [Exponential-tail example](../three-gen-nonlinear-recurrence-lamp-has-simple-host.md) |
| Self-similar radial labels and full finite-germ groups | [Recurrence RN family](../recurrence-radial-rn-groups-are-f-infinity.md) |

The [recurrence and matrix proof artifact](beyond-polynomial-germs/recurrence-and-matrix-proofs.md)
records the finite-forward-lattice and finite-window HNN arguments separately
from the geometric host construction. The
[recurrence-to-polynomial route](../polynomial-lamp-hosts-via-recurrence-envelope.md)
connects the two manuscripts without assuming the polynomial normal-filtration
proof. The exact germ criterion excludes nonrecurrent profiles only from this
scalar germ finite-presentation mechanism; it is not a negative BH result.

The exact-arithmetic script's fresh MSI replay passed all 26,296 checks in
1.94 seconds on one CPU and reproduced the supplied JSON. The independent
integration review additionally exposed the required equality of local germ
**groupoids** away from the fixed finite set in the punctured induction:
one must localize preceding-degree source-to-target germs while avoiding that
set. This obligation is now recorded in the induction gate and proof artifact;
formula checks do not discharge it.

## The quotient obstruction and what it actually excludes

The proposed direct example is a finitely presented perfect decidable group E
with proper normal M containing every proper normal subgroup, with E/M infinite
simple and not recursively presentable. An embedded V_D (even D) is infinite,
finitely presented and simple, meets M trivially, and every nonidentity core
element normally generates E. The action on proper nonempty clopens has type
[A₂] and kernel M. Membership in M is co-c.e. but not c.e., with the same Turing
degree as the original free-recursion tree kernel.

A pair embedding means exactly j(E) ∩ L = j(M). If H is finitely presented
and L is finitely normally generated, H/L is finitely presented, so such an
embedding would place the finitely generated non-recursively-presentable E/M
inside a recursively presented group. Substituting its generator words and
enumerating ambient relator consequences contradicts that conclusion. No
relative-simplicity or action hypothesis on (H,L) is needed for this exclusion.
Subject to the construction gates, this supplies the reported yes to FFWZ 5.8
and no to both parts of 5.9 in the exact normal-pair sense. It does not answer
FFWZ 5.7 or disprove relative BH, PBH, or BH.

The preservation lemma behind the tempting shortcut is valid: if a simple
subgroup normally generates P, every proper normal subgroup of P misses that
subgroup. Finite generation of P makes a chain of proper normal subgroups have
proper union, so a maximal proper subgroup exists by Zorn. Its quotient is
simple and preserves the core. **Finite presentation is the missing conclusion.**
For finitely presented P, P/N is finitely presented iff N is finitely normally
generated. In a strictly increasing chain N_i, if P/(∪N_i) were finitely
presented, finitely many normal generators would lie in one N_i, forcing
stabilization. An infinite sequence of repairs needs a real finite compression.

## Subsidiary proofs retained from the first manuscript

### Type [A₂] kernels and exact removal

A type [A₂] actor is finitely presented, has finitely generated point
stabilizers, and finitely many pair orbits. Choose finitely many point-orbit
representatives H_j and complete finite double-coset representative lists.
Membership in each H_j g H_j is c.e. by enumerating subgroup words and equality
proofs. These disjoint sets cover all words, so simultaneous searches decide
the unique double coset, in particular membership in H_j. This uses fixed
finite data, not an algorithm discovering it from an arbitrary presentation.
Enumerating conjugates outside a stabilizer enumerates the complement of the
action kernel K. Thus K is co-c.e.; K recursive, image decidable, and image
recursively presentable are equivalent. A finitely generated sharp subgroup
has decidable word problem by dovetailing equality and nonkernel witnesses.

If a finitely generated stabilizer H has finitely presented image H/K, choose
a finite presentation on the images of its generators. Lift those finitely
many relators into H. They normally generate K in H and hence in P. This
does not assume H itself finitely presented. The existing node
[`a2-stabilizer-image-presentation-controls-kernel`](../a2-stabilizer-image-presentation-controls-kernel.md)
records this positive criterion.

The exact removal criterion is already
[`a2-kernel-removable-iff-image-in-type-a2-actor`](../a2-kernel-removable-iff-image-in-type-a2-actor.md).
A target pair (H,L) with L finitely normally generated gives a finitely
presented faithful type (A₂) actor H/L containing P/K. Conversely, if
i:P/K→Λ embeds in a faithful type (A₂) actor, let P×Λ act through Λ.
Its kernel P×1 is finitely normally generated, and p↦(p,i(pK)) is an
injective homomorphism with the exact pair intersection. A recursive kernel
alone is not asserted sufficient.

### A decidable wreath product with nonrecursive polynomial identities

For the proposed decidable actor E, finitely many transitive orbit kernels
have intersection M. Each is co-c.e.; at least one, M_O, is not c.e., or
their intersection would be recursive. Fix O=E/H with H finitely generated
and finitely many double cosets. Its membership is decidable as above.

Set W=C₂ wr_O E. Adjoin a lamp c to a finite presentation of E, with
c²=1, [c,h_i]=1 for finite generators of H, and
[c,d_j c d_j⁻¹]=1 for finite double-coset representatives. Lamps g c g⁻¹
are well-defined on gH by centralization. The double-coset relations make
every two commute. The resulting map from the restricted direct sum, with
the E action, is inverse on generators to the natural map to W. This proves
finite presentation directly. Collecting lamp positions using decidable H
membership and deciding the actor word proves decidable word problem.

Let P(W) be generated, under pointwise multiplication of functions W→W,
by constant functions and the identity function. It is finitely generated.
The polynomial [x c x⁻¹,g] is identically one exactly when the actor g fixes
every point of O: conjugates of c are precisely the orbit lamps, since the
lamp base is abelian. Hence g↦[x c x⁻¹,g] reduces M_O to the evaluation
kernel in W*⟨x⟩. That kernel is not c.e.; P(W) cannot be recursively
presentable. This is a direct route to the existing
[`fp-decidable-group-whose-e-is-not-recursively-presented`](../fp-decidable-group-whose-e-is-not-recursively-presented.md),
not a new priority claim or an independent check of MathOverflow's wording.

### Correct perfect envelopes

The map g↦(g,g⁻¹) is a homomorphism only for abelian groups. The new
[`inverse-diagonal-is-homomorphic-iff-abelian`](../inverse-diagonal-is-homomorphic-iff-abelian.md)
invalidates its two historical engine consumers. The pointwise commutator
identity does not repair multiplicativity.

The valid existing replacement is
[`mitosis-and-virtually-free-perfect-envelope-proof`](../mitosis-and-virtually-free-perfect-envelope-proof.md).
For a finitely presented decidable Q, start with Q×Q and two HNN letters
s,d identifying the first factor with the second and with the actual
diagonal g↦(g,g). Edge membership tests v=1, u=1, u=v are decidable with
coordinates. Britton reduction decides the resulting T(Q). Killing the base
retracts onto F(s,d), whose membership is decided by comparing an element
with its retraction. The HNN relations kill the base in abelianization.

In A₅*A₅ take a of order two and b of order three from different factors.
The kernel C₂*C₃→C₂×C₃ is free of rank two with basis
u=abab⁻¹, v=ab⁻¹ab. Finite Schreier rewriting and free-product normal
forms decide its membership and coordinates. Amalgamate T(Q) with A₅*A₅
by s=u,d=v. Normal forms embed both factors, yield decidable word problem,
and finite presentations give a finite presentation of the amalgam. The
perfect factor kills the remaining stable-letter abelianization. This is
an infinite perfect decidable finitely presented envelope, not a simple host.

## All 43 archived direct-route assessments

The following preserves the supplied audit's route classification. It is not
a fresh certification of every dependency proof. Each stem names a current
research file; “archive-refuted” retains the original distinction from an
argument reproduced in the manuscripts.

**Current-checkout difference:** Cairn already invalidates
`boone-higman-via-ck-maximal-kernel` because its encoded universal premise is
refuted by `poisoned-ck-envelopes-have-no-fng-maximal-kernel`. The supplied
audit's “conditional” assessment concerns a construction-specific repair.
These are different quantifiers; the historical assessment below does not
override the live graph's invalidation or establish the clean-marking gate.

| Route (prefix `boone-higman-`) | Supplied assessment / remaining gate |
| --- | --- |
| via-houghton-like-shift-envelopes | Conditional; generic free shifts archive-refuted. |
| via-v-times-aperiodic-sft-full-groups | Universal minimal free SFT and full-group presentation missing. |
| via-essential-shell-germ-algebras | Essential-algebra presentation and Steinberg-kernel gates. |
| via-perfect-shell-envelopes | Perfect wrapper available; shell finite presentation missing. |
| via-germ-steinberg-algebra-presentation | Defective full-algebra simplicity, quantifiers and kernel premise. |
| via-shell-germ-stabilizers | Universal finitely presented shell stabilizers missing. |
| via-ck-maximal-kernel | Particular maximal kernel must be finitely normally generated. |
| via-fp-stabilizer-engines | Archive-refuted engine; inverse-diagonal error corrected here. |
| via-kazhdan-boone-higman | Valid implication from a stronger conjecture. |
| from-infinite-simple-inputs | Valid reduction; upgrade remains open. |
| via-bader-shalom-lattice-hosts | Universal lattice construction and presentation missing. |
| via-finite-bi-index-envelope | Conditional; canonical-corner versions excluded. |
| via-fiber-product-criterion | Universal fiber-product data missing. |
| via-shift-higman-compiler | Input-sensitive finite-presentation compiler missing. |
| via-sandwich-ring-simplicity | Invalid: one full element does not make ring simple. |
| via-isolated-overgroup-and-local-boone-higman | Conditional, includes an equivalent local BH problem. |
| via-local-boone-higman | Equivalent formulation, not a solution. |
| via-rover-nekrashevych-hosts | Universal faithful-host premise archive-refuted. |
| via-maximal-quotient-of-the-envelope | Invalid: simple quotient need not be finitely presented. |
| via-enlarged-shell-stabilizers | General permutation extension missing; restricted models retained. |
| via-leavitt-units-of-rigid-sft-overgroups | Universal crossed-product host and K-theory hypotheses missing. |
| via-v-times-rigid-topfree-sft-full-groups | Rigid symbolic action and full-group presentation missing. |
| via-ck-quotient-cosets | Inherited-corner quotient repair archive-excluded. |
| via-universal-leavitt-host | Invalid fixed-host universality shortcut. |
| via-finitely-presented-simple-ring-quotient | Generic unital embedding and central-scalar defects. |
| via-isolated-stabilizer-engines | Archive-dead engine; inverse-diagonal error corrected here. |
| from-simple-fa-inputs | Conditional simple-FA-input upgrade. |
| via-decidable-edge-towers | Tower existence and BH preservation under HNN steps missing. |
| via-bffhz-action-image | Non-finitely-presented-core universal version archive-refuted. |
| via-shell-stabilizer-overgroups | Finite bi-index in presented overgroup missing. |
| via-central-simple-leavitt-tensor-host | Universal coefficient host and K-theory gates. |
| via-universal-fp-self-similar-host | False: faithful tree groups are residually finite. |
| via-stabilizer-engines | Circular or false in universal archived form. |
| via-genuine-action-shell-envelopes | Universal finite-presentation construction missing. |
| via-units-of-cantor-crossed-leavitt-tensors | Input-containing host and K-triviality missing. |
| via-fp-shell-envelopes | Suitable finitely presented shell envelope missing. |
| via-leavitt-units-of-rigid-topologically-free-sfts | Universal crossed-product and K-theory gates. |
| via-hypothesis-free-shift-compiler | False: would embed undecidable inputs in FP simple groups. |
| via-projective-ring-host | Core injection valid; center and Steinberg-kernel finiteness missing. |
| via-infinite-shift-compiler | Product with Z repairs infinitude, not the compiler. |
| from-countable-decidable-bh | Valid implication from stronger open assertion. |
| via-permutational-boone-higman | Valid implication; universal faithful actor missing. |
| via-complexity-graded-universal-inputs | Stipulated uniform host archive-refuted. |

## Remaining frontier and provenance

An exact universal remaining target is: embed every infinite finitely generated
recursively presented simple group into a finitely presented simple group.
Simple recursive groups have decidable word problem by parallel enumeration
of equality and normal-generation witnesses; classical simple-envelope and
Clapham reductions do not themselves perform the required upgrade.

The quotient version needs a construction-specific finitely normally generated
maximal kernel. The proposed obstruction excludes obtaining that merely from
decidability, perfectness and a finitely presented normally generating simple
core. Universal faithful rooted-tree hosts are ruled out by residual finiteness.
Local realization in FP simple groups is an equivalent BH formulation. Ring
routes must separately prove ring simplicity, Steinberg-kernel finite normal
generation and the appropriate central quotient; unital characteristic six
cannot embed in a simple unital ring. A perfect simple core's legitimate
diagonal elementary embedding survives projectivization, without proving
those presentation gates.

The first manuscript reports an audit of archive
`group-approximation-main (1)(2).zip`, SHA-256
`ea0fa7cbdcdf97212971b1f3c547e304e4eb147d1ccf532fd6528cd077192b40`:
72,696 entries, 519,310,776 uncompressed bytes, 34,115 parsed research nodes,
79 frontmatter errors, and a backward closure of 500 identifiers with 498
parsed nodes (242 claims, 256 routes). These figures and its source-byte hashes
describe the supplied archive audit; they have not been independently replayed
or substituted for current-checkout counts. Its two unresolved identifiers,
`ck-envelope-simple-core-has-finite-bi-index` and
`decidable-inputs-admit-two-sided-fg-near-index-kernel`, **both exist in this
checkout**. No fake missing-node placeholders are needed.

The polynomial manuscript names a different archive, `(1)(3).zip`. Its public
literature search and assertion of the q-difference target's prior OPEN status
are supplied provenance. Neither that search nor the exact-arithmetic script
certifies novelty or an unconditional Lean result. These results are selected
for the combined Palomar package; release must wait for actual Lean proofs and
verification. The prose
manuscripts are not substitutes for those checks.
