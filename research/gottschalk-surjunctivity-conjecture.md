---
rg: 2
id: gottschalk-surjunctivity-conjecture
kind: claim
title: Every group is surjunctive on every finite-alphabet full shift
root: true
goal: true
refuted_by:
  - projective-ternary-leavitt-group-nonsurjunctive
  - ternary-leavitt-unit-group-nonsurjunctive
  - leavitt-unit-group-nonsurjunctive
distinct_from:
  gottschalk-surjunctivity-fixed-two-generator-tester: that establishes a reduction to one group; this is the universal conjecture itself, still unresolved here.
  leavitt-unit-group-nonsurjunctive: that seeks one counterexample and would refute this universal positive goal; it is not a positive proof prerequisite.
artifacts:
  - notes/GOTTSCHALK_RESEARCH_2026-09-07.md
  - research/artifacts/gottschalk-information-transport-pinning-control-2026-09-08.md
  - research/artifacts/gottschalk-row-column-deficit-measure-control-2026-09-08.md
  - research/artifacts/gottschalk-injective-image-uniform-gibbs-bridge-2026-09-08.md
  - research/artifacts/gottschalk-quadratic-block-elimination-2026-09-08.md
  - research/artifacts/gottschalk-virtually-abelian-guard-stratification-2026-09-08.md
  - research/artifacts/gottschalk-polycyclic-guard-rank-extension-2026-09-08.md
  - research/artifacts/gottschalk-surjunctive-guard-finite-intersection-proof-2026-09-08.md
  - research/artifacts/gottschalk-off-guard-quadratic-elimination-2026-09-08.md
  - research/artifacts/gottschalk-tarski-common-factor-residual-controls-2026-09-08.md
  - research/artifacts/gottschalk-common-factor-coset-collisions-2026-09-08.md
  - research/artifacts/gottschalk-stable-three-factor-reduction-2026-09-08.md
  - research/artifacts/gottschalk-recipient-affine-normal-form-and-fiber-obstruction-2026-09-08.md
  - research/artifacts/gottschalk-tarski-operand-reversal-exclusions-2026-09-08.md
  - research/artifacts/gottschalk-exact-quadratic-derivative-collision-criterion-2026-09-08.md
  - research/artifacts/gottschalk-central-odd-norm-conjugacy-direct-finiteness-2026-09-08.md
  - research/artifacts/gottschalk-noncentral-order-three-axis-corner-2026-09-08.md
  - research/artifacts/gottschalk-noncentral-norm-feedback-rigidity-and-corner-equivalence-2026-09-08.md
  - research/artifacts/gottschalk-unrestricted-order-three-odd-parity-obstructions-2026-09-08.md
  - research/artifacts/gottschalk-directed-quadratic-intertwiner-rigidity-2026-09-08.md
  - research/artifacts/gottschalk-balanced-invariant-code-finite-exclusion-and-infinite-prefix-control-2026-09-08.md
  - research/artifacts/gottschalk-balanced-triangular-invariant-scalar-code-construction-2026-09-08.md
  - research/artifacts/gottschalk-controlled-symmetry-linear-code-extension-and-complement-collision-2026-09-08.md
  - research/artifacts/gottschalk-finite-support-reversible-completion-of-invariant-code-2026-09-08.md
  - research/artifacts/gottschalk-prefix-symmetry-group-elementary-amenability-2026-09-08.md
  - research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md
---

For every group G and every finite nonempty alphabet A, every injective
cellular automaton tau:A^G -> A^G is surjective. An empty alphabet gives
the trivial empty configuration space and causes no additional case.

A cellular automaton means a continuous equivariant self-map of the full
shift, equivalently a map given by a finite memory set and a local rule.
The topology is the product of the discrete alphabet topologies. A proper
invariant subshift cannot replace the full shift in this statement.

This records the positive goal requested on 2026-09-07. Neither the
repository's nonsofic-group constructions nor a completed dependency
reduction settles it. Its negative Leavitt lane remains separate; a
counterexample there would refute this claim.

## Attempts

**Positive permanence beyond soficity (2026-09-11).**
`rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive` proves that
`A wr_X G` is surjunctive for every residually finite lamp `A`, every
`G`-set `X` and every surjunctive `G`. Its proof transplants an injective
automaton to the coset spaces that remember lamp classes at finitely many
marked sites. There the rule is uniform off strata that are right cosets of
point stabilizers. Composing with slicewise inverses in order of cardinality
leaves the identity off finitely many right cosets of one stabilizer
intersection. A coset-region lemma turns that remainder into an automaton over
the intersection, which is a surjunctive subgroup.

Consequences: `kun-thom-nonsofic-wreaths-are-surjunctive`, and the root
`surjunctive-nonsofic-group-exists`, a negative answer to Bowen--Chapman's
question whether surjunctivity characterizes soficity. This is a class
theorem, not the universal goal. The binary Leavitt unit group is not in the
class. Any counterexample must avoid permutational wreath products with
residually finite lamps over a surjunctive base.

The same proof needs only a finitary site structure on a split kernel:
residually finite site projections, translated supports, and stabilizer
invariance (`finitary-split-extension-surjunctivity-permanence`). It
therefore also covers every group double `G *_Gamma G` of a surjunctive `G`
(`doubles-of-surjunctive-groups-are-surjunctive`). In particular the
nonsofic Kun--Thom doubles are surjunctive
(`kun-thom-group-doubles-are-surjunctive`). Counterexamples must also avoid
these doubles. General amalgams, non-split extensions, the Leavitt unit group,
Thompson's `V` and the Fournier--Facio group remain outside the method.

The finite-observable approach now yields the quantitative criterion
split-ca-defects-force-linear-observable-rank: a strict encoder has a
positive defect seed generating a tower of dimension n delta. It does
not furnish an upper bound contradicting that growth.
reversible-xor-has-linear-observable-rank disproves the proposed universal
sublinear bound, even for the unique decoder of a bijective automaton.
Another invariant must distinguish defect growth from reversible growth.

The fixed-test-group route below uses the existing reduction honestly:
surjunctivity of the test group itself remains an open prerequisite.

The second attack proves split-decoders-have-generic-cantor-fibers. A
strict encoder forces every local decoder to erase a finite perturbation
and have a Cantor subset in every transitive output fiber. The new route
therefore asks for a decoder with just one countable transitive fiber.
No such universal countability result has been proved. In particular,
large topological fibers do not force positive conditional entropy for
the measure supported on the chosen section; the artifact gives a
rectangular counterexample to that inference.

The quantum extension attack now has exact obstruction bounds in
split-ca-quantization-has-sharp-defect. Compression by the encoder's
isometry is local and unital completely positive, but a strict encoder
would give it a norm-one multiplicative defect and put its range
projection at distance 1/2 from the quasilocal algebra. The universal
extension to a unital homomorphism on full matrix observables remains
an open prerequisite. Locality alone does not supply multiplicativity.

The information-transport attack's proposed exact row identity is false,
even for a reversible two-track involution. A degree-64 tree parity shear
with fully iid source and output pins has a discontinuous conditional
entropy for an interval of source-pin densities; finite-exhaustion reveal
accounting misses a uniformly positive atomic contribution. The artifact
gives the exact posterior reduction and proof. This rules out eliminating
all singular information mass as the universal positive argument. A
comparison of the missing row and column contributions remains open and
does not establish surjunctivity here.

The singular row and column deficit measures also have no universal
local ordering: the reversible control gives opposite strict signs on
transposed rectangles in the two pin densities. Their total difference
is exactly the still-unproved percolative-entropy lower bound. The new
control excludes assigning each local deficit a favorable sign; it does
not refute a possible global comparison using cancellation or transport.

The Gibbs bridge proves that the image of an injective CA carries a
unique uniform Gibbs measure, finite dependence, and exact completion
counts `N_Y(E,c)=|A|^|I_E| b_E(c)`. The residual integer counts input
boundary assignments. An overlapping-pair encoding gives a proper
image with all these properties when the output alphabet is larger.
At equal alphabet, no argument removes the boundary loss or licenses
replacement by a forbidden output pattern. This bridge therefore
leaves the headline surjunctivity question open.

The quadratic-feedback attack proves positive exclusions for arbitrary
bipartite operand graphs, target-multiplicative systems without same-track
quadratic terms, and nearest-two cyclic feedback of every length. A
generalized two-block lemma supplies the common argument. The artifact
also excludes every scalar two-term selector by explicit collision or
reduction to a finite memory subgroup, and gives mixed-triangle controls, including
a track-shift conjugate with distinct spatial pairs that resists the
specified initial elimination moves. The unrestricted conjecture remains
open; escaping those moves is not an injectivity or strictness proof.

The support-preservation argument now covers every surjunctive guard
subgroup: injectivity forces surjectivity when configurations supported
in unions of its cosets stay in those unions. Only finitely many
intersections of the original mask stabilizers can arise. A finite
poset of their commensurability classes replaces the earlier rank
induction, and Neumann's finite-coset avoidance theorem removes the
amenability restriction in isolation. Uniform local recoverability is
preserved throughout cancellation. It is enough that the subgroup
generated by the guard's finite memory addresses be surjunctive.
This includes free guards as well as the preceding abelian and
polycyclic cases. The unrestricted ambient group is not proved
surjunctive; the general conjecture remains open.
The conditional theorem and its proof route are recorded as
`surjunctive-guard-subgroups-force-surjectivity` and
`finite-coset-intersection-elimination-proves-guard-transfer`.

A separate elimination theorem needs no surjunctivity assumption on
the guard when exactly one operand of each quadratic monomial lies
in it. Finite unions of guard cosets become recipient color blocks
in a compact invariant coefficient space. The block argument keeps
the coloring fixed and proves uniform locality of each inverse.
For `x+x_r x_(rt)+x_s x_(st)`, a strict candidate must consequently
have every one-from-each-pair guard generate the whole memory group.
Satisfying that condition is not an injectivity proof.

The full family `F=x+(1+R_t)R_s(x R_t x)` is now excluded over every
group: injectivity implies surjectivity. Infinite or even-order t
gives a bipartite operand graph; finite odd order gives an explicit
coset collision unless the memory subgroup is abelian. The Tarski
instance passes the earlier mask and coloring controls and still
has a finite collision. This closes that specified nonlinear family,
without asserting surjunctivity of the Tarski group or arbitrary CA.

The common-factor result extends to every outer actor `u` in `<t>`
for `F=x+(1+R_u)R_s(x R_t x)`. In the finite odd-order case,
injectivity forces either `u in <s>` or the memory subgroup `<s,t>`
to be finite abelian. For arbitrary `u`, a five-exclusion coset
witness gives further explicit collisions; it does not prove the
remaining rules injective. This family theorem is recorded in
`common-factor-power-actor-ca-are-surjunctive`.

A universal reduction is now recorded in
`stable-three-factor-reduction-proves-gottschalk`: add identity tracks
and compose with reversible local shears to reduce every finite-alphabet
CA to sums of products of at most three unary lookup factors over
`Z/qZ`. This preserves both injectivity and surjectivity in both
directions. Over finite fields there is also an ordinary cubic
polynomial version. The prerequisite
`three-factor-finite-alphabet-ca-are-surjunctive` is still open;
the existing block elimination theorems do not cover this universal
class. The reduction therefore does not close the headline goal.

The further universal normal form `H(x,u)=(x+u,F(x)-x-u)` puts
every output's nonlinearity on the opposite block while giving it
constant coefficient +1 or -1 on its own recipient track. The exact
fiber identity `H^-1(z,w) ~= F^-1(z+w)` shows that these properties
retain the full problem. Isolating a preserved certificate gives
fibers that are translates of F; none is known bijective independently.
The new prerequisite `recipient-affine-three-factor-ca-are-surjunctive`
is open. The artifact also excludes obtaining an invariant coordinate
fiber by constant linear two-track changes while retaining recipient
affinity for a non-affine rule.

In the conditional Tarski common-factor example, operand reversal
excludes two of the four residual mechanisms. At most two actors
remain for fixed noncommuting s,t, with exact subgroup relations in
the new artifact. They are necessary cases still to be tested, not
injective maps or counterexamples.

The quadratic difference equation now has an exact criterion for
every shared shift t, including orders one, two, and infinity.
For F=x+A(x R_t x) with arbitrary linear CA A, a collision exists
exactly when a configuration q yields nonzero delta=Aq and satisfies
the stated local compatibility and finite-cycle parity conditions.
Orbit recurrences then construct the two inputs. The criterion
also proves that the simplest one-subgroup mask cannot work in one
remaining Tarski case. An admissible nonzero q for either unresolved
case has not been constructed. The proved criterion is recorded in
`quadratic-shift-differences-have-exact-orbit-criterion`.

For each fixed Gamma, surjunctivity of the full family x+A Q_t on
Gamma x C_3, with arbitrary scalar linear A, is exactly equivalent
to direct finiteness of F_2[Gamma]. A local parity-majority involution
and two-block elimination prove sufficiency using only scalar direct
finiteness. The norm subclass proves necessity. This is recorded in
`central-c3-quadratic-surjunctivity-iff-direct-finiteness`;
neither side is established for arbitrary Gamma.

For any odd n>=3, the narrower central norm rules F_B=x+(B-I)E Q_t
on Gamma x C_n are explicitly conjugate to B on the parity coordinate
and identity on the other coordinates. This conjugacy preserves
composition and decoder identities. Finite central blocks also encode
arbitrary matrix rules on enlarged groups. The all-odd-cycle result
is recorded in `central-odd-norm-quadratic-ca-are-conjugate-to-linear`.

For an arbitrary order-three element, the feedback preserving the
invariant triple subspace is surjunctive exactly when the corner
eF_2[G]e, e=1+t+t^2, is directly finite. When <t> is normal, all
linear feedback qualifies and the corner is F_2[G/<t>]. This is
recorded in `order-three-axis-feedback-surjunctivity-iff-corner-finiteness`.
For nonnormal <t>, injectivity on the linear axis alone does not
justify compressing it back to that axis: a finite order-18 control
disproves that intermediate inference. The control itself is
noninjective; the unrestricted nonnormal case remains unresolved.

The nonnormal norm-feedback subclass x+aE Q_t now has an exact
criterion without assuming preservation of the invariant subspace.
Injectivity forces the compressed corner map B=e+eae to be injective.
If B is bijective, a shortest-cycle or finite-path argument forces
the off-axis map (1-e)ae to vanish, making the quadratic rule
conjugate to B plus identity. Consequently any strict injective
norm rule explicitly produces the strict injective scalar linear
rule I+EaE on the same group. This is recorded in
`noncentral-norm-feedback-surjunctivity-iff-corner-finiteness`.
The missing mechanism for unrestricted nonnormal feedback must
involve its additional action on the even-parity subspace.

For unrestricted scalar feedback, the odd-parity subshift now
has an exact collision criterion. If EAE=0, a directed-path
argument forces AE=0 under injectivity, and then proves
surjectivity without any ring hypothesis. On A_4, 2-transitivity
gives an explicit collision for every feedback with (I-E)AE
nonzero. These are recorded in
`unrestricted-zero-compression-feedback-is-surjunctive`.
For arbitrary A, injectivity also forces every fixed-parity
linear map v -> v+A((1+c)R_t^2 v) from ker E into the full
output space to be injective. Compressing those maps back to
one parity component is not justified. No theorem covers the
remaining unrestricted nonnormal feedback.

A direct encoding of the reversible two-track control is now
excluded in `quadratic-intertwiners-cannot-scalarize-triangular-feedback`.
The unbalanced triangular rule moves the unique Q-fixed point with
a singleton preimage fiber. Every injective zero-preserving scalar
binary cellular automaton fixes it, excluding arbitrary nonlinear
Q-preserving conjugacies. The argument also excludes injective
Q-preserving encodings into invariant codes when the transitive
target coordinate action commutes with Q.

For balanced triangular feedback F_A(x,y)=(x+A Q_t(y),y), A1=0,
the condition AE != 0 excludes full Q-preserving scalar conjugacies:
the intrinsic stratum of Q-fixed points with four preimages has a
proper nonempty fixed subset for F_A, while scalar shifts act
transitively on the corresponding target stratum. A separate
finite-source argument excludes arbitrary invariant-code encodings
for every nonzero balanced A: three intrinsically distinguished
Q-fixed points cannot all map to distinct scalar constants. In
contrast, an explicit infinite-source construction for A_4 x Z
with nonzero off-axis component gives a continuous Q-preserving
injection into a proper invariant scalar code over a countable
group Lambda, with reversible dynamics on that code. A separating
orbit of a two-component observable is obtained using prefix
centralizers and component permutations; see
`balanced-triangular-rule-has-an-invariant-scalar-code`.
Adjoining one controlled symmetry gives an enlarged group and an
exact two-term scalar linear-feedback extension, but a tetrahedral
complement collision proves that extension noninjective. This is
not a linear-span claim for the original group. The support group
has at most 192 elements; completing its projected code involution
by the identity on unused blocks now gives a zero-preserving
nonlinear reversible full-shift extension, recorded in
`balanced-invariant-code-has-a-reversible-full-shift-extension`.
An injective extension specifically of the form x+B Q_s remains
open as a reversible-control question. The stronger group audit now
closes the entire current prefix/permutation/controlled-diagonal
construction as a counterexample route: its source symmetry group
is elementary amenable, even when memory generates an infinite
subgroup. Faithful restrictions to finitely many non-u labels embed
each finitely generated subgroup into a known elementary amenable
orthant permutation group; see
`current-prefix-symmetry-group-is-elementary-amenable`.
Thus every finite-alphabet full-shift cellular automaton using
addresses from this group is surjunctive. Other source symmetries
are not classified, and the headline conjecture remains unresolved.
Independently, continuous affine Q-intertwiners only copy triples or make them
constant. Their proper nonempty globally fixed-coordinate set
excludes affine full and invariant-code encodings of the unbalanced
control even for arbitrary equivariant targets, without target
injectivity or zero preservation. Encodings that alter Q and
encodings into non-invariant codes remain outside the stated
obstructions.

Preserving Q is not itself incompatible with nonlinear scalar
reversibility: a conditional triple rotation on C_3 x C_2 is
an explicit countercontrol. However, no nontrivial rule x+A Q
can commute with Q, as the same artifact proves using the
translation stabilizers of its fibers. A proposed nonlinear
encoding therefore still needs a separate argument that its
conjugated rule has the required linear-feedback form.

**Decoder fibers, measured (2026-09-12).** The countable-fiber route is an
exact reformulation, not a weakening. The converse route
`countable-transitive-decoder-fiber-from-gottschalk` makes its prerequisite
equivalent to this goal, and the two routes form a deliberate cycle. The fiber
zero-one law now has an established measure form,
`strict-split-pairs-carry-positive-entropy-flip-lifts`. A strict split pair
carries an invariant factor-of-iid lift of uniform Bernoulli through the
decoder whose identity coordinate has conditional entropy at least
`log 2 / (|A|^|W| |WW^-1|)`. Over amenable groups a Følner average of this
bound recovers surjunctivity. Single-site fiber entropy contradicts nothing by
itself: `xor-lift-of-bernoulli-has-positive-fiber-entropy` refutes
`ca-bernoulli-lifts-have-zero-fiber-entropy` and kills
`gottschalk-via-flip-lift-and-zero-fiber-entropy`. Over `F_2` the
Ornstein--Weiss block map shows that no average works without using the section
`tau`. The missing ingredient is an averaged fiber-entropy bound that uses
`tau` and survives nonamenable boundaries. A cellular marker rule also gives infinitely many cellular sections and an equivariant injection of a decorated subshift into the full shift (`strict-split-decoders-have-infinitely-many-sections`). Over amenable groups that contradicts entropy monotonicity; over general groups no monotone invariant is known. Artifact:
`research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md`.

**Three-factor normal form and the peeling criterion (2026-09-12).** An
independent re-derivation confirms the stable three-factor reduction group by
group and shows it is an equivalence.
`gottschalk-specializes-to-three-factor-class` and
`three-factor-class-specializes-to-recipient-affine` close the cycles, so both
open claims are the conjecture in normal form, not smaller targets.
`controlled-self-linear-feedback-ca-are-surjunctive` proves the peeling
criterion over every group and finite ring. An injective automaton is
surjective once some ordering of its track blocks makes each row, with the
earlier blocks set to zero, linear in its own block under controllers reading
only later blocks, with invertible constant part. This contains the 09-08
bipartite and target-multiplicative theorems. The recipient-affine normal form
fails the criterion under both orderings, so what remains is exactly offsets or
own-block nonlinearity that survive every ordering. Artifact:
`research/artifacts/three-factor-audit-and-controlled-feedback-2026-09-12.md`.

**No permanence route to the tester host (2026-09-12).**
`fixed-host-outside-sofic-permanence-closure` shows that the host `U` of the
fixed tester is not built from sofic groups by subgroups, directed colimits,
finitary split extensions, graph folds or LEF-lamp graph wreaths. `U` contains
the binary Leavitt unit group, a finitely presented simple nonsofic Kazhdan
group, and no member of that class contains such a group. So
`fixed-host-lies-in-sofic-permanence-closure` is refuted and
`fixed-host-surjunctive-via-sofic-permanence` is dead. Every landed
surjunctivity permanence theorem is one of these operations, so iterating them
reaches neither `U` nor the Leavitt unit group. A positive proof on the host has
to handle automata on a simple nonsofic Kazhdan group directly. Subgroup
heredity now has its own node, `surjunctivity-passes-to-subgroups`, and the dead
route names it as a prerequisite. Artifact:
`research/artifacts/fixed-host-permanence-closure-obstruction-2026-09-12.md`.

**Linear case over the Leavitt unit group (2026-09-12).**
`leavitt-inverse-defects-are-visible-or-invisible` proves that every Kaplansky
pair in `F_2[R^x]` is a group-element translate either of a lift of
`(s_0, t_0)` or of a pair in `1 + ker(pi)`, where `pi` is the evaluation onto
the Leavitt algebra. So the linear route into
`leavitt-unit-group-nonsurjunctive` comes down to exactly two lifting problems:
`left-invertible-lift-of-s0-in-leavitt-group-algebra` and
`leavitt-evaluation-kernel-unitization-not-directly-finite`. Killing both
proves `leavitt-unit-group-algebra-is-directly-finite`, and then every
injective `F_2`-linear automaton over `R^x` is surjective. The visible lifting problem is equivalent to finding lifts `a` of `s_0` and `b` of `t_0` with `b a` a unit of `F_2[R^x]`, and `b a - 1` nilpotent suffices. Its positive direction is gated by `binary-leavitt-unit-group-is-f2-linear-sofic`: `F_2`-linear soficity of `R^x` kills both lifting problems.

**Logical form (2026-09-12).** A group is not surjunctive exactly when some
pair of local rules satisfies the decoder identity on the realized forward
rectangle `S x M` and fails the reverse identity on `M x S`
(`surjunctivity-is-axiomatized-by-rectangle-clauses`). The identity passes to
coarser tables and its failure passes to finer ones. So the surjunctive groups
are exactly the models of decidably many universal sentences with equational
premises and conclusions, and existentially closed groups decide the
conjecture. The conjecture itself is the `Pi^0_2` sentence "for every strict
rectangle data `D`, some reverse coincidence follows from the forward relations
of the canonical host `P(D)`". By `surjunctivity-recognition-dichotomy`, either
every group is surjunctive, or surjunctivity of finite presentations is
undecidable and the nonsurjunctive finite presentations are not recursively
enumerable. On one host with decidable word problem the search stays
`Sigma^0_1`. None of this decides the conjecture. Artifact:
`research/artifacts/gottschalk-rectangle-clauses-and-recognition-2026-09-12.md`.

**Canonical table groups (2026-09-12).** A rule pair has a strict realization
in some group exactly when it is strict over the table group `U_E` of some
minimal forward-sufficient partition `E`
(`strict-automata-live-on-canonical-table-groups`). Every realization of `E`
receives a homomorphism from `U_E`, which only coarsens the reverse table, so no
choice of group helps beyond `U_E`. Forward partitions that Tietze-eliminate
triangularly give free table groups and bijective automata
(`triangular-forward-tables-force-surjectivity`). Every one-relator partition is
triangular, so a strict design needs a non-eliminable core of at least two
coincidences, and that core presents a nonsofic group. Artifact:
`research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md`.

**Invariant-output architecture (2026-09-12).** If the memory normalizes the
symmetry, an invariant-output automaton is a strict automaton on the quotient
memory group (`normalizing-invariant-output-descends-to-quotient`). Over `F_2`
the encoder needs a nonzero linear part and an odd number of invariant
monomials, and norm rules die (`invariant-output-rules-need-odd-invariant-monomials`).
A single-site sensitivity profile with a right symmetry of order divisible by the
alphabet size admits no decoder of any degree
(`right-symmetric-sensitivity-profile-admits-no-decoder`). Over `F_3` the
swap-averaging idempotent is a genuine group-algebra idempotent, and the corner
equation `c e b = 1` already holds in `L_(F_3)(1,2)`. Lifting it to
`F_3[L_(F_3)(1,2)^x]` would give an injective linear automaton with
swap-invariant output, hence a counterexample
(`ternary-leavitt-swap-idempotent-is-full`); the ternary Leavitt unit group is
now its own counterexample root, `ternary-leavitt-unit-group-nonsurjunctive`.
Artifact: `research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md`.

**The operator-algebraic trace route is closed (2026-09-12).** By
`injective-ca-product-trace-zero-one-law`, for an injective automaton over an
infinite group the image measure either equals the uniform measure or is
singular to it: a strict image is null, because a Garden of Eden has infinitely
many disjoint translates. Every state extending the product trace takes the
encoder's range projection to 0 or 1, and the compression is tracial, or
multiplicative, exactly in the onto case.
`bijective-ca-preserve-uniform-bernoulli-measure` holds over every group. So the
matrix-observable prerequisite `injective-ca-pullbacks-extend-to-matrix-observables`
is the goal restated, and the converse route
`matrix-observable-extension-from-surjunctivity` makes a deliberate cycle. No
trace-level premise in the style of Kaplansky's characteristic-zero proof can be
an intermediate step. The missing count lives at per-site logarithmic scale,
where `strict-automaton-lowers-bernoulli-rokhlin-entropy` and the open
`bernoulli-rokhlin-entropy-maximal-for-every-group` act.

**Corrected tails (2026-09-12).** `surjectivity-reduces-to-offset-corrected-tails`
extends the peeling criterion to rows with surviving offsets, provided the row is
linear in its own block and the linear part is invertible for every value of the
later blocks. Solve the row for zero: the automaton is surjective exactly when
its corrected tail, the later rows evaluated at that solution, is surjective.
Such steps mix with the zero-offset steps. The recipient-affine normal form peels
in one such step to a copy of the original automaton. So offsets are not an
obstruction by themselves. The difficulty sits in the corrected tails, together
with own-block nonlinearity and non-invertible own-linear parts, which this move
does not reach. Artifact: `research/artifacts/offset-corrected-peeling-2026-09-12.md`.

**Rokhlin entropy route (2026-09-12).** A strict injective automaton on `q`
symbols with Garden-of-Eden window `Omega` gives every amplified uniform Bernoulli
shift `(A^k)^G` Rokhlin entropy at most `k(log q - delta/D) + log 3`, where
`delta = -log(1 - q^-|Omega|)` and `D = |Omega Omega^-1|`
(`strict-automaton-lowers-bernoulli-rokhlin-entropy`). The proof is
self-contained: independent markers code the missing pattern, and amplification
pays the marker cost. With Seward's imported per-group formula, the Rokhlin
supremum of a counterexample host is below `(floor(D log 3/delta) + 1) log q`
(`strict-automaton-bounds-rokhlin-supremum`). Maximal Bernoulli entropy passes to
subgroups and up finite index, and a deficit is witnessed by one finite
configuration of translates (`bernoulli-rokhlin-deficit-has-a-finitary-witness`).
So maximality is closed under directed colimits, and the tester host `U` decides
it for every group. `gottschalk-via-maximal-bernoulli-rokhlin-entropy` needs the
open claim `bernoulli-rokhlin-entropy-maximal-for-every-group`, which two routes
make equivalent to `every-group-has-positive-rokhlin-entropy-action`, and
`fixed-tester-surjunctive-via-rokhlin-entropy` needs maximality on `U` only.
Over nonamenable groups window entropy is not an invariant, which kills the naive
image-subshift argument (`gottschalk-via-window-entropy-deficit`). No lower bound
on Bernoulli Rokhlin entropy is known for any nonsofic group.

**Defect windows (2026-09-12).** Placing a Garden-of-Eden window on a
compression defect does not by itself give strictness. Rigid compression defects
lie in the sofic radical, and the surjunctive Kun--Thom graph wreaths carry
nontrivial ones (`surjunctive-groups-carry-invisible-rigid-defects`). Adjoining a
free LEF centralizing factor over any subgroup of any host, the Leavitt unit
group included, leaves surjunctivity unchanged in both directions while creating
nontrivial defects (`free-centralizer-amalgams-are-surjunctivity-inert`). What
remains of the configuration is nesting: the conjugated commuting element lies
inside the compressed Kazhdan subgroup. The nine-leaf Leavitt configuration has
such a nested defect (`leavitt-units-carry-nested-rigid-defect`). Whether nesting
forces nonsurjunctivity is the open claim `nested-rigid-defects-force-nonsurjunctivity`,
routed into `leavitt-unit-group-nonsurjunctive`. Artifact:
`research/artifacts/defect-window-automata-2026-09-12.md`.

**Holonomy normal form and decoder bound (2026-09-12).**
`table-groups-are-memory-holonomy-groups`: eliminating the decoder letters along
a spanning forest of the decoder difference graph gives
`U_E ≅ <memory letters | cycle holonomies> * free`. Restricting the decoder to
the identity component preserves strictness, so a counterexample reduces to a
connected minimal design whose host is generated by the encoder memory, with
decoder addresses as path holonomies. By `amenable-decoder-memory-forces-surjectivity`,
if the decoder's memory group is amenable then the encoder is surjective (the
Garden of Eden theorem plus split decoders). So a strict pair needs a nonsofic
encoder memory group and a nonamenable decoder memory group, and a decoder
memory `{1, a}` is never strict. By
`unicyclic-strict-designs-present-nonsofic-one-relator-groups`, a strict connected
design with one independent cycle presents a nonsofic one-relator group, so under
Pestov 4.10 every strict design needs two independent coincidence cycles.
Artifact: `research/artifacts/table-group-holonomy-normal-form-2026-09-12.md`.

**Ternary split (2026-09-12).** The central involution `-1` splits
`F_3[L_(F_3)(1,2)^x]` into `F_3[PG]`, where `PG` is the quotient by scalars, and
an anti-central summand. There the sign unit `s0 t0 - s1 t1` halves the swap
idempotent, so the corner equation is equivalent to a unital Cohn family, and a
solution acts only on a proper subshift. The Leavitt evaluation sees only that
summand. The half that would yield a counterexample, fullness of the swap
idempotent in `F_3[PG]`, is invisible to it. It holds in the adjoint image
algebra `R (x) R^op` with explicit witnesses; witnesses in the span of
`g (x) g^-1` are open (`projective-ternary-swap-idempotent-is-full`). The
projective ternary group is now its own counterexample root,
`projective-ternary-leavitt-group-nonsurjunctive`.

**F_2-linear-sofic gate for R^x (2026-09-12).** Both Kaplansky lifting problems
sit behind `binary-leavitt-unit-group-is-f2-linear-sofic`, whose negative side is
the rank row `f2-linear-sofic-groups-kill-rigid-compression-defects`. In rank
ultraproducts, fixed right ideals round with no property (T) and compressors
conserve them in every tensor degree
(`rank-ultraproduct-compressors-conserve-fixed-right-ideals`). That layer cannot
kill defects (`linear-scale-rank-conservation-does-not-kill-defects`). The Hamming
normalization proof fails in the rank metric exactly at rounding into expanding
pieces and at one-piece transport, where compressors can rotate multiplicity
coordinates. Every rank model of `R^x` must have the nine-leaf Kazhdan subgroup
fixing exactly what `R^x` fixes (`leavitt-rank-models-kazhdan-fixed-ideals-are-global`).
Neither direction of the gate is decided.
