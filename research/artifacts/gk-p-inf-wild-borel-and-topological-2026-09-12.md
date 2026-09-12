# Borel-structurability blindness and topological invariants of full shifts

Lane `gk-p-inf-wild`, 2026-09-12. Supports these Cairn claims:
- `borel-structurability-invariants-are-bernoulli-base-blind`;
- `seward-tucker-drob-free-borel-actions-map-to-2-shift`;
- `full-shifts-with-different-alphabets-are-not-conjugate`.

The lane's brief was a lower bound for Bernoulli Rokhlin entropy on a nonsofic group by
unconventional means: model theory and ultraproducts of actions, descriptive set theory and Borel
combinatorics, topological versions, and operator-algebraic entropies. This artifact records what
each class of invariant can and cannot see.

**Correction (2026-09-12).** An earlier version of Section 3 presented alphabet invariance under
topological conjugacy as an open target sitting strictly between the goal and the measurable
classification. It is elementary for every group (Proposition 3.0). Section 3 is rewritten, and
Section 5 records what topological counting can see on groups with no proper finite-index subgroup.

Division of labour with sibling lanes:

* Weak-equivalence and orbit-relation invariants (Abért–Weiss, cost, l2-Betti numbers, ultraproduct
  factors) belong to lane `gk-p-inf-cost`, which lands them as its own claims.
* Factor non-monotonicity (Ornstein–Weiss, Bowen's weak isomorphism arXiv:0812.2718) is already
  recorded in the Attempts of `every-group-has-positive-rokhlin-entropy-action` and
  `bernoulli-shift-entropy-classifies-for-every-group`. It is used below only as a remark.
* Bowen's f-invariant and co-amenability belong to lane `gk-p-inf-f`.
* Almost-everywhere codes into fewer symbols are `measurable-alphabet-compression-over-leavitt-units`
  (artifact `research/artifacts/measurable-alphabet-compression-2026-09-12.md`).

## 1. Borel-structurability invariants are blind to the base

**Source (read 2026-09-12).** B. Seward and R. D. Tucker-Drob, *Borel structurability on the
2-shift of a countable group*, arXiv:1402.4184, Ann. Pure Appl. Logic 167 (2016) 1–21. Abstract,
verbatim: "We show that for any infinite countable group G and for any free Borel action
G ↷ X there exists an equivariant class-bijective Borel map from X to the free part Free(2^G) of the
2-shift G ↷ 2^G."

**Definitions.** A free Borel action is a Borel action of `G` on a standard Borel space with all
stabilizers trivial. A Borel map `f: X -> Y` between free Borel actions is *class-bijective* if it
is equivariant and bijective from each orbit onto an orbit. Call an invariant `J` of free Borel
`G`-actions, with values in a partially ordered set, *monotone under class-bijective maps* if
`J(X) <= J(Y)` whenever a class-bijective Borel map `X -> Y` exists.

Examples: the Borel chromatic number of the Schreier graph for a fixed finite generating set; the
existence of a Borel perfect matching or a Borel proper edge colouring with a given number of
colours, ordered by "Y has it implies X has it"; and in general every Borel structurability property
of the orbit equivalence relation, since structures pull back along class-bijective maps. The
source's introduction gives the chromatic-number case.

**Proposition 1.1.** Let `G` be a countably infinite group. Every invariant `J` monotone under
class-bijective maps takes the same value on the free parts `Free(q^G)` for all `q >= 2`.

*Proof.* By the source theorem there is a class-bijective Borel map `Free(q^G) -> Free(2^G)`, so
`J(Free(q^G)) <= J(Free(2^G))`. The inclusion `{0,1} ⊂ {0,...,q-1}` induces an equivariant Borel
injection `2^G -> q^G`. It preserves stabilizers, because the shift action is the same on both
sides, so it maps `Free(2^G)` into `Free(q^G)`. An equivariant map between free actions is bijective
from each orbit onto an orbit, since both orbits are copies of `G`. So the inclusion is
class-bijective and `J(Free(2^G)) <= J(Free(q^G))`. QED

**Calibration.** Over an infinite amenable group the Bernoulli shifts `(q^G, uniform)` have
Kolmogorov–Sinai entropy `log q`, which separates all `q`, while Proposition 1.1 makes every `J`
constant. So no invariant of this class computes entropy. The Borel classes of the free parts carry
no measure and cannot see a base.

**What survives.** A lower bound on nonsofic hosts must be an isomorphism invariant of the measured
action that is:

* not monotone under factor maps (all nontrivial Bernoulli shifts over a group containing `F_2`
  factor onto each other, by Bowen's weak isomorphism theorem; every nonsofic group known here
  contains `F_2`);
* not a weak-equivalence invariant (lane `gk-p-inf-cost`);
* not determined by the Borel structure of the free part (Proposition 1.1).

## 2. Model theory and ultraproducts

Weak containment of p.m.p. actions has an ultraproduct characterization. Conley, Kechris and
Tucker-Drob, *Ultraproducts of measure preserving actions and graph combinatorics*, Ergodic Theory
Dynam. Systems 33(2) (2013), give "equivalent definitions of weak containment in terms of the space
of all actions and ultraproducts of actions". The theorem statement was not read verbatim here: the
PDF fetch failed on a certificate error. So invariants that pass to factors of ultrapowers are
weak-containment invariants, and they fall under `gk-p-inf-cost`'s obstruction. No separate node is
landed for this section.

Where a model-theoretic invariant could still help is the finitary witness of
`bernoulli-rokhlin-deficit-has-a-finitary-witness`. A deficit is a Sigma^0_1 statement over the word
problem, and maximality is Pi^0_1 on a host with decidable word problem. That is a statement about
exact incidence patterns, not approximate statistics, which is why it escapes weak equivalence.

## 3. Alphabet size under topological conjugacy is elementary

**Proposition 3.0.** Let `G` be any group and `A`, `B` finite alphabets. If there is an equivariant
injection `A^G -> B^G`, continuous or not, then `|A| <= |B|`. So full shifts on alphabets of
different sizes are never conjugate.

*Proof.* A configuration fixed by every element of `G` is constant, so `Fix_G(A^G)` has `|A|`
points. An equivariant injection maps fixed points to fixed points, injectively. QED

The same count with a finite-index subgroup `K` gives `|A|^[G:K] <= |B|^[G:K]`, which is the lead's
calibration. The index-one case already settles every group.

**Propositions 3.1 and 3.2, kept as calibration.** Both are correct and both are now redundant.

* *From surjunctivity.* If `phi: A^G -> B^G` is a conjugacy with `|A| > |B|` and `iota: B^G -> A^G`
  is induced by an injection `B -> A`, then `iota o phi` is an injective, non-surjective cellular
  automaton (Curtis–Hedlund–Lyndon). So a surjunctive `G` has no such conjugacy.
* *From Bernoulli maximality.* Pushing the uniform measure through `phi` gives a measured copy
  generated by the time-zero partition of `B^G`, so `h^Rok(A^G) <= log |B| < log |A|`.

**Why topology is trivial and measure is not.** Conjugacies see fixed and periodic points, and every
Bernoulli measure gives them measure zero. Once they are discarded, alphabet size is exactly the
open question `measurable-alphabet-compression-over-leavitt-units`. Its artifact records that a
continuous code injective almost everywhere is pre-injective, and that pre-injective non-surjective
automata exist over every nonamenable group. So neither topological extreme (full injectivity, where
fixed points obstruct, or pre-injectivity, which is too weak) is the right intermediate. The genuine
intermediate is measurable.

## 4. Operator-algebraic invariants, status

* **Crossed product alone.** For uniform `q`, Fourier transform identifies
  `L^inf(q^G) ⋊ G` with the group von Neumann algebra `L((Z/q) wr G)`. Over an infinite amenable `G`
  this is an injective II_1 factor for every `q`, hence the hyperfinite factor by Connes' theorem
  (context, not imported). So invariants of the ambient algebra alone are blind to `q` over amenable
  groups, where entropy is not.
* **Cartan pair.** The pair `L^inf(q^G) ⊂ L^inf(q^G) ⋊ G` determines the action up to orbit
  equivalence (Singer; Feldman–Moore). Its invariants are orbit-equivalence invariants and belong to
  `gk-p-inf-cost`'s class.
* **Microstates.** Unitary (Hilbert–Schmidt) microstate spaces for the crossed product have volume
  at scale `exp(c n^2)`. The Shannon data of a partition of `X` sits at scale `exp(n H)`. Without a
  renormalized second-order entropy that isolates the abelian Cartan part, counting unitary models
  does not see base entropy. This is recorded as where the idea stops, not as a theorem.

## 5. Topological counting for strict automata on groups without finite-index subgroups

Let `tau` be an injective, non-surjective cellular automaton on `A^G` with image `X`, missing a
pattern `p` on a window `Omega`. Then `tau` is a conjugacy `A^G -> X`, so every conjugacy invariant
of `A^G` is shared by `X`. This section tests the invariants the lead proposed on groups with no
proper finite-index subgroup, the hard case, which includes the canonical simple Kazhdan hosts.
Convention: `(g.x)(h) = x(g^-1 h)`, and automata read right translates `h omega`.

**5.1 Periodic points.** For a normal subgroup `N`, `tau` maps `Fix_N(A^G)`, identified with
`A^(G/N)`, into itself as a cellular automaton over `G/N`. If `G/N` is surjunctive, `Fix_N(A^G)`
lies in `X`. That is the periodic-point proof that residually surjunctive groups are surjunctive
(context, not imported). `Fix_K(A^G)` is finite exactly when `[G:K]` is finite. In an infinite simple
group a finite-index subgroup contains its normal core, which has finite index and is normal, hence
is `G`. So the only finite fixed-point set is the constants, which `tau` permutes, and counting gives
nothing beyond Proposition 3.0.

**5.2 Finite subgroups modulo normalizers.** Let `F` be a finite subgroup. `Fix_F(A^G)` consists of
the configurations constant on the right cosets `Fh`, identified with `A^(F\G)`. It is invariant
under the normalizer `N(F)`, which acts on `F\G` by `n.Fh = Fnh`. The stabilizer of `Fh` is `F`, so
`N(F)/F` acts freely, with orbit set `N(F)\G`. Hence

    Fix_F(A^G) ≅ (A^(N(F)\G))^(N(F)/F),

a full shift over `N(F)/F` whose alphabet `A^(N(F)\G)` is a Cantor set whenever `[G:N(F)]` is
infinite. In an infinite simple group this holds for every nontrivial finite `F`: if `N(F)` had
finite index it would be `G` by 5.1, so `F` would be a finite normal subgroup, hence trivial.

* `tau` restricts to an injective `N(F)`-equivariant continuous self-map of `Fix_F(A^G)`, the
  same local rule read on the right Schreier graph of `F\G`. The index set has infinitely many
  `N(F)/F`-orbits, so no cocompact symmetry is available.
* Over a Cantor alphabet `K = A^N`, the map `(c_0, c_1, ...) -> (a, c_0, c_1, ...)` applied at every
  site is continuous, injective, equivariant and not surjective. So no surjunctivity principle holds
  for that class, and Fix_F carries no finite count.

Where it dies: finite subgroups yield only restricted automata on less symmetric index sets, which is
a problem of the same kind (compare `end-fixing-tree-symmetries-carry-strict-automata`).

**5.3 Pattern counts on windows.** A conjugacy-invariant count of patterns on large windows that drops
on proper subshifts would decide the goal. Over nonamenable groups ball-growth pattern entropy is not
monotone under codes of positive radius. Over `F_2 = <a, b>`, the Ornstein–Weiss block code
`x -> (x(g) + x(ga), x(g) + x(gb)) mod 2` pushes the uniform measure on `2^(F_2)` to the uniform
measure on `4^(F_2)` (context; see Section 4 of
`research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md`). Its image is closed with full measure,
so it is all of `4^(F_2)`. A radius-one factor map thus raises ball entropy from `log 2` to `log 4`.
Growth counts become invariants only with Følner sets or finite models, and neither is available on
the hosts.

**5.4 Homology and clopen invariants.**

* *Group homology.* `H_*(G; C(A^G, Z))` is a conjugacy invariant. A strict `tau` gives a
  surjective, non-injective equivariant endomorphism `f -> f o tau` of `C(A^G, Z)`. It is surjective
  because a locally constant function on the closed set `X` extends to a locally constant function
  on `A^G`. Its kernel is the set of functions vanishing on `X`. On coinvariants the uniform measure
  `mu` defines a functional, and composing with `tau` gives integration against `tau_* mu`.
  Comparing the two is `every-injective-ca-preserves-uniform-bernoulli-measure`; this gives no new
  constraint.
* *Clopen type semigroup.* `X` is closed, invariant and nowhere dense. Its complement contains every
  translate of the cylinder `[p]`, and these translates meet every cylinder, because `G` is infinite
  and a translated window can be made disjoint from any finite window. So clopen invariants of `A^G`
  do not restrict to `X`. Dead.

**5.5 Summary.** On groups with no proper finite-index subgroup, topological counting reduces to the
`|A|` constants. The remaining candidate invariants are either the measurable targets already on main
or dead.

No lower bound on Bernoulli Rokhlin entropy for any nonsofic group is produced here.
