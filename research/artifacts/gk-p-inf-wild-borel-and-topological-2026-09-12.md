# Borel-structurability blindness and the topological alphabet-size target

Lane `gk-p-inf-wild`, 2026-09-12. Supports the Cairn claims
`borel-structurability-invariants-are-bernoulli-base-blind`,
`seward-tucker-drob-free-borel-actions-map-to-2-shift` and
`full-shifts-with-different-alphabets-are-not-conjugate`.

The lane's brief was a lower bound for Bernoulli Rokhlin entropy on a nonsofic group by
unconventional means: model theory and ultraproducts of actions, descriptive set theory and Borel
combinatorics, topological versions, and operator-algebraic entropies. This artifact records what
each class of invariant can and cannot see, and one topological target that sits strictly between
the goal and the measurable classification.

Division of labour with sibling lanes:

* Weak-equivalence and orbit-relation invariants (Abért–Weiss, cost, l2-Betti numbers, ultraproduct
  factors) belong to lane `gk-p-inf-cost`, which lands them as its own claims.
* Factor non-monotonicity (Ornstein–Weiss, Bowen's weak isomorphism arXiv:0812.2718) is already
  recorded in the Attempts of `every-group-has-positive-rokhlin-entropy-action` and
  `bernoulli-shift-entropy-classifies-for-every-group`. It is used below only as a remark.
* Bowen's f-invariant and co-amenability belong to lane `gk-p-inf-f`.

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
second paragraph of the source abstract gives the chromatic-number case.

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

## 3. A topological target: alphabet size under conjugacy

**Claim.** For every countably infinite group `G` and finite alphabets `A`, `B` with `|A| != |B|`,
the full shifts `A^G` and `B^G` are not topologically conjugate. A topological conjugacy is an
equivariant homeomorphism, which by Curtis–Hedlund–Lyndon is a sliding block code with a
sliding-block inverse.

**Proposition 3.1 (from the goal).** If `G` is surjunctive, the claim holds for `G`.

*Proof.* Suppose `phi: A^G -> B^G` is a conjugacy. By symmetry (use `phi^-1`) assume `|A| > |B|`,
and fix an injection `B -> A`. It induces an equivariant continuous injection `iota: B^G -> A^G`.
Then `iota o phi: A^G -> A^G` is continuous, equivariant and injective, hence a cellular automaton
by Curtis–Hedlund–Lyndon. Its image lies in `iota(B^G)`, a proper closed subset of `A^G`. So it is
injective and not surjective, and `G` is not surjunctive. QED

**Proposition 3.2 (from Bernoulli maximality).** If
`h^Rok_G(A^G, uniform) = log |A|` for every finite alphabet `A`, the claim holds for `G`.

*Proof.* Let `phi: A^G -> B^G` be a conjugacy with `|A| > |B|`, `mu` the uniform product measure and
`nu = phi_* mu`. Then `phi` is an isomorphism of the measured actions `(A^G, mu)` and `(B^G, nu)`,
and Rokhlin entropy is an isomorphism invariant. The time-zero coordinate partition of `B^G`
generates the Borel sigma-algebra under the shift and has Shannon entropy at most `log |B|`. So
`h^Rok(A^G, mu) = h^Rok(B^G, nu) <= log |B| < log |A|`, contradicting maximality. QED

**Scope and use.**

* The claim is weaker than both hypotheses. A conjugacy is a very special strict design: both
  composites are identities, on two different alphabets.
* For a counterexample search it is a sharper negative target. A conjugacy across alphabet sizes
  refutes Gottschalk for `G` (Proposition 3.1) and gives an explicit Bernoulli deficit certificate
  (Proposition 3.2) at the same time.
* The pair `(phi, phi^-1)` is two local rules whose forward and reverse tables both give identities.
  So the filters of `forward-relations-of-a-counterexample-have-a-nonsofic-core` and
  `table-groups-are-memory-holonomy-groups` apply to both composites. Over a host with decidable
  word problem, existence of a conjugacy with given memories is Sigma^0_1.
* Over sofic groups the claim holds by sofic entropy (context, not imported here). Over nonsofic
  hosts it is open for the same reason as everything else in the region.

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

No lower bound on Bernoulli Rokhlin entropy for any nonsofic group is produced here.
