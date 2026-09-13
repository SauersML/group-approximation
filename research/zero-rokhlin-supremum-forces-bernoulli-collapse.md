---
rg: 2
id: zero-rokhlin-supremum-forces-bernoulli-collapse
kind: claim
title: A group whose free ergodic actions all have zero Rokhlin entropy has isomorphic Bernoulli shifts of different base entropy
distinct_from:
  bernoulli-entropy-counterexample-constraints: that proves necessary conditions on a group where classification fails, among them a small Rokhlin supremum; this is the open converse, that the extreme case of zero supremum is sufficient for a failure.
  bernoulli-isomorphism-collapse-set-is-a-subgroup: that proves the structure of the set of failures on any group; this asks that the set be nontrivial whenever the Rokhlin supremum vanishes.
  every-group-has-positive-rokhlin-entropy-action: that is Seward's existence root; this is the bridge which, together with base-entropy classification for every group, would prove that root.
  some-group-has-isomorphic-bernoulli-shifts-of-different-entropy: that asks for one group with a collapse; this asks that zero Rokhlin supremum be a sufficient condition for a collapse on any group.
---

**OPEN.** Let `G` be a countably infinite group with `h^Rok_sup(G) = 0`, so every free
ergodic p.m.p. action of `G` has Rokhlin entropy `0`. Then `D(G) ≠ {0}` in the notation
of `bernoulli-isomorphism-collapse-set-is-a-subgroup`: there are finite bases of
different entropy with isomorphic Bernoulli shifts over `G`.

The strong form asks that all Bernoulli shifts with positive base entropy be
isomorphic, i.e. `X_h ≅ X_∞` for every `h > 0`.

**Payoff.**
- **The root would be as hard as Seward's question.** For every group, INV(G) and
  this claim for `G` give POS(G): if POS(G) failed, then `h^Rok_sup(G) = 0`, this
  claim gives a collapse, and INV(G) fails. So under this claim,
  `bernoulli-shift-entropy-classifies-for-every-group` is equivalent to
  `every-group-has-positive-rokhlin-entropy-action` (route
  `positive-rokhlin-via-classification-and-collapse`). A positive proof of the root
  would then prove Gottschalk's surjunctivity conjecture and Kaplansky's direct
  finiteness conjecture for all groups.
- **Dichotomy hosts.** On groups with `h^Rok_sup ∈ {0, ∞}`, such as the binary
  Leavitt unit group and Thompson's `V`, classification would be equivalent to
  positive Rokhlin entropy.
- **Refutation value.** A group with zero supremum over which base entropy still
  classifies would show that the root is strictly weaker than Seward's question, and
  would need an invariant that is not semicontinuous in the shift measure.
- **A counterexample from the Leavitt units.** With
  `leavitt-units-have-zero-rokhlin-entropy-supremum`, this claim gives a group where
  classification fails (route `leavitt-zero-supremum-and-collapse-give-bernoulli-failure`).
  A strict automaton over the binary Leavitt unit group would supply that zero supremum
  (`leavitt-zero-rokhlin-supremum-from-strict-automaton`).

**Consistency with what is established.** When `h^Rok_sup(G) = 0`:
- every Bernoulli shift of positive base entropy is a weak* limit of models of every
  other one, in both directions
  (`rokhlin-entropy-is-the-bernoulli-approximation-threshold`);
- every semicontinuous isomorphism invariant is constant on positive base entropies
  (`semicontinuous-invariants-blind-above-rokhlin-supremum`);
- Seward's Proposition 6.5 (arXiv:1501.03367v4) gives
  `h^Rok_G(L^G, λ^G | 𝓚^G) = min(H(𝓛 | 𝓚), h^Rok_sup(G)) = 0` for every coordinate
  Bernoulli factor. Every split Bernoulli factor already generates up to zero relative
  Rokhlin entropy.

## Attempts

- **Seward's recoding along the pseudogroup.** The equal-entropy isomorphisms of
  arXiv:1805.08279, Theorem 3.2, fix a common factor and apply Ornstein's theorem for
  `Z` along each orbit of an aperiodic pseudogroup element. That needs equal entropy
  along the orbits, and the entropy per step is set by the base.
  - Grouping labels into finite blocks per step does not help. The block sizes are
    integrable by mass transport, so the relative entropy per step stays finite and
    set by the base.
  - Infinite blocks would need a Borel enumeration of the infinite classes of a
    measure-preserving equivalence relation, invariant on each class. A class-invariant
    choice of first element is a transversal. That transversal is null, and so is its
    saturation.

  Dies at: a collapse has to recode along a nonamenable structure. No Ornstein-type
  theorem is available there.
- **Iterated absorption.** A collapse `X_h ≅ X_h × X_d` iterates to compatible factor
  maps `X_h → X_(nd)` with independent complements `C_n ≅ X_h`, decreasing in `n`. The
  limit factor is `X_∞`, and it is independent of `∩ C_n`. The two need not generate
  together: for i.i.d. signs `y_i`, the products `y_i y_(i+1)` and the tail miss the
  global sign. So the strong form does not follow from the weak form this way.
  - **Exact criterion** (`bernoulli-infinite-power-iff-approximate-half-absorption`). A self-square
    `X_h ≅ X_h × X_h` reaches `X_∞` exactly when, for every finite partition `R` and `ε > 0`, some exact
    splitting `X_h = A × C` with `A ≅ C ≅ X_h` has `R` within `ε` of `A`. Equivalently, automorphisms move
    any finite partition approximately into one fixed half. Choosing each splitting after the partition
    to be captured is known repairs the sign example.
- **Krieger generators near split factors.** Let `α_0` be the `λ`-coordinate partition
  of `λ^G × μ^G`, and `α` a generating partition with `ε = µ(α ≠ α_0)`. Record `α` on
  `{α ≠ α_0}` by a partition `η`, so `H(η) ≤ H(ε) + ε log(|L| + 1)` and
  `α ⊆ σ(α_0 ∨ η)`. By sub-additivity and Proposition 6.5,
  `min(H(μ), h^Rok_sup(G)) ≤ H(η)`. On groups with positive supremum, generators stay a
  definite distance from split i.i.d. factors. On groups with zero supremum there is no
  such local obstruction, but a collapse needs a generator that is *exactly* i.i.d.
  Dies at: exact independence in a limit, with no finitely determined property
  available.
- **Baire category.** Let `A(G, X, µ)` be the space of actions and `Y` the closure of
  the conjugacy class of a nontrivial Bernoulli shift. `Y` is the same for every base,
  because nontrivial Bernoulli shifts are weakly equivalent
  (`nontrivial-bernoulli-shifts-are-weakly-equivalent`, together with Abért–Weiss for
  infinite bases).
  - Each Bernoulli conjugacy class is dense in `Y`, analytic, and invariant under
    `Aut(X, µ)`, which acts on `Y` with a dense orbit.
  - By the topological 0-1 law (Kechris, *Classical Descriptive Set Theory*, 8.46),
    each class is meager or comeager in `Y`. So two non-meager Bernoulli classes
    coincide.

  Dies on product hosts. When `G` has an infinite central locally finite residually finite subgroup
  of infinite index, as Seward's `P × G` does, zero entropy along that subgroup is a dense `G_δ` in `Y`,
  so every Bernoulli class is meager (`bernoulli-classes-meager-on-central-locally-finite-hosts`).
  - **What survives: category among i.i.d. partitions.** Let `𝒫_λ` be the set of measurable
    `α: X_∞ → L` whose `G`-translates are i.i.d. with law `λ`, with the metric `µ(α ≠ β)`. Joint laws of
    finitely many translates are Lipschitz in `α`, so `𝒫_λ` is closed in `L^0(X_∞, L)` and Polish. The
    generating ones form a `G_δ` `𝒢_λ`: for a dense sequence `B_j` and `k ≥ 1`, "`B_j` is within `1/k`
    of a union of atoms of some finite window of translates" is open. `𝒢_λ ≠ ∅` iff `X_∞ ≅ X_λ`. So
    density of every such open set in `𝒫_λ` gives the strong form by Baire.
  - The meagerness argument does not transfer: every `α ∈ 𝒫_λ` spans a Bernoulli factor, whose entropy
    along the central subgroup is full.
  Dies at: density is a perturbation lemma. Perturb an exactly i.i.d. partition by a small amount,
  keeping exact independence, so that it captures a given set. That is an Ornstein-type copying step
  with no finitely determined property available.
  - **Finite bases (lane ex-bernoulli-rokhlin-complete, 2026-09-13).**
    - The same density for a finite-base shift `X_κ` is posed as `iid-generators-dense-at-zero-rokhlin-supremum`.
      Its Baire route into this claim is `zero-supremum-collapse-via-dense-iid-generators`.
    - Its non-exact half holds at zero supremum. Generating partitions are `d^Rok`-dense exactly when the
      Rokhlin entropy is `0` (`generators-dense-iff-zero-rokhlin-entropy`, from Seward's small-support
      generators). So the perturbation lemma above is purely an exactness statement.
    - On nonamenable groups with positive supremum the density fails for every distribution, near i.i.d.
      partitions carried by small Bernoulli factors (`iid-generators-not-dense-at-positive-rokhlin-supremum`).
- **Finitely determined properties (lane ex-bernoulli-zero-supremum, 2026-09-13).** Over `Z`, Ornstein copies
  processes through finite determination. Over every group, Seward derives it from RBS
  (`seward-bernoulli-measures-finitely-determined-under-rbs`, arXiv:1804.05269v3, Corollary 1.6).
  - Shift models of a rigid action stay at d-bar distance `≥ (1 − Σ_l λ(l)^2)/2` from `λ^G`
    (`rigid-actions-have-no-dbar-close-bernoulli-models`). At zero supremum they converge weak* to `λ^G`
    with the same Rokhlin entropy `0`. So on a group with a rigid free ergodic action, no nontrivial Bernoulli
    measure is finitely determined (`bernoulli-measures-not-finitely-determined-at-zero-supremum`).
  - Rigid free ergodic actions exist on maximally almost periodic groups (so on `P × G` with `G` residually
    finite, and on the Kun–Thom groups) and on Thompson's `V` (`thompson-v-has-a-rigid-free-ergodic-action`).
    On `V`, finite determination of one Bernoulli measure is equivalent to POS(V)
    (`thompson-v-bernoulli-finitely-determined-iff-pos`).
  Dies at: a copying argument at zero supremum must restrict to a class of measures that excludes models of
  rigid actions, such as models of Bernoulli shifts. No d-bar estimate on such a class is known.
- **Algebraic absorption (lane ex-bernoulli-negative).** A stable finiteness failure over
  `F_p[G]` makes a Bernoulli shift absorb a nontrivial algebraic factor,
  `b ≅ b × X_P` (`stable-finiteness-failure-is-algebraic-bernoulli-absorption`). That is
  the collapse form with `X_P` in place of a Bernoulli factor. The entropy that
  co-induction from finite subgroups can add is the lifted p-adic trace, and module
  isomorphisms conserve it (`finite-subgroup-induced-absorption-conserves-entropy`). So
  algebra supplies absorption but not Bernoullicity of the absorbed factor. Such a failure
  would also bound the supremum through `strict-automaton-bounds-rokhlin-supremum`, and on
  dichotomy hosts force it to `0`, which is the hypothesis here.
- **Category in joining space (lane ex2-bernoulli-exactification, 2026-09-13).** Let `A` and `B` be the factor
  joinings between `X_λ` and `X_κ` in the two directions. Suppose every endomorphism of each shift has approximate
  right inverses by endomorphisms. Then `A ⊆ cl(B)` and `B ⊆ cl(A)`, both sets are dense `G_δ` in `cl(A) ∩ cl(B)`,
  and some joining is an isomorphism (`bernoulli-isomorphism-from-approximate-right-inverses`).
  - So this claim follows from `zero-supremum-endomorphisms-have-approximate-right-inverses`, by route
    `zero-supremum-collapse-via-approximate-right-inverses`.
  - The input is weaker than the partition-space exactification above, which already contains total finite
    collapse (`iid-density-iff-collapse-and-endomorphism-density`).
  - The argument cannot run in the space of all ergodic joinings on groups with a proper finite-index subgroup.
    Averaging coset-dependent right translations over the cosets gives ergodic self-joinings with a finite factor,
    and these are not weakly contained in the Bernoulli shift. This is a sketch, recorded on the node.
  - The property fails for every finite base at positive supremum, through Bowen's Proposition 9.4 mechanism. Over
    `Z` it holds, by the Burton–Keane–Serafin residual factor theorem.

  Dies at: approximate right inverses, with exact i.i.d. law, for non-invertible endomorphisms whose fibres spread
  along a nonamenable structure. An example is the Ornstein–Weiss map on a group containing `F_2`.
  - **Refuted where `F_2 <= G` (same lane).** There the Ornstein–Weiss endomorphism has no approximate right inverses,
    by Kesten's spectral bound. No two Bernoulli shifts of different entropy both have approximate right inverses,
    and generating i.i.d. partitions are dense for no pair of different entropies
    (`ornstein-weiss-map-has-no-approximate-right-inverses`). So neither the joining-space route nor the
    partition-space route can give a collapse over a group containing `F_2`, such as Thompson's `V`, at any
    supremum. Over such groups a proof of this claim needs a different mechanism.
  - **Refuted on every nonamenable group (same lane).** Along Bowen's measurable free subrelation the same spectral
    bound holds (`spectral-gap-refutes-exactification-on-nonamenable-groups`). On every nonamenable group, hence on
    every group this claim concerns:
    - no two Bernoulli shifts of different entropy both have approximate right inverses;
    - generating i.i.d. partitions are dense for no pair of different entropies;
    - the two factor-joining sets are not each in the closure of the other.

    So both category routes into this claim have inputs equivalent to `every-group-has-positive-rokhlin-entropy-action`,
    under which this claim is vacuous. A proof must use a mechanism other than genericity in partition or joining
    space, and must not produce approximate right inverses.
