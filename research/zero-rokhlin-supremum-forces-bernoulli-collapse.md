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

  Dies at: no argument is known that any Bernoulli class is non-meager in `Y` when the
  supremum is zero.
- **Algebraic absorption (lane ex-bernoulli-negative).** A stable finiteness failure over
  `F_p[G]` makes a Bernoulli shift absorb a nontrivial algebraic factor,
  `b ≅ b × X_P` (`stable-finiteness-failure-is-algebraic-bernoulli-absorption`). That is
  the collapse form with `X_P` in place of a Bernoulli factor. The entropy that
  co-induction from finite subgroups can add is the lifted p-adic trace, and module
  isomorphisms conserve it (`finite-subgroup-induced-absorption-conserves-entropy`). So
  algebra supplies absorption but not Bernoullicity of the absorbed factor. Such a failure
  would also bound the supremum through `strict-automaton-bounds-rokhlin-supremum`, and on
  dichotomy hosts force it to `0`, which is the hypothesis here.
