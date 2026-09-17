---
rg: 2
id: thompson-f-finite-state-flows-cannot-prove-nonamenability
kind: claim
title: No expansion certificate for the positive monoid of Thompson's F can be computed from a finite tree automaton run on the forest, because every finite automaton carries an idempotent state measure
distinct_from:
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that makes non-amenability equivalent to doubling of some monomial set; this uses the flow form of that criterion and proves that no flow read off from finitely many tree states can witness it.
  thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs: that gives a sufficient order-based condition for doubling and rules out lexicographic orders by computation; this rules out, for every finite S and every ratio above 1, all flows that depend on the forest only through a finite automaton profile and the number of trees.
  thompson-f-ore-obstructions-must-see-finite-support: that rules out leading-term invariants and division-ring overrings for non-Ore pairs; this rules out finite-state expansion flows, a different certificate shape, by a random-forest averaging argument.
  thompson-f-moment-data-cannot-certify-nonamenability: that is about finitely many return probabilities; this is about local combinatorial transport rules on the positive monoid.
  thompson-f-cardinality-certificates-need-tower-degree: that bounds the degree at which non-doubling can be certified (amenable side); this constrains the information a doubling certificate must use (non-amenable side).
  thompson-f-evacuation-schemes-need-capacity-three: that bounds capacities on one Cayley graph; this is capacity-independent and says which state a transport rule must read.
artifacts:
  - experiments/thompson-f-finite-automaton-certificates-2026-09-17/check_idempotent_forest_model.py
  - experiments/thompson-f-finite-automaton-certificates-2026-09-17/output.txt
---

**ESTABLISHED** through `thompson-f-finite-state-flows-cannot-prove-nonamenability-proof`
(direct proof; one classical import, Hall's theorem for locally finite bipartite graphs; not
independently reviewed; no priority claimed).

**Setting.** `M` is the positive monoid of `F`. It is identified with the set `Φ` of forests
`y = (t_0, t_1, ...)` of finite binary trees, almost all trivial, where `x_k` acts by merging roots `k` and
`k+1` (Belk–Brown forest diagrams). For finite `S ⊆ M` and `λ > 0`, a *certificate* is a function
`w : S × M → [0, ∞)` with

- (out) `Σ_(s ∈ S) w(s, y) >= λ` for every `y`;
- (in) `Σ_(s ∈ S, s y = z) w(s, y) <= 1` for every `z`.

**Certificates are exactly non-amenability proofs.**
- A certificate with `λ > 1` gives `|S Y| >= λ |Y|` for all finite `Y`, so `F` is not amenable.
- If `F` is not amenable, a `{0,1}`-valued certificate with `λ = 2` and `S = S_(m+1,m+d+1)` exists
  (Hall's theorem applied to item 2 of `thompson-f-nonamenable-iff-some-monomial-set-doubles`).

A *finite tree invariant* is a finite set `Q` with a map `δ : Q × Q → Q` and a leaf state `ℓ`. It assigns
`q(•) = ℓ` and `q(L ∧ R) = δ(q(L), q(R))`; this is a deterministic bottom-up tree automaton. The profile
of a forest is `p(y) = (q(t_0), q(t_1), ...)`, and `N_y` is the number of trees up to the last nontrivial
one.

**Theorem.** Let `S ⊆ M` be finite, `(Q, δ, ℓ)` a finite tree invariant, and `G` an arbitrary
nonnegative function, with no computability or continuity assumption. Put `w(s, y) = G(s, p(y), N_y)`.
Then

`sup_z Σ_(s y = z) w(s, y)  >=  inf_y Σ_s w(s, y)`.

So no certificate with `λ > 1` has this form.

**Where the method sits.**
- *Covered.* The rule sees all trees jointly. Any finite amount of shape near the roots, sizes and
  depths modulo fixed integers, membership of each tree in regular tree languages, and finite products
  of such data are all finite tree invariants.
- *Mechanism.* Brouwer's theorem gives a probability `π` on the reachable states with
  `δ_*(π ⊗ π) = π`. In a random forest of `N` trees, each a complete top with independent `π`-typed
  subtrees underneath, every split `split_s` is defined, and the profile of `split_s Y` has the same
  law as the profile of `Y` with `N` shifted by `deg s`. Averaging (in) over this model gives the
  inequality. The model needs `Y ∈ ∩_(s ∈ S) sM`, which is the Ore property of `M`.
- *Calibration.* In the free monoid on `{a, b}` the constant rule `w ≡ 1` is a certificate with
  `λ = 2`. The theorem does not apply there because `aM ∩ bM = ∅`.
- *Gate.* The same proof works for any tree invariant into a countable magma that carries an
  idempotent probability measure on its reachable states. The identity invariant (the free magma),
  size and depth carry none: the least size, or depth, in the support strictly increases under
  `δ_*`. By Moore, arXiv:1807.05469, the free binary system has no idempotent mean either. So a
  certificate, if one exists, must read unbounded tree data such as sizes, depths or exact shapes, and
  must break every finite-state stationarity. This is exactly where Moore's idempotent-mean route
  failed.

**Scope.**
- Not covered: rules that also depend on the total caret count, rules for flows on the Cayley graph of
  `F` itself (pairs of forests), and rules continuous in a compact infinite state space.
- The theorem proves neither answer. It kills one class of witnesses for `thompson-f-is-not-amenable`.

**Check.** The artifact script checks four things.
- The forest model: the relations of `M` and injectivity on 462 normal forms.
- Idempotent measures for 16 random 2- and 3-state automata, all with support of at least 2 states.
- By exact enumeration, for `S = X_2` and `S = X_2 ∪ S_(3,5)`: the profile law of `split_s Y` equals the
  i.i.d. law of length `N + deg s`, with worst total variation `9.7e-15`.
- A control where a non-idempotent `π` gives total variation `0.875`.
