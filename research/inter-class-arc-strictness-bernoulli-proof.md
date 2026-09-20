---
rg: 2
id: inter-class-arc-strictness-bernoulli-proof
kind: route
title: The uniform product measure turns sitewise absorption by an upset into sitewise equality for bijective automata
target: injective-automata-with-inter-class-transitions-are-strict
requires:
  - bijective-ca-preserve-uniform-bernoulli-measure
  - transition-digraph-capacity-lifts-give-nonsurjunctive-sizes
  - passive-fixing-injective-automata-are-surjective
---

Complete proof over every group `G`. Notation as in the target. `Ψ(x)(g) = μ((g^(-1)x)|_M)` with `1 ∈ M`,
where `(g^(-1)x)(h) = x(gh)`. So `Ψ(x)(g) = Ψ(g^(-1)x)(1)` and `(g^(-1)x)(1) = x(g)`. Write `ν` for the
uniform product measure on `B^G`.

**Imports, verbatim.**
- `bijective-ca-preserve-uniform-bernoulli-measure`: "Let `G` be any group, `A` a finite alphabet, `mu` the
  uniform product measure on `A^G`, and `tau: A^G -> A^G` a bijective cellular automaton. Then
  `tau_* mu = mu`."
- `transition-digraph-capacity-lifts-give-nonsurjunctive-sizes`, item 3: "With `g(τ) = 1`, `NS(G)` is
  cofinite." Its theorem is stated for `τ` strict on `A^G`, over any group, with `g(τ)` the gcd of the class
  sizes of `R(τ)`.
- `passive-fixing-injective-automata-are-surjective`: "Let `Φ` be an injective cellular automaton on `C^G`
  such that, for every configuration `x` and every `g` in `G`: if `x(g) ∈ P`, then `Φ(x)(g) = x(g)`; if
  `x(g) ∉ P`, then `Φ(x)(g) ∉ P`. Then `Φ` is surjective." (The two bullets of the source are joined.)

**Step 0 (a clopen null set is empty).** A clopen subset of `B^G` is a finite union of cylinders over finite
windows `F`, and each cylinder has `ν`-measure `|B|^(-|F|) > 0`. So a clopen set of measure `0` is empty.

**Step 1 (item 1, upset rigidity).** Let `Ψ` be bijective and `U` an upset. Put
`C = {x : x(1) ∈ U}`. It is clopen, and `ν(C) = |U|/|B|`.
- The upset property at `g = 1` says `x ∈ C ⇒ Ψ(x) ∈ C`, that is, `C ⊆ Ψ^(-1)(C)`.
- `Ψ` is continuous, so `Ψ^(-1)(C)` is clopen, and `Ψ^(-1)(C) \ C` is clopen.
- By the import, `ν(Ψ^(-1)(C)) = (Ψ_* ν)(C) = ν(C)`. So `ν(Ψ^(-1)(C) \ C) = 0`, and by Step 0 the set is
  empty. Hence `Ψ(x)(1) ∈ U ⇔ x(1) ∈ U`.
- Apply this to `g^(-1)x`. Then `Ψ(x)(g) ∈ U ⇔ x(g) ∈ U` for every `g`.
- So `Ψ` maps `U^G` into `U^G`, and its inverse does too: `Ψ(y) ∈ U^G` forces `y ∈ U^G`. Hence
  `Ψ(U^G) = U^G`.

**Step 2 (item 2, no one-way arcs).** Let `Ψ` be bijective and `(a, b) ∈ R(Ψ)` with `a`, `b` in different
classes. Let `U` be the set of letters reachable from `b` in `R(Ψ)`, with `b` included.
- `U` is closed under arcs, so it is an upset.
- `a ∉ U`. Otherwise `b` reaches `a` and `a -> b`, so `a` and `b` would share a class.
- The arc is realized: there are `x` and `g` with `x(g) = a` and `Ψ(x)(g) = b`. Then `Ψ(x)(g) ∈ U` and
  `x(g) ∉ U`, against Step 1.

So every arc lies inside a class. The weakly connected components are then unions of classes joined by no arc,
so each is a single class.

**Step 3 (item 3).** Let `Ψ` be injective with an arc between two classes. If `Ψ` were surjective it would be
bijective, against Step 2. So `Ψ` is strict. Its class sizes have gcd `g(Ψ)`, and a class of size `1` makes
`g(Ψ) = 1`, so the capacity-lift import applied to `Ψ` gives `NS(G)` cofinite.

**Step 4 (item 4).** Let `Ψ` be injective, and suppose `c` is never written at a site not holding `c`, that is,
`Ψ(x)(g) = c ⇒ x(g) = c`.
- *Inert case.* Suppose also `x(g) = c ⇒ Ψ(x)(g) = c`. Take `P = {c}`. Both hypotheses of
  `passive-fixing-injective-automata-are-surjective` hold, so `Ψ` is surjective, hence bijective.
- *Destroyed case.* Otherwise there are `x`, `g` with `x(g) = c` and `Ψ(x)(g) = d ≠ c`, so `(c, d) ∈ R(Ψ)`.
  The only arc into `c` is the loop at `c`, so no cycle passes through `c` and another letter, and `{c}` is a
  class. The arc `(c, d)` joins two classes, and Step 3 gives strictness and `NS(G)` cofinite.
- The two cases exclude each other and cover everything.

**Step 5 (item 5).** Let `Ψ` be injective and `U` a nonempty upset. Then `Ψ(U^G) ⊆ U^G`, and `Ψ|_(U^G)` is the
automaton on `U^G` whose local rule is the restriction to `U^M`. If `Ψ` were surjective it would be
bijective, and Step 1 would give `Ψ(U^G) = U^G`. So if `Ψ|_(U^G)` is not onto `U^G`, then `Ψ` is not
surjective, and being injective it is strict.

**Step 6 (item 6).** Let `Φ` on `(A ⊔ D)^G` be injective and extend `τ`, with no `D`-letter written at an
`A`-site. Then `A` is an upset of `R(Φ)` and `Φ|_(A^G) = τ`, which is not onto `A^G`. Step 5 makes `Φ`
strict, so `|A| + |D| ∈ NS(G)`.

**Checks.**
- No property of `G` is used: not countability, not soficity, not amenability.
- The only analytic input is measure invariance, used once, in Step 1.
- *Model tests on `Z`.*
  - The rule on `{0,1}^Z` that writes `0` wherever a site or a neighbour holds `0` has the one-way arc
    `1 -> 0`. Consistently with item 2 it is not bijective: the word `101` is an orphan, since output `1` at
    `g - 1` and at `g + 1` forces input `1` on `g - 2, ..., g + 2`, and then output `1` at `g`. It is also not
    injective, so Step 3 does not apply to it.
  - Bijective examples have only exact upsets. For a letter permutation, the classes are its cycles and every
    arc lies in one. For the shift, `R` is complete.
