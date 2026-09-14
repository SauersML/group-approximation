---
rg: 2
id: passive-fixing-injective-automata-are-surjective
kind: claim
title: An injective automaton that leaves every passive site in place and keeps active sites active is surjective
distinct_from:
  surjunctivity-failure-descends-to-binary-alphabet: that asks whether strictness moves down to two symbols with the memories allowed to change; this proves, over every group, that no extension which leaves a reserved set of symbols in place and never writes a reserved symbol at an unreserved site can be strict.
  strict-rule-pairs-ascend-to-larger-alphabets: that asks whether strict rules for fixed tables extend to more symbols; this rules out, at group level and at every alphabet size, the extensions that keep the added symbols fixed and output original symbols at original sites.
  amenable-groups-satisfy-the-garden-of-eden-theorem: that derives surjectivity from pre-injectivity on amenable groups; this derives surjectivity from injectivity on every group, under a condition on where the automaton writes.
artifacts:
  - research/artifacts/gk3-alphabet-descent-2026-09-14.md
---

**ESTABLISHED** by `passive-fixing-injective-automata-surjective-proof`.

Let `G` be a group, `C` a finite alphabet and `P ⊆ C` a nonempty set of *passive* symbols. Let `Φ` be an
injective cellular automaton on `C^G` such that, for every configuration `x` and every `g` in `G`:
- if `x(g) ∈ P`, then `Φ(x)(g) = x(g)`;
- if `x(g) ∉ P`, then `Φ(x)(g) ∉ P`.

Then `Φ` is surjective.

**Consequences.**
- **Extensions by reserved symbols.** Let `τ` be a strict automaton on `A^G` and `C = A ⊔ D` with `D`
  nonempty. An injective automaton on `C^G` that leaves `D`-symbols in place and outputs `A`-symbols at
  `A`-sites is surjective, so it is not strict. The walls construction of
  `strict-rule-pairs-ascend-to-larger-alphabets` (star at starred sites, raw symbols within radius `R`,
  `τ`-values elsewhere) has this form, whatever `R` and whatever rule is used near the stars. So its
  failure is not a defect of the annulus bookkeeping: every design of that shape fails.
- **What a strict extension must do.** A strict automaton on `(A ⊔ D)^G`, for ascent or for descent
  through a coding, must on some configuration write at a `D`-site, or write a `D`-symbol at an `A`-site.
- **Descent through `G × F`.** For a finite group `F`, a binary automaton over `G × F` is an automaton on
  `({0,1}^F)^G` commuting with the translations of `F` along fibers. If it leaves the two constant fibers
  `0^F` and `1^F` in place and sends non-constant fibers to non-constant fibers, it is surjective once it
  is injective. A binary strict automaton over `G × F` must rewrite some constant fiber, or make some
  non-constant fiber constant.

**Scope.** The conditions are sitewise. Designs defined as the identity off the image of a coding, and
designs in which relays reading a reserved symbol output it (the erasure design), are not covered.
