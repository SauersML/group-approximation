---
rg: 2
id: pre-injective-automata-can-destroy-never-created-letters
kind: claim
title: A never-created letter of a pre-injective automaton is inert over two letters, but over three or more letters and any group containing F_2 it can be destroyed
distinct_from:
  finite-injective-charge-noncreation-forces-surjectivity: that forbids a finite-injective automaton from lowering a positive charge; this is the dual direction, raising the count of non-c sites, which the same finite hypothesis permits from three letters on.
  pair-distinct-ternary-rules-pre-injective-on-free-memory: that gives pre-injective, non-injective ternary rules on three free addresses with no letter structure; this is a quiescent never-created letter that is destroyed, and it uses the four-neighbour tree hull, not a site-triangle forest count.
  strict-automata-never-omit-separated-patterns: that is about injective automata omitting patterns; this is about pre-injective automata and the growth of a never-created letter's complement.
  amenable-groups-satisfy-the-garden-of-eden-theorem: that ties pre-injectivity to surjectivity over amenable groups; this builds its example over groups containing F_2, where the two notions come apart.
artifacts:
  - experiments/dual-charge-calibration-2026-09-17/verify_preinjective.py
  - experiments/dual-charge-calibration-2026-09-17/f2_binary_search.py
  - experiments/dual-charge-calibration-2026-09-17/ball_collisions.py
  - experiments/dual-charge-calibration-2026-09-17/rules_search.py
---

**ESTABLISHED 2026-09-20** by `pre-injective-automata-can-destroy-never-created-letters-proof`.

**Setting.** `G` is a group, `A` a finite alphabet and `τ` a cellular automaton on `A^G`. A letter `c` is
*never created* if `τ(x)(g) = c` implies `x(g) = c`. It is *inert* if `τ(x)(g) = c` exactly when `x(g) = c`.
`τ` is *pre-injective* if two configurations that differ at finitely many sites never have the same image.

**Statement.**
- **(a) Two letters.** If `|A| = 2` and `τ` is injective on the configurations that differ from the other
  letter's constant configuration at finitely many sites, then every never-created letter is inert. This holds
  over every group, and in particular whenever `τ` is pre-injective.
- **(b) Three or more letters.** Suppose `G` contains a free subgroup of rank two and `|A| >= 3`. Then there
  is a pre-injective `τ` on `A^G` with a quiescent, never-created letter `c` such that a configuration with one
  non-`c` site maps to one with exactly five non-`c` sites.

**Construction for (b).** Let `F_2 = <a, b>`, `A' = a^-1`, `B' = b^-1`, memory `{1, a, A', b, B'}`, and
alphabet `{c} ⊔ Z/m` with `m >= 2`. Choose maps `α, β : {c} ⊔ Z/m -> Z/m` whose pair `(α, β)` is injective.
For `m = 2` one choice is `α = (c, 0, 1) ↦ (0, 0, 1)` and `β = (c, 0, 1) ↦ (1, 0, 0)`. Put `φ_a = φ_b = α`,
`φ_A' = φ_B' = β`, and `Σ(k) = Σ_s φ_s(x(ks))` over `s ∈ {a, A', b, B'}`, taken mod `m`.
- If `x(k) = e ∈ Z/m`, then `τ(x)(k) = e + Σ(k)`.
- If `x(k) = c`, then `τ(x)(k) = c` when all four neighbours `ks` hold `c`, and `τ(x)(k) = Σ(k)` otherwise.

Over a larger group, `τ` uses the same memory inside `F_2`.

**Consequences.**
- **The dual charge theorem needs global injectivity from three letters on.** Need `ebb50f1d` asks whether an
  injective automaton with a quiescent, never-created `c` never raises the number of non-`c` sites of a finite
  configuration. By (b), no argument that uses only injectivity on asymptotic pairs can prove this for
  `|A| >= 3` over any group containing `F_2`. That covers the charge-level induction, Hall matching on finite
  configurations over any background, and Garden-of-Eden counting. The example is injective on all finite
  configurations over every background, yet one letter grows into five.
- **Where the induction dies.** In `charge-level-induction-and-colored-collision-corners`, a configuration of
  level `n` whose image had lower charge would collide with a lower level already shown to be filled. In the
  dual, images go *up*, into levels not yet filled, so there is nothing to collide with. The example shows this
  step cannot be repaired within finite configurations.
- **Sharp threshold.** By (a), the binary case of the need holds by finite methods alone. So `|A| = 3` is the
  first size where the need is open, and the obstruction is exact.
- **The example is not injective.** `F_2` is sofic, hence surjunctive (`sofic-groups-are-surjunctive`). If `τ`
  were injective it would be bijective, hence reversible by Curtis–Hedlund–Lyndon. It fixes `c^G` and never
  lowers the non-`c` count, so `reversible-automata-that-never-lower-rest-counts-preserve-them`, with rest symbol
  `c`, would force that count to be preserved, against the growth from one site to five. So the
  collisions of `τ` are pairs that differ at infinitely many sites. This matches the need's remark that a proof
  must use wandering configurations.
