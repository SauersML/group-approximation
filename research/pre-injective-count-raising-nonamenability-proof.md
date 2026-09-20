---
rg: 2
id: pre-injective-count-raising-nonamenability-proof
kind: route
title: Support-flag Bartholdi automata at non-amenable groups, Bernoulli preservation at amenable ones
target: pre-injective-count-raising-characterizes-nonamenability
requires:
  - amenable-groups-satisfy-the-garden-of-eden-theorem
artifacts:
  - experiments/pre-injective-count-raising-2026-09-17/verify_flag_bartholdi.py
---

Notation: `τ(φ)(g)` depends on `φ` restricted to `Mg` for a finite memory `M`. A letter-dual automaton has
`τ(0^G) = 0^G`, and `φ(g) ≠ 0` implies `τ(φ)(g) ≠ 0`. So `supp τ(φ) ⊇ supp φ` for every `φ`.

**Imports.** All are quoted verbatim from L. Bartholdi (with an appendix by D. Kielak), *Amenability of groups is
characterized by Myhill's Theorem*, J. Eur. Math. Soc. 21 (2019), arXiv:1605.09133, from text extracted from the PDF.

- (B1) Theorem 1.1: "Let G be a non-amenable group. Then there exists a cellular automaton carried by G that admits
  Gardens of Eden but no mutually erasable patterns."
- (B2) From its proof. The combinatorial step ends with: "and furthermore we have obtained ⋃_{s∈S} X_s ⫋ Y." Then:
  "Let K be a large enough finite field (in a sense to be precised soon), and set A := K^Y. For each s ∈ S, choose a
  linear map α_s : A → K^{X_s} ⊂ A". Next: "Define now a cellular automaton with stateset A and carrier G by
  Θ(φ)(g) = Σ_{s∈S} α_s(φ(sg)). Clearly Θ admits gardens of Eden: for every φ ∈ A^G, we have
  Θ(φ)(1) ∈ K^{(⋃_{s∈S} X_s)} ⫋ A." Next: "it is enough to show, for φ ∈ A^G non-trivial and finitely supported, that
  Θ(φ) ≠ 0". It ends: "so ψ ≠ 0 and we have proven that Θ admits no mutually erasable patterns." Here `S` is finite.
- (B3) Introduction: "Hedlund proved in [7, Theorem 5.4], for G = Z, that a cellular automaton preserves Bernoulli
  measure if and only if it has no GOE. This result was generalized by Meyerovitch to amenable groups [10, Proposition
  5.1]." The Bernoulli measure is the uniform one: "for every pattern φ ∈ A^Y it assigns measure 1/#A^{#Y} to the clopen
  set". [10] is T. Meyerovitch, *Finite entropy for multidimensional cellular automata*, Ergodic Theory Dynam. Systems
  28 (2008).
- (G) `amenable-groups-satisfy-the-garden-of-eden-theorem` (ESTABLISHED; Ceccherini-Silberstein, Machì and Scarabotti,
  Ann. Inst. Fourier 49 (1999)). Over an amenable group, a cellular automaton is surjective iff it is pre-injective.

## Step 0. (2) ⇔ (3) over every group

(2) implies (3): equal supports give equal counts. For (3) implies (2), suppose `supp τ(x) ≠ supp x` for some `x`. Since
`supp τ(x) ⊇ supp x`, there is a `g` with `x(g) = 0` and `τ(x)(g) ≠ 0`. Let `x'` agree with `x` on `Mg` and be `0`
elsewhere. Then `x'` is finite and `τ(x')(g) = τ(x)(g) ≠ 0 = x'(g)`, so `supp τ(x') ⊋ supp x'`.

## Step 1. Amenable implies (2)

Let `G` be amenable and `τ` pre-injective and letter-dual on `A^G`. Let `λ` be the uniform Bernoulli measure.

1. By (G), `τ` is surjective, so it has no GOE. By (B3), `τ_* λ = λ`.
2. Let `C = {φ : φ(1) = 0}`. Letter-duality gives `τ^{-1}(C) ⊆ C`.
3. Both sets are clopen, and `λ(τ^{-1}C) = λ(C)` by step 1. So `C \ τ^{-1}(C)` is a clopen `λ`-null set.
4. `λ` gives every nonempty cylinder positive measure, so `C \ τ^{-1}(C)` is empty.
5. So `φ(1) = 0` iff `τ(φ)(1) = 0`, for every `φ`. Translating gives `supp τ(φ) = supp φ` for every `φ`.

## Step 2. Non-amenable implies not (3)

Let `G` be non-amenable, and take `K`, `Y`, `X_s`, `S`, `α_s` and `Θ` as in (B2). Fix `y0 ∈ Y \ ⋃_s X_s`, which exists
by (B2), and let `0` be the zero vector of `A = K^Y`. Define

    τ(φ)(g) = Θ(φ)(g) + [φ(g) ≠ 0] e_{y0},

with memory `S ∪ {1}`. `Θ` is linear with values in `K^{⋃ X_s}`, so the `y0`-coordinate of `Θ(φ)(g)` is `0`, and the
`y0`-coordinate of `τ(φ)(g)` is exactly `[φ(g) ≠ 0]`.

1. **Letter-dual.** `τ(0^G) = Θ(0^G) = 0^G`. If `φ(g) ≠ 0`, the `y0`-coordinate of `τ(φ)(g)` is `1`.
2. **Pre-injective.** Let `π` delete the `y0`-coordinate. Then `π τ = Θ`, on the values `K^{⋃X_s}`. Suppose
   `τ(φ) = τ(φ')` with `φ - φ'` finitely supported and nonzero. Then `Θ(φ - φ') = Θ(φ) - Θ(φ') = 0`, which contradicts
   (B2).
3. **Count-raising.** For `a ∈ A` and `h ∈ G`, `Θ(aδ_h)(g) = Σ_{s : sg = h} α_s(a)`, and exactly one `s` contributes. So
   `supp Θ(aδ_h) = {s^{-1}h : s ∈ S, α_s(a) ≠ 0}`. Suppose that for every `a ≠ 0` no `s ≠ 1` has `α_s(a) ≠ 0`.
   - By (B2), `Θ(aδ_h) ≠ 0`, so `1 ∈ S` and `α_1(a) ≠ 0` for every `a ≠ 0`.
   - Then `α_1 : K^Y → K^{X_1}` is injective. But `X_1 ⊆ ⋃ X_s ⫋ Y`, so this is impossible by dimension.
   - Hence some `a ≠ 0` and `s ≠ 1` have `α_s(a) ≠ 0`. Then `τ(aδ_h)` is nonzero at `h` and at `s^{-1}h ≠ h`, so the
     count rises from `1` to at least `2`.

So (3) fails at every non-amenable group. Together with Step 1 and Step 0, (1), (2) and (3) are equivalent. ∎

## Remarks

- **Injectivity.** `τ(φ) = τ(φ')` iff `Θ(φ) = Θ(φ')` and `supp φ = supp φ'`. So an injective `Θ` makes `τ` injective.
  Conversely, suppose `|K| >= 3` and `0 ≠ k ∈ ker Θ`. For `c ∉ {0, -1}`, `ck` and `(c+1)k` have the same support and the
  same image. So `τ` is injective iff `Θ` is. The flag never produces a dual counterexample at a group where Bartholdi's
  `Θ` is not already a Gottschalk counterexample.
- **`F_2` instance** (the artifact). `A = GF(2)^{u,v}`, `Θ(x)(h) = u(h) + u(ha^{-1}) + v(h) + v(hb^{-1})` in the
  `u`-coordinate, and the flag in the `v`-coordinate. The script checks, by GF(2) rank, that `Θ` is injective on
  configurations supported on balls of radius up to `6`. It is injective on all finite configurations because it is the
  mod-2 boundary of a finite edge set of the Cayley tree, and a nonempty finite forest has a leaf. It is not injective:
  `Θ((1,1)^G) = Θ((1,0)^G) = 0` and both flags are `1`.

## Consequences for the graph

- **Class kill for need `ebb50f1d`** (dual charge theorem). A dual failure at `G` forces `G` to be non-surjunctive,
  hence non-sofic, hence non-amenable. At every such `G`, including torsion groups without free subgroups (free
  Burnside groups of large odd exponent, Tarski monsters), Step 2 gives a pre-injective letter-dual automaton that
  raises counts.
  - Invariant: injectivity only on pairs that differ at finitely many sites.
  - The step where every member dies is the first appeal to injectivity. Any argument that goes through with
    pre-injectivity proves a false statement.
  - So a proof must use injectivity on pairs that differ at infinitely many sites.
- **Scope beyond `F_2`.** This extends the w23 free-subgroup calibration, whose example needs `F_2 ≤ G`, to every
  non-amenable group. It adds the converse: over amenable groups the pre-injective version is true.
- **Primal versus dual.** `finite-injective-charge-noncreation-forces-surjectivity` needs only finite injectivity over
  every group. The dual cannot have such a proof at any non-amenable group.
- **Hilbert hotels.** For `strict-automata-yield-odd-one-rest-hilbert-hotels`, count-raising pre-injective automata with
  one quiescent rest letter exist at every non-amenable group. So any obstruction there must use global injectivity.
