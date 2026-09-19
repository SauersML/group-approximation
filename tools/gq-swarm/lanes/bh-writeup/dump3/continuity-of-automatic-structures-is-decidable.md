---
rg: 2
id: continuity-of-automatic-structures-is-decidable
kind: claim
title: An automatic structure with uniqueness is a continuous normal form exactly when left multiplication by each generator has bounded lookahead, and this is decidable from the multiplier automata
distinct_from:
  mapping-class-groups-are-continuous-automatic: that asks whether mapping class groups have some continuous automatic structure; this decides, for one given automatic structure such as Mosher's, whether it is continuous.
  rational-germ-singular-sets-are-finite-graph-path-spaces: that decides the singular set of a rational boundary action, which presupposes a continuous structure; this decides continuity itself, the step before.
  thin-rational-actions-give-finite-germ-extensions: that uses thin generators on the boundary; this is the prior condition that the boundary action exists.
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed). Proof:
`continuity-of-automatic-structures-decidable-proof`.

## Setting

- **Automatic structure.** `(X, L)` is an automatic structure with uniqueness on a group
  `G`, in the convention of Belk--Bleak--Chatterji--Matucci--Perego (BBCMP, preliminary,
  §1.1). So `L ⊆ X^*` is regular and maps bijectively to `G`.
- **Multiplier maps.** For `s ∈ X` let `f_s : L → L` send `β` to the word of `s·π(β)`.
  Its graph `R_s = {(f_s(β), β)}` is accepted by a deterministic synchronous automaton
  `𝒜_s` over `(X ∪ {$})^2`, reading padded pairs, with state set `Q_s`.
- **Notation.** `|β ∧ β'|` is the length of the longest common prefix.

## Statement

For each `s ∈ X` the following are equivalent:
1. **(continuity at s)** For every `N` there is `M` such that `|β ∧ β'| ≥ M` implies
   `|f_s(β) ∧ f_s(β')| ≥ N`.
2. **(bounded lookahead)** There is `K` such that `|β ∧ β'| ≥ i + K` implies
   `|f_s(β) ∧ f_s(β')| ≥ i` for all `i`. One may take `K = |Q_s|^2`.
3. **(no split cycle)** In the twin graph of `𝒜_s`, no path from `(q_0, q_0)` does all of
   the following: it first splits, then runs through a cycle, then ends at a pair of
   co-accessible states.
   - The twin graph has vertices `Q_s × Q_s`. It has an edge
     `(q,q') → (δ(q,(a,b)), δ(q',(a',b)))` for letters `a, a' ∈ X ∪ {$}` and a common
     `b ∈ X`.
   - A path *splits* when some edge on it has `a ≠ a'`.

By BBCMP Proposition 2.1 with the monoid generating set `X`, `L` is a continuous normal
form iff condition 1 holds for every `s ∈ X`. Condition 3 is a finite graph search, so
continuity of a given automatic structure is decidable.

## Why it is useful

- **What continuity really says.** Continuity is bounded lookahead. Up to a delay, left
  multiplication by a generator is computed by a left-to-right transducer. This is the
  mechanism of the BBCMP examples: Garside carries and normal cube paths.
- **A first, decidable test for candidate structures.** For example, Mosher's automatic
  structure on mapping class groups. The thinness and germ-rate tests of lane
  bh-free-51 (`rational-germ-singular-sets-are-finite-graph-path-spaces`,
  `germ-rate-homomorphism-tests-germ-extension-finiteness`) apply only after this test is
  passed, because they need the boundary action to exist.
- **Scope.** This decides continuity of one given structure. BBCMP Question 1.16 asks
  whether some automatic structure is continuous, which this does not decide. The
  asynchronous case is not treated.
