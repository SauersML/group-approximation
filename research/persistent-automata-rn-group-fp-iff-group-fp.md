---
rg: 2
id: persistent-automata-rn-group-fp-iff-group-fp
kind: claim
title: For a persistent finite-state self-similar group G, lift ideals are just normal subgroups, so V_d(G) is finitely presented if and only if G is
distinct_from:
  rover-nekrashevych-fp-iff-finite-lift-presentation: that is the general criterion (N a finitely generated lift ideal); this identifies the class where lift-closure is vacuous and the criterion collapses to finite presentability of G.
  rover-nekrashevych-group-of-lamplighter-automaton-is-fp: that is an action of Z/2 wr Z with N = K_infty and V f.p.; here the persistent action of the same group has K_infty = 1 and V not f.p.
  rover-nekrashevych-finite-presentation-criteria: that records sufficient conditions and asks for a characterization; this answers its "is some finite-state V_d(G) not finitely presented" sub-question, which Skipper-Witzel-Zaremsky had already answered.
---

**ESTABLISHED (proof in `persistent-automata-rn-group-fp-iff-group-fp-proof`; unreviewed). The `F_2` case of the
equivalence is a new proof of a known theorem: Skipper–Witzel–Zaremsky, *Simple groups separated by finiteness
properties*, Invent. Math. 215 (2019), arXiv:1712.05361, Theorem 5.8. The twisted version (2) and the same-group
contrast (4) are not in that paper.**

## Setting

Notation is that of `rover-nekrashevych-fp-iff-finite-lift-presentation`: `X = {0, ..., d-1}`, `G = ⟨S⟩ ≤ Aut(X^*)`
with `S` finite and closed under sections and inverses, `F = F(S)`, `N = ker(F -> G)`, and `K_∞ = ⟨⟨∅⟩⟩_lift`.

- `S` is **persistent at `i in X`** (SWZ Definition 5.1) if `s(i) = i` and `s|_i = s` for every `s in S`.
- `S` is **twisted-persistent at `i`** if `s(i) = i` for every `s in S` and `θ(s) := s|_i` is a permutation of `S`.

## Statement

1. **Lift-closure is vacuous.** If `S` is persistent at `i`, then every normal subgroup of `F` is a lift ideal. So
   `⟨⟨R⟩⟩_lift = ⟨⟨R⟩⟩` for every `R`, and `K_∞ = 1`.
2. **Twisted version.** If `S` is twisted-persistent at `i`, then every `θ`-invariant normal subgroup of `F` is a
   lift ideal (here `θ` also denotes the automorphism of `F` extending `s ↦ s|_i`), and `⟨⟨R⟩⟩ ⊆ ⟨⟨R⟩⟩_lift ⊆ ⟨⟨∪_{j ≥ 0} θ^j(R)⟩⟩` (a finite union, since
   `θ` has finite order). Again `K_∞ = 1`.
3. **Theorem.** In either case, `V_d(G)` is finitely presented if and only if `G` is finitely presented.
4. **Finite presentability of `V_d(G)` depends on the action, not only on the group.** `Z/2 ≀ Z` has two faithful
   finite-state self-similar actions on the 4-regular tree, one with `V_4` finitely presented and one without:
   - The lamplighter automaton of `rover-nekrashevych-group-of-lamplighter-automaton-is-fp`, read two letters at a
     time (alphabet `{0,1}^2`), still has `N = K_∞`. So its `V_4` is finitely presented.
   - The persistent extension `a = σ(a, b, a, a)`, `b = (a, b, b, b)` (`σ = (0 1)`, letters 2 and 3 fixed with
     self-sections) generates the same group with the same relator kernel. Its `K_∞` is `1`, so by (3) its `V_4` is
     not finitely presented.
   - Over three letters, the persistent extension `a = σ(a, b, a)`, `b = (a, b, b)` likewise has `V_3` not finitely
     presented, while `V_2` of the original lamplighter is finitely presented.

## Scope

- (3) recovers the non-finitely-presented examples of SWZ Example 7.2 (`V_3` of the persistent Grigorchuk action)
  and SWZ Theorem 7.1 for `n = 2`, with a three-line proof from Theorem A instead of SWZ's §5 retraction argument.
  SWZ's Theorem 5.8 is stronger in the other direction: it transfers `F_n` for all `n`.
- The `rover-nekrashevych-fp-iff-finite-lift-presentation` Attempts list the existence of a finite-state `G` with
  `V_d(G)` not finitely presented as "not settled in the sources read". It was settled in 2019 by SWZ, and (3) gives
  the shortest route to it inside this graph.
- (4) shows that persistence cannot be dropped from SWZ Theorem 5.8. A stronger instance, in SWZ's own affine family,
  is in `rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp`.

## Attempts

- 2026-09-18 (w8-101): proved via Theorem A. If `s|_i = s` for all `s in S`, then `w|_i = w` for every word `w`, so a
  word whose sections all lie in a normal subgroup `M` already lies in `M`.
  - Machine check: `experiments/affine-lamplighter-rn-2026-09-17/afflamp.py --persist` confirms that under persistent
    extension every lamplighter relator tested lies in `N` and none lies in `K_∞`. See `results.txt` there.
  - The brief's main step ("the first `V_d(G)` not finitely presented") was already known; see Scope.
