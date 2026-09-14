---
rg: 2
id: brin-thompson-2v-nonsurjunctive
kind: claim
title: The Brin–Thompson group 2V carries an injective non-surjective cellular automaton
distinct_from:
  thompson-v-nonsurjunctive: that names Thompson's V; this names the Brin–Thompson group 2V, which contains V, so that claim implies this one and not conversely.
  leavitt-unit-group-nonsurjunctive: that names the unit group of L_(F_2)(1,2); this names 2V, the product-cylinder permutation units of L_(F_2)(1,2) ⊗ L_(F_2)(1,2).
artifacts:
  - research/artifacts/brin-thompson-2v-gottschalk-host-2026-09-12.md
---

**OPEN.** Let `C = {0,1}^N` and let `2V` be the Brin–Thompson group: the homeomorphisms of `C × C` that cut
`C × C` into finitely many product cylinders `[α] × [γ]` and send each onto another product cylinder by prefix
replacement in both coordinates. Exhibit a finite alphabet `A` and a cellular automaton on `A^(2V)` that is
injective and not surjective.

**Consequences.** A proof refutes `gottschalk-surjunctivity-conjecture` and shows that `2V` is not sofic
(`sofic-groups-are-surjunctive`).

**Why this host.**
- `V <= 2V`, so `thompson-v-nonsurjunctive` implies this claim
  (`thompson-v-nonsurjunctivity-ascends-to-brin-thompson-2v`). The linear gate for `2V` is implied by the
  gate for `V` (artifact Corollary 2.2).
- The binary Theorem B (`binary-cyclic-corner-full-iff-complement-corner-has-no-state`) applies to `F_2[2V]`,
  because `2V` contains `g` and the nine-cylinder units and is stable under the halving `D` (artifact
  Proposition 2.1).
- `2V` contains the ternary baker unit `u = Σ_i s_i ⊗ t_i`, which conjugates `V ⊗ 1` onto `D(V) ⊗ 1`. So the
  halving endomorphism of Theorem B is inner in `2V`. No element of `V` conjugates `V` into `D(V)`
  (artifact Lemma 2.3).

## Attempts
* **Theorem B transfer (w6-free-neg-d, 2026-09-12; artifact Sections 1–2).** Worked in the unit model of `2V`
  inside `L_(F_2)(1,2) ⊗ L_(F_2)(1,2)`. Put `e = 1 + [g ⊗ 1] + [g² ⊗ 1]` and `T = (1 - e) F_2[2V] (1 - e)`. If
  `(K_0(T), [T])` has no state, then `e` is full (`brin-thompson-2v-order-three-averaging-idempotent-is-full`),
  `F_2[2V]` is not directly finite, and this claim holds. The corresponding condition for `V` implies it. Status:
  the reduction is on paper and awaits verification. The gate is open.
* **Baker unit and product tower (w6-free-neg-d, 2026-09-12; artifact Propositions 2.4–2.5).** Conjugation by
  `u` turns the halving homomorphism `ψ(x) = e D(x)` on `F_2[V ⊗ 1]` into multiplication by
  `1 + [1 ⊗ g] + [1 ⊗ g²]`, and the tower idempotents `E_k` into external products `E_(k-j) ⊗ E_j`. A state of
  `K_0(F_2[2V])` gives the four products of `e ⊗ 1`, `f ⊗ 1` with `1 ⊗ e`, `1 ⊗ f` the values `a, b, b, 2b`, with
  `a + 4b = 1`. Where it stopped: `b = 0` (augmentation) and `b = 2/9` (independent product of the regular
  values) satisfy every relation coming from finite subgroups and `u`. An obstruction must use elements of
  infinite order that mix the two coordinates.
