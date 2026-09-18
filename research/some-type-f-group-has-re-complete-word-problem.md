---
rg: 2
id: some-type-f-group-has-re-complete-word-problem
kind: claim
title: Some group of type F has a word problem that is r.e.-complete under many-one reductions
distinct_from:
  some-type-f-group-has-unsolvable-word-problem: That gives a type F group whose word problem is not decidable; this pins its degree at the top r.e. many-one degree, which is what word-problem-degree obstructions to embeddings (Zaremsky 1.1) consume, and which unsolvability alone does not rule out.
  every-turing-degree-is-a-simple-kazhdan-lef-word-problem: That realizes every Turing degree by finitely generated (not finitely presented, not type F) simple Kazhdan LEF groups; this is one degree realized by a group of type F.
---

There is a finitely presented group `G` of type `F` (a finite `K(G,1)`) whose
word problem, the set of words over its finite generating set that represent
`1`, is complete among recursively enumerable sets under many-one reductions.

The group is the Aanderaa--Cohen--Boone group `G_M` of the machine-checked
Novikov--Boone chain, for the modular machine `M` produced there from Mathlib's
universal partial recursive function.

**Consequence.** For every finite `m`, some group of type `F_m` has an
r.e.-complete word problem. This refutes
`some-type-fm-level-has-no-complete-word-problem` at every level, so the route
`no-type-fn-plus-1-host-via-word-problem-degree` towards Zaremsky Problem 1.1
dies at its premise: many-one word-problem degree cannot separate type `F_n`
from type `F_{n+1}` hosts at any level. Every degree-based obstruction has to use
an invariant finer than the many-one degree of the word problem (for instance,
the time complexity or Dehn function, or the degree of other decision problems).

Proof: route `some-type-f-group-has-re-complete-word-problem-proof`.

## Attempts

- **The computability of the index map was already machine-checked; the proof
  called it "by inspection".** (w3-117, 2026-09-17.) The map `m -> f(m)` is
  `Computable` by `computable_index_map D M₁`. That is the conjunct `Computable f` of
  `exists_modularMachine_universal_control` (`ModularMachineConfigHalting.lean`).
  The words are computable by `exists_boone_words`. The only step not in Lean
  is the r.e.-to-code composition:
  - choose `c_L` with `(eval c_L x).Dom <-> (unpair x).1 ∈ L` (`Code.exists_code`);
  - put `g(p) = encode (Code.curry c_L p)` (`Code.primrec₂_curry`, `Code.eval_curry`);
  - reduce by `w ∘ f ∘ g`, with `mm, f` from `exists_modularMachine_universal_control 0`.

  Step 0 of `type-f-group-receives-re-languages-by-pattern-reductions-proof`
  gives the details. It also records the explicit form
  `f(n) = (a_0, encList m (c_cons :: (trNat n).reverse.map code))`, read off
  `encCfg_initQCfg`, `map_enc_trInit` and `trNat_eq_cons`.

- **The finer invariant suggested above (time complexity of the reduction) is
  dead too** (proposed-established, w3-117). The reduction `w ∘ f ∘ g` above has
  exponential size. The fix is the type F group
  `H_M = <G_M, s | [s,t] = [s,x] = 1, s^-1 y s = y^m>`. Its most-significant-first
  Horner words compress `y^b` with a stable letter that commutes with `t` and `x`.
  - `H_M` receives every r.e. language by patterns `v -> omega_L(phi(v))`, with ONE
    free-monoid homomorphism `phi` and four occurrences of `phi(v)`.
  - So every reducibility containing these patterns (linear-time, polynomial-time,
    log-space) fails to separate type `F_n` from type `F_{n+1}` hosts at every `n`.
  - At one occurrence the relation is exactly embedding (Lemma E), so it is
    Problem 1.1 itself.
  - A word-problem-reduction obstruction must use 2- or 3-occurrence patterns, or
    a host invariant.
  exponential size.
  - The fix is the type F group `H_M = <G_M, s | s^-1 y s = y^m>`. Its Horner
    words compress `y^b`, and it receives every r.e. language by linear-size
    patterns `v -> omega_L(phi(v), psi(v))`, with `phi` and `psi` free-monoid
    homomorphisms.
  - So every reducibility containing these patterns (linear-time, polynomial-time,
    log-space) fails to separate type `F_n` from type `F_{n+1}` hosts at every `n`.
  - Inverse-respecting substitution is exactly embedding (Lemma E), so there it is
    Problem 1.1 itself.
  - A word-problem-reduction obstruction must live strictly between the two, or
    use a host invariant.

  See `type-f-group-receives-re-languages-by-pattern-reductions`.
