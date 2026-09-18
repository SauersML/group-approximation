---
rg: 2
id: infinite-order-inputs-admit-mixed-near-relations
kind: claim
title: Every countable input with an element of infinite order and infinite index admits an enumeration whose near shift group satisfies a mixed relation
distinct_from:
  route-form-shell-inputs-have-computable-mixed-near-relations: that constructs the mixed relation for inputs P_0 x <t> with an infinite cyclic direct factor; this needs only one element of infinite order and infinite index, with no product structure, so it covers inputs such as St_4(R_L).
  free-shift-shell-envelopes-are-not-finitely-presented: that shows a free near shift group P*<s> forces a non-finitely-presented envelope; this shows that the hypothesis of that obstruction can always be avoided for such inputs.
  decidable-inputs-have-fp-shell-envelopes: that asks for a finitely presented envelope; this removes one necessary obstruction and asserts no finite presentation.
---

**ESTABLISHED** by `infinite-order-inputs-admit-mixed-near-relations-proof` (lane
proof, elementary, not independently reviewed; no novelty claimed).

## Statement

Let `P` be a countable group and `t ∈ P` an element of infinite order with
`[P : <t>] = ∞`. Let `λ'` be the permutation of `N` in
`route-form-shell-inputs-have-computable-mixed-near-relations`, and `s : n ↦ n+1`.

1. There is a bijection `nu : P -> N` whose regular permutation of `t`,
   `λ_t(nu(h)) = nu(th)`, equals `λ'`.
2. For such `nu`, `[λ_t s^4 λ_t^-1, s^8] = 1` in `NearSym(N)`. The word
   `t s^4 t^-1 s^8 t s^-4 t^-1 s^-8` is a nonidentity reduced word of `P * <s>`, so
   the canonical map `P * <s> -> R_nu` is not injective. Hence the hypothesis of
   `free-shift-shell-envelopes-are-not-finitely-presented` fails for `nu`.
3. **Computability.** Suppose `P` has decidable word problem and a decidable power
   problem for `t`: given `g`, decide whether `g ∈ <t>`, and if so find `k` with
   `g = t^k`. Then `nu` can be chosen computable, with computable inverse.

## Instance

`P = St_4(R_L)` and `t = x_12(1)`.
- `t` has infinite order: its image `e_12(1)` in `E_4(R_L)` has `k`-th power
  `e_12(k) ≠ I` for `k ≠ 0`, because `Q ⊆ R_L` unitally.
- `[P : <t>] = ∞`: `P` is infinite (it contains every `GL_n(Q)`) and has property
  (T), so it is not virtually cyclic.
- So item 1 and item 2 apply, and the free-shift obstruction does not bind
  `steinberg-resolvent-shell-envelope-is-finitely-presented`.
- Item 3 needs the word problem of `St_4(R_L)`, which is gate 1 of that node, and the
  power problem for `x_12(1)`. Neither is known.

## Scope

The relation involves only `t`. `λ(P)` is otherwise unconstrained, exactly as in the
route-form construction. Nothing is asserted about finite presentation of `R_nu`, the
finite-window gate of `shell-ascending-gate-is-a-finite-window-inclusion`, the germ
group or the envelope.
