---
rg: 2
id: commonly-fixed-letters-compress-to-faithful-actions
kind: claim
title: If every state of an automaton fixes a letter x, compressing runs of x gives a faithful finite-state action of the same group, by the same states, on a tree without that letter
distinct_from:
  loop-retraction-forces-fp-eventual-section-groups: that is the obstruction a commonly fixed letter creates for finite presentation of V_d(G); this is a construction that removes the letter while keeping the group and the state set, so the obstruction disappears.
  persistent-automata-rn-group-fp-iff-group-fp: that treats a persistent action as given; this shows a persistent letter can always be deleted (the p = 0, q = 1 case below), so persistence never decides anything about the group.
  lift-presented-automaton-groups-satisfy-boone-higman: that consumes one lift-presented action; this produces new finite-state actions to feed it.
---

**ESTABLISHED** by `commonly-fixed-letters-compress-to-faithful-actions-proof` (lane proof, elementary; no priority claimed). Referee a (proof gaps) PASS: `research/artifacts/gq-referee-a-commonly-fixed-letters-compress-and-spine-grigorchuk.md`.

## Setting

`G = ⟨S⟩ <= Aut(X^*)`, `S` finite and closed under sections and inverses. Suppose a letter `x` is fixed by every
state. Then `σ(g) = g|_x` is an endomorphism of `G` (all elements fix `x`). Choose `p >= 0` and `q >= 1` with `σ^p = σ^{p+q}` on
`S` (they exist because `S` is finite). For `b >= 0` let
`[b] = b` if `b < p + q`, and otherwise `[b]` is the unique `c in {p, …, p+q-1}` with `c ≡ b (mod q)`; then
`σ^b = σ^{[b]}` on `G`. Put `Y = X ∖ {x}` and `A = Y × {0, 1, …, p+q-1}`.

## Statement

**Theorem (run compression).** The rule
- root permutation of `s` on `A`: `(y, c) ↦ (σ^c(s)(y), c)`;
- section of `s` at `(y, c)`: `σ^c(s)|_y` (an element of `S`)

defines a faithful action of `G` on `A^*` by the finite automaton with state set `S`. It is the action obtained
by reading a point `x^{b_0} y_0 x^{b_1} y_1 …` of `X^ω` (with infinitely many letters from `Y`) as
`(y_0,[b_0]) (y_1,[b_1]) …`.

## Consequences

1. **Persistent letters can be deleted.** If `S` is persistent at `x` (`σ = id`), take `p = 0`, `q = 1`: then
   `A = Y × {0} ≅ Y` and the compressed action is the restriction of `G` to `Y^*`, which is therefore
   faithful. If `S` is twisted-persistent (`σ` a permutation of order `q`), take `p = 0`: `A = Y × Z/q`. So a
   (twisted-)persistent action never decides whether `G` has a lift-presented action; the persistent failures
   of `persistent-automata-rn-group-fp-iff-group-fp` (SWZ Ex. 7.2: Grigorchuk on `T_3` compresses to the
   standard `T_2` action) are failures of the action only.
2. **The spine obstruction is removed.** The letter `x`, and with it the eventual section group of
   `loop-retraction-forces-fp-eventual-section-groups`, disappears. New letters `(y,c)` fixed by all states can
   appear; they correspond to rays `(x^c y)^ω` of the old action, and compression can be repeated at them.
3. **Example.** `spine-grigorchuk-automaton-group-has-a-bounded-action`: the linear-activity automaton of
   `linear-activity-automata-can-have-non-fp-nekrashevych-groups`, whose `V_3` is not finitely presented,
   compresses to a bounded, contracting automaton on 4 letters, so its group has a finitely presented `V_4`
   (Nekrashevych FP2). Boone–Higman for it follows unconditionally from that contracting action or from
   `G <= (Γ ≀ C_2) × Γ` (see that node).
4. If `|A| = 1` (so `d = 2` and `p + q = 1`), faithfulness forces `G = 1`.
