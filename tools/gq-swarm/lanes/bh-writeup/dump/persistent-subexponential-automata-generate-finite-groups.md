---
rg: 2
id: persistent-subexponential-automata-generate-finite-groups
kind: claim
title: A twisted-persistent automaton of subexponential activity generates a finite group
distinct_from:
  persistent-automata-rn-group-fp-iff-group-fp: that shows persistent actions have V_d(G) finitely presented iff G is; this shows that for subexponential activity G is then finite, so every non-finitely presented V_d(G) from persistence has exponential activity.
  linear-activity-automata-can-have-non-fp-nekrashevych-groups: that is a linear-activity failure of finite presentation using only a commonly fixed letter, not full persistence.
---

**ESTABLISHED** (lane proof below, elementary; no priority claimed). Referee a (proof gaps) PASS: `research/artifacts/gq-referee-a-loop-retraction-linear-activity-persistent-automata.md`.

## Statement

Let `S <= Aut(X^*)` be finite, closed under sections and inverses, and **twisted-persistent** at a letter `i`:
every `s in S` fixes `i`, and `θ(s) = s|_i` is a permutation of `S`. Suppose every state has subexponential
activity (`#{v in X^n : s|_v ≠ 1}` grows subexponentially), e.g. polynomial activity in Sidki's sense. Then
`G = ⟨S⟩` is finite.

**Consequence.** With `persistent-automata-rn-group-fp-iff-group-fp`, every persistent (or twisted-persistent)
finite-state action with `V_d(G)` not finitely presented has exponential activity; in particular SWZ's
Example 7.2 (the persistent Grigorchuk action on `T_3`) must, and does.

## Proof

1. **Two cycles force exponential activity.** If a nontrivial state `u` has two distinct first-return closed
   walks `W, P` in the section graph (edges `s --y--> s|_y`), then the `2^n` concatenations of the blocks
   `W^{|P|}` and `P^{|W|}` are distinct words `v` of length `n|W||P|` (decode by cutting at returns to `u`)
   with `u|_v = u ≠ 1`. So `u` has exponential activity. Hence under the hypothesis no nontrivial state has
   two distinct first-return walks.
2. **The spine and the order.** For nontrivial `s`, `θ(s) = s|_i ≠ 1` (`θ` is a permutation fixing `1`), so
   `s` returns to itself along `i^m`, `m` its `θ`-period: its spine walk, beginning with the letter `i`. Order
   the `θ`-orbits of nontrivial states by `O ≻ O'` if some state of `O` has a nontrivial section in `O'` at a
   letter `y ≠ i`. A chain `O_0 ≻ O_1 ≻ … ≻ O_k = O_0` (`k >= 1`) gives, at the state `u_0 in O_0` that owns the non-`i`
   edge into `O_1`, a closed walk beginning with that letter `y ≠ i` (non-`i` edges between orbits, spine edges inside them), hence a
   first-return walk different from the spine walk, contradicting (1). So `≻` is acyclic; let `h(O)` be the
   length of the longest descending chain from `O`, and `G_h = ⟨states in orbits of height <= h⟩`.
3. **Section endomorphism.** All states fix `i`, so `g|_i` is a homomorphism `θ̂: G -> G` extending `θ`; it
   has finite order `M` (it permutes generators). Also `ρ(g) = (g|_{X∖i}; (g|_y)_{y ≠ i})` is a homomorphism
   `G -> G ≀ Sym(X∖{i})`, since elements fixing `i` permute `X∖{i}`. For `g in G_h`, the non-`i` sections
   of its letters lie in lower orbits, so `ρ(G_h) <= G_{h-1} ≀ Sym(X∖{i})` (with `G_{-1} = 1`), and
   `θ̂(G_h) = G_h`.
4. **Injectivity.** If `ρ(θ̂^j g) = 1` for `0 <= j < M`, then for `y ≠ i`,
   `g(i^k y w) = i^k θ̂^k(g)(y w) = i^k y (θ̂^k g)|_y(w) = i^k y w`, and `g(i^ω) = i^ω`; so `g = 1`. Hence
   `g ↦ (ρ(θ̂^j g))_{j<M}` embeds `G_h` in `(G_{h-1} ≀ Sym(X∖{i}))^M`. By induction on `h` every `G_h` is
   finite, and `G = G_H` for the maximal height `H`. ∎
