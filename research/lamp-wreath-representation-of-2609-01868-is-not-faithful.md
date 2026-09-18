---
rg: 2
id: lamp-wreath-representation-of-2609-01868-is-not-faithful
kind: claim
title: In the self-similar representation that arXiv:2609.01868 builds for Z wr_X PSL_2(Z[1/2]), every lamp acts as the same tree automorphism, so the representation is not faithful; the error is in the faithfulness step of their Theorem A, not in condition (Ω)
distinct_from:
  z-wr-psl2-z-half-is-not-residually-finite: that proves no faithful self-similar representation of the group exists (it is not residually finite) and guesses that the source's error lies in condition (Ω) or in faithfulness; this reads the source's proofs, shows their verification of (Ω) for PSL_2(Z) is correct, and exhibits the kernel of their representation explicitly.
  z-wr-psl2-z-half-embeds-in-fp-self-similar-group: that is the printed question, refuted; this corrects the positive theorem printed alongside it.
---

**ESTABLISHED** (lane proof below, elementary; source read at arXiv:2609.01868v1 main.tex; no priority
claimed).

## The source's construction

`G = PSL_2(Z[1/2])`, `K = PSL_2(Z)`, `X = K\G`. Theorem B(2) (l.670–689): `G` is self-similar via
`f(h) = P^{-1}hP` on `H = {(a, 3b; c, d)}`, of index 4, `P = [[0,3],[-1,1]]`. Theorem A (l.400–419) then
represents `W = Z ≀_X G` through the virtual endomorphisms
- `ρ_1` on `lamps ⋊ H`: `a^{Kg} ↦ a^{K f(h)}` if `Kg = Kh` with `h in H`, and `↦ 1` otherwise; `h ↦ f(h)`;
- `ρ` on all of `W` (index 1): `a^{Kg} ↦ x` (a fixed infinite-order `x in G`), `G ↦ 1`,

on the 5-ary tree, and Theorem B(3) (l.841–895) checks condition (Ω) for `K` to conclude that `W` is
self-similar.

## Statement

1. **(Ω) holds.** The source's verification of (i)–(iii) for `K = PSL_2(Z)` (l.847–894) is correct.
2. **All lamps act alike.** `K` acts transitively on `G/H`, since `K -> PSL_2(F_3)` is onto and `H` is a
   point stabilizer of `P^1(F_3)`. So `KH = G`: every coset `Kg` meets `H`, and no lamp is sent to `1` by `ρ_1`.
   Hence every lamp `a^y` has trivial root permutation, lamp sections at the four `ρ_1`-letters and the section
   `x` at the `ρ`-letter `5`. By induction on length, every lamp acts on `{1,…,5}^*` as the same automorphism
   `τ`: `v 5 u ↦ v 5 x(u)` for `v in {1,…,4}^*`, and the identity on words with no `5`.
3. **Not faithful.** So `a^y (a^z)^{-1}` acts trivially for all `y, z in X`. The zero-sum lamp subgroup is a
   nontrivial normal subgroup inside the kernel. Equivalently, it is invariant under `ρ_1` (lamps are
   transported bijectively, `ρ_1` never kills one) and under `ρ` (a zero-sum element goes to `x^0 = 1`), so the
   `f`-core is nontrivial.
4. **Where the source's proof breaks.** In the faithfulness step (l.511–532), a minimal-support element
   `y = a^{n_1 K + n_2 K h_2 + ⋯}` of an invariant `N` is shown to keep its support under every
   `ρ_{i_1}⋯ρ_{i_k}`, and the proof concludes `h_2, …, h_r in K H_ω`. That conclusion does not follow: here
   every product of `ρ_1`'s keeps every support, since `KH = G`, while `h_i ∉ K`. The general mechanism: if
   `KH_i = G` for every `i`, the `ρ_i` never kill a lamp, and all lamps act as the same automorphism.

## Consequences

- Theorem B(3) of the source is false for `A = Z`, and indeed for every nontrivial `A`, by
  `z-wr-psl2-z-half-is-not-residually-finite`. This node locates the error for the `Z`-lamp construction.
  The finite-lamp construction (Theorem A(1), l.540–571) uses different formulas; its error here is not
  located, but its conclusion fails for the same group by the same residual-finiteness argument.
- Any use of Theorem A needs `K` to act non-transitively on some `G/H_i`, or some other way for different
  lamps to be separated by their survival along the tree.
