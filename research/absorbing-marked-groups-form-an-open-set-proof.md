---
rg: 2
id: absorbing-marked-groups-form-an-open-set-proof
kind: route
title: Write an absorption as a translation lift and check every identity on a finite ball
target: absorbing-marked-groups-form-an-open-set
requires:
  - monomial-quantum-automata-are-topological-bernoulli-absorptions
  - absorptions-give-post-surjective-strict-pairs
---

**Step 1: finite data.** Let `(G, s)` absorb at size `d`, and let `A = Z/d`. By (2) implies (3) of
`monomial-quantum-automata-are-topological-bernoulli-absorptions`, there is a cellular automaton `sigma` with local
rule on a finite memory `W`, and a lift `T_e`.
- `T_e(u) = Psi^-1(Psi(u) + (delta_e, 0))`. It writes only on a finite `S` and reads only on a finite `P ⊇ S`.
- The lift satisfies `T_e^d = id`, `sigma o T_e = sigma + delta_e`, and `T_e T_g = T_g T_e` for all `g`, where
  `T_g = lambda_g T_e lambda_g^-1`.
- By (i) of `absorptions-give-post-surjective-strict-pairs`, `sigma` is not pre-injective. So there are a finite
  `E`, two different patterns on `E`, and a common filling of `EW^-1W \ E`, such that `sigma` gives the same output
  on `EW^-1`.

**Step 2: every identity is local.** Let `K = P S^-1 ∪ S P^-1`, a finite set.
- For `g ∉ K`, `T_g` writes outside what `T_e` reads, and the reverse also holds, so the two commute automatically.
- The identities `T_e^d = id` and `sigma o T_e = sigma + delta_e`, the commutations for `g ∈ K`, and the
  non-pre-injectivity witness are all statements about patterns on one finite set `Q`. That set is a union of
  products of `W`, `W^-1`, `P`, `S`, `S^-1`, `K` and `E`.
- Choose `r` so large that `Q` and every product used above lie in the `r`-ball. Represent each element as a word
  in `s`.

**Step 3: transport.** Let `(G', s')` be a marked group whose `2r`-ball has the same labelled Cayley graph.
- Define `sigma'` and `T'_e` on `(Z/d)^(G')` by the same local rules, reading the same words.
- All the identities of Step 2 hold in `G'`, because they are checked on the same labelled ball. The sets `K`
  correspond as well, so commutation for `g ∉ K'` is again automatic.
- `T'_e` is a bijection, since `T'_e^d = id`.
- `sigma'` is not pre-injective, hence not injective.
- So `(sigma', T'_e)` satisfies (3) of the monomial theorem, and `G'` absorbs at size `d`. These `(G', s')` form an
  open neighbourhood of `(G, s)`.

**Step 4: finitely presented groups.**
- If a group absorbs, then by (iv) of `absorptions-give-post-surjective-strict-pairs` so does a finitely generated
  subgroup `H = F_n / N`.
- Enumerate `N = {w_1, w_2, ...}` and put `G_m = F_n / <<w_1, ..., w_m>>`. These groups are finitely presented and
  converge to `H` in the space of marked groups.
- By Step 3, `G_m` absorbs for all large `m`.

**Step 5: limits of sofic groups.** A limit of sofic marked groups is sofic. Sofic groups do not absorb, by the
consequences of `absorptions-give-post-surjective-strict-pairs`. So by openness an absorbing group is not such a
limit.
