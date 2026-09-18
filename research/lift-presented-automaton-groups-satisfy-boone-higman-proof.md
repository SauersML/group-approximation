---
rg: 2
id: lift-presented-automaton-groups-satisfy-boone-higman-proof
kind: route
title: Regroup to make the abelianization finite without changing the lift-ideal condition, then embed G diagonally on e disjoint cones into the simple commutator subgroup
target: lift-presented-automaton-groups-satisfy-boone-higman
requires:
  - rover-nekrashevych-fp-iff-finite-lift-presentation
  - rover-nekrashevych-finite-presentation-criteria
---

Notation of the claim. Inputs: Theorem A of `rover-nekrashevych-fp-iff-finite-lift-presentation`, its
proof's §0 (cone copies `L_v` and the conjugation rule `h L_u(g) h^{-1} = L_v(g)` for `h in V_d` with
`h(uw) = vw`), and items (S), (FP3) and (R) of `rover-nekrashevych-finite-presentation-criteria`
(Scott, Nekrashevych, Zaremsky arXiv:2405.09722, by citation).

## 1. Regrouping preserves the hypothesis

Let `Y = X × {1,…,m}`. The regrouped action (item (R)) is the recursion `ψ_Y` on `F` with
`s(x,i) = (s(x), i)` and `s|_{(x,i)} = s|_x`; it is a faithful self-similar action of `G` on `Y^*` (R).
For a word `w in F`, its root permutation on `Y` is trivial iff its root permutation on `X` is, and its
`Y`-sections are exactly its `X`-sections, each repeated `m` times. Hence:
- the set of words reachable by taking sections is the same for `ψ` and `ψ_Y`;
- by consequence 4 of Theorem A (`w in N` iff every reachable word has trivial root permutation), the
  relator kernel of the `Y`-action is the same subgroup `N` of `F`;
- a normal subgroup `M` is lift-closed for `ψ_Y` iff it is lift-closed for `ψ`, since both conditions read
  "trivial root permutation and all sections in `M`" over the same sections.

So `N` is a finitely generated lift ideal for `ψ_Y` iff it is for `ψ`, and by Theorem A `V_{md}(G)` is
finitely presented whenever `V_d(G)` is, for every `m >= 1`.

## 2. Finite abelianization and the simple host

By (R), for even `m` with `1/m` not an eigenvalue of `A` (all but finitely many even `m`, since `A` has
finitely many eigenvalues), `V := V_{md}(G)` has finite abelianization. By (S), `C := [V,V]` is simple. It
has finite index in the finitely presented group `V` (§1), so it is finitely presented (FP3).

## 3. The cone-diagonal embedding into C

Let `e` be the exponent of `V^ab`, and choose `e` pairwise disjoint nonempty cones `v_1X'^ω, …, v_eX'^ω`
in `X'^ω`, `X' = Y` (possible since `md >= 2`).
- Each `g -> L_{v_i}(g)` is an injective homomorphism `G -> V` (the action is faithful), and copies on
  disjoint cones commute. So `δ_e(g) = L_{v_1}(g) ··· L_{v_e}(g)` is an injective homomorphism.
- Any two proper cones `vX'^ω`, `v'X'^ω` are exchanged by prefix replacement by some `h in V_{md}`: their
  complements are finite unions of cones whose counts are both `≡ 0 mod (md-1)`, so they can be matched
  by a prefix-replacement bijection. By the conjugation rule, `L_{v'}(g) = h L_v(g) h^{-1}`. So all
  `L_{v_i}(g)` have the same image `c(g)` in `V^ab`.
- The image of `δ_e(g)` in `V^ab` is `e·c(g) = 0`. So `δ_e(G) <= C`.

Therefore `G ≅ δ_e(G) <= C`, a finitely presented simple group. ∎

**Remark (replaces Zaremsky's wreath step).** §3 uses only that `V^ab` is finite, so it applies verbatim
to his setting as well; nothing here depends on `G` being finitely presented.
