---
rg: 2
id: braided-thompson-group-bv-is-perfect-proof
kind: route
title: bV is perfect because the coinvariants of H_1 of the pure braided kernel vanish
target: braided-thompson-group-bv-is-perfect
requires: []
---

**Setup.** Elements of `bV` are classes of triples `(T_-, β, T_+)`: binary trees
`T_±` with `n` leaves and a braid `β ∈ B_n`. Expanding a leaf of `T_+` by a
caret, the matching leaf of `T_-` by a caret, and replacing the corresponding
strand of `β` by two parallel strands (cabling) gives the same element.
Replacing `β` by its permutation gives the surjection `π: bV → V`. Let `K = ker π`.

**Step 1: the kernel.** Suppose `π(T_-, β, T_+) = 1`. Expansions of triples in
`bV` lie over expansions of tree pairs in `V`, and the trivial element of `V`
is represented by `(S, id, S)` for every tree `S`. So after expanding, the
element is `(T, β', T)` with `β'` a pure braid. Hence `K` is the filtered colimit,
over binary trees `T` ordered by expansion, of the pure braid groups
`P_{|T|}`, embedded as `(T, β, T)`. The transition maps are cabling maps, and
cabling maps are injective.

**Step 2: `H_1(K)`.** `H_1(P_n) = Z^{n(n-1)/2}` with basis `e_{ab}` (`a ≠ b`,
unordered), dual to the winding numbers `ω_{ab}: P_n → P_2 ≅ Z` obtained by
forgetting every strand except `a` and `b`. Cabling strand `i` into parallel
strands `i', i''`:

- `ω_{i'j} = ω_{i''j} = ω_{ij}`, since forgetting down to `{i', j}` or `{i'', j}`
  gives the same two-strand braid as forgetting down to `{i, j}`;
- `ω_{i'i''} = 0`, since two parallel copies of one strand do not wind around each other;
- all other winding numbers are unchanged.

So on `H_1` the cabling map sends `e_{ij} ↦ e_{i'j} + e_{i''j}` and fixes the
other `e_{ab}`. The leaves of a tree are disjoint dyadic cones of the Cantor
set `C`, and subdivision is additive, so
`H_1(K) ≅ C_c(Y, Z)`: compactly supported locally constant integer functions
on the space `Y` of unordered pairs of distinct points of `C`, with `e_{UW}`
corresponding to the indicator of the image of `U × W`.

**Step 3: the action.** `K` acts trivially on `H_1(K)`, so `bV` acts through
`π`. Expand `g = (T_-, γ, T_+)` and `k = (T_+, β, T_+)` over a common tree.
Then `g k g^{-1} = (T_-, γβγ^{-1}, T_-)` and
`ω_{σ(a)σ(b)}(γβγ^{-1}) = ω_{ab}(β)`, where `σ` is the permutation of `γ`.
So `g` sends `e_{UW}` to `e_{π(g)U, π(g)W}`: the geometric action of `V` on pairs of cones.

**Step 4: coinvariants vanish.** Any two disjoint cones are leaves of one tree,
so the classes `e_{UW}` generate `H_1(K)`.

- `V` acts transitively on unordered pairs `{U, W}` of disjoint cones with
  `U ∪ W ≠ C`. Map `U → U'` and `W → W'` by the canonical prefix
  replacements. The complements are nonempty clopen sets, each a union of the
  same number of cones after subdividing, so they can be matched cone by cone
  in the same way. The result is an element of `V`.
- So all these pairs have one class `f` in `H_1(K)_V`. For such a pair, split
  `U` into its two child cones `U_1, U_2`. By Step 2, `e_{UW} = e_{U_1 W} + e_{U_2 W}`,
  and both new pairs again have nonempty complement. So `f = 2f`, hence `f = 0`.
- The remaining pairs have `U ∪ W = C`, so `U`, `W` are the two children of the
  root, and `e_{UW} = e_{U_1 W} + e_{U_2 W} = 0`.

Hence `H_1(K)_V = 0`.

**Step 5: conclusion.** The Lyndon–Hochschild–Serre five-term exact sequence of
`1 → K → bV → V → 1` is
`H_2(bV) → H_2(V) → H_1(K)_V → H_1(bV) → H_1(V) → 0`.
`V` is simple and non-abelian (Thompson), so `H_1(V; Z) = 0`. Together with
`H_1(K)_V = 0` this gives `H_1(bV; Z) = 0`. ∎

**Second argument (corroboration, citation).** Zaremsky, "On normal subgroups
of the braided Thompson groups", arXiv:1403.8132 (Groups Geom. Dyn.), abstract:
"Every proper normal subgroup of Vbr lies in the kernel of the natural quotient
Vbr → V". If `[bV, bV]` were proper it would lie in `K`, and then `V = bV/K`
would be a quotient of the abelian group `bV/[bV, bV]`, which is impossible
because `V` is non-abelian. The theorem number was not checked against the
paper body; the self-contained argument above does not depend on it.
