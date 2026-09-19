---
rg: 2
id: m11-loop-star-survivors-are-not-finitely-presented-proof
kind: route
title: Proof that exponent-sum functionals certified by the linear descent test survive every relation of a unit-weight polynomial recursion, that the loops of the chain (a,a,e) survivor generate G, and that every loop-star survivor has b_1 >= 1 and is not finitely presented
target: m11-loop-star-survivors-are-not-finitely-presented
requires:
  - unit-weight-polynomial-recursions-split-over-loop-edges
  - fully-self-replicating-fp2-groups-have-odd-cyclic-h1
  - fully-self-replicating-fp-infinity-groups-are-acyclic
artifacts:
  - experiments/loop-subgroup-membership-2026-09-19/descent.py
  - experiments/loop-subgroup-membership-2026-09-19/classify.py
  - experiments/loop-subgroup-membership-2026-09-19/classify.out
  - experiments/loop-subgroup-membership-2026-09-19/sanity.py
  - experiments/loop-subgroup-membership-2026-09-19/sanity.out
  - experiments/loop-subgroup-membership-2026-09-19/stab.py
  - experiments/loop-subgroup-membership-2026-09-19/loops_generate.py
  - experiments/loop-subgroup-membership-2026-09-19/loops_generate.out
  - experiments/loop-subgroup-membership-2026-09-19/lat1.py
  - experiments/loop-subgroup-membership-2026-09-19/lat1.out
---

**Status: ESTABLISHED (unreviewed).** §1 and §3 are proofs by hand. §2 and §4 apply §1 by
exact rational linear algebra (`descent.py`). §3 uses two exact finite computations
(`loops_generate.py`, `lat1.py`). Notation is that of the claim and of
`unit-weight-polynomial-recursions-split-over-loop-edges`.

## 0. Conventions

- `F = F(S) ∗ P`, where `S` is the set of state letters and `P = M_11` acts by rooted
  permutations (trivial sections, acting on the first letter of a vertex only).
  `ρ : F ↠ G`. A *word* is a normal form of `F`: `π_0 s_1^{ε_1} π_1 ⋯ s_k^{ε_k} π_k` with
  `π_i ∈ P`, `s_i ∈ S`, and no `s s^{-1}` with `π = 1` between them. Its *count* is `k`.
- Sections: `(uv)|_y = u|_y v|_{y^u}`, `π|_y = 1`, iterated along vertices, then reduced
  to normal form. Reduction never raises the count. If `w ∈ ker ρ`, every `w|_v` lies in
  `ker ρ`.
- `E : F → Z^S` is the signed exponent sum of the state letters, with `E(P) = 0`.
  Then `Σ_{x ∈ X} E(w|_x) = M E(w)`, where `M[l, s]` is the signed number of occurrences
  of `l` in the sections of `s`. The sum is additive, and `s^{-1}|_x = (s|_{x^{s^{-1}}})^{-1}`.
  Iterating gives `Σ_{v ∈ X^n} E(w|_v) = M^n E(w)`.
- Functionals are row vectors, and `λ` is *valid on* `F_D = F(D) ∗ P` if `λE(w) = 0` for
  every `w ∈ ker ρ ∩ F_D`.

## 1. The linear descent theorem (item 3)

**Hypotheses, checked by `descent.py` for each recursion.**
- (U): every level-1 section has count `≤ 1`. By induction, so does every level-`n`
  section of a letter. Such a section is `c l^{δ} d` with `c, d ∈ P`, or lies in `P`.
- `p` is a multiple of every cycle length of the signed section digraph, and
  `N = M^p − I` is nilpotent.
- (T_p): for every `s ∈ S`, at most one `y ∈ X^p` has `s|_y` containing a letter of the
  signed strongly connected component of `(s, +1)`. For that `y`, the letter is `s^{+1}`.
  The script asserts this by enumerating `X^p`.

Fix a section-closed `D`. Let `D_low` be its lower part and `T = D ∖ D_low` its top letters.
- **(a) Letters of `D_low` have sections in `F_{D_low}`.** This is closure.
- **(b) The only top letter in a level-`p` section of a top letter `s` is `s` itself.**
  Suppose `s|_y` (`|y| = p`) contains `l ∉ D_low`. The section path from `(s,1)` cannot
  leave the SCC of `(s, 1)`. The first letter after an exit is an exit letter of a letter
  of `D`, so it lies in `D_low`, and so does everything after it by (a). So `l` is in the
  SCC, and (T_p) says `l = s^{+1}`. A letter of the SCC is never in `D_low`: otherwise
  `s` would be reachable from `D_low` and would lie in `D_low`.
- **(c) Consequence.** Each top letter occurrence at a vertex has its top letter in at most
  one child of `X^p`, and in exactly one when it is a cycle letter.

**Lemma A (closed walks).** Let `z ∈ F_D` be a word with `z ∈ ker ρ`, and let `u ∈ X^m`
with `m` a multiple of `p`. Suppose `z|_u = z` as words, and that every letter of `z` has a
state letter in its section at the point where it acts on `u`. Then:
1. `E(z)` lies in the label image `C_D` of the cycle space of the level-`p` loop graph on
   its `D`-edges;
2. `N E(z) = 0`.

*Proof.* Write `z = π_0 s_1^{ε_1} π_1 ⋯ s_k^{ε_k} π_k`, and let letter `i` act at
`y_i = u^{π_0 s_1^{ε_1} ⋯ π_{i−1}}`. By (U) its section is `c_i t_i^{δ_i} d_i` with
`c_i, d_i ∈ P`. The section `z|_u` is the product of these sections, since the `π`'s have
trivial sections. So
`z|_u = c_1 t_1^{δ_1} (d_1 c_2) t_2^{δ_2} ⋯ (d_{k−1} c_k) t_k^{δ_k} d_k`.
This is already a normal form. It equals `z`, so `t_i^{δ_i} = s_i^{ε_i}`, `π_0 = c_1`,
`π_i = d_i c_{i+1}` and `π_k = d_k`.

So each `(s_i, ε_i, y_i, c_i, d_i)` is a level-`m` loop state. Its loop-graph edge runs
from `y_i^{c_i^{-1}}` to `y_i^{s_i^{ε_i} d_i}`. For `ε = −1` this is the reverse of the
positive edge of the loop state `(s_i, +1, y_i^{s_i^{-1}}, d_i^{-1}, c_i^{-1})`. The walk
closes up:
- edge 1 starts at `y_1^{c_1^{-1}} = u^{π_0 c_1^{-1}} = u`;
- edge `i + 1` starts at `y_{i+1}^{c_{i+1}^{-1}} = y_i^{s_i^{ε_i} π_i c_{i+1}^{-1}} = y_i^{s_i^{ε_i} d_i}`,
  where edge `i` ends;
- edge `k` ends at `y_k^{s_k^{ε_k} d_k} = u^z = u`, because `z ∈ ker ρ` fixes `u`.

So `E(z) = Σ ε_i e_{s_i}` is the label sum of a closed walk in the level-`m` loop graph.

The level-`m` loop graph is the level-`p` one, relabelled. A letter `s` has a level-`m`
loop only if its section path returns to `(s, 1)` at every multiple of `p`. By (T_p) that
forces `s|_{x_s} = c s d` (`|x_s| = p`) at each block. Induction on `m/p` then gives:
- the level-`m` loop is `c s d`, with the same `c, d`;
- its edge runs from `ι^{m/p}` to `o^{m/p}`, where `ι = x_s^{c^{-1}}` and `o = x_s^{s d}`;
- `c` and `d` act only on the first letter of the next block.

The map `b ↦ b^{m/p}` on vertices is injective, which proves (1).

For (2): every state letter of `z` goes to the child `u`, so `z|_v ∈ P` for `v ≠ u` in
`X^m`. Hence `M^m E(z) = Σ_v E(z|_v) = E(z)`. Also
`M^m − I = (I + N)^{m/p} − I = N Q`, where `Q = (m/p) I + binom(m/p, 2) N + ⋯` is
invertible and commutes with `N`. So `N E(z) = 0`. ∎

**Theorem (item 3).** Let `L` be valid on `F_D` and `Λ_{low}` valid on `F_{D_low}`.
Suppose `λ` is supported on `D` and satisfies (i), (ii) and (iii) of the claim, with
`K_D = {r ∈ C_D : L r = 0, N r = 0}`. Then `λ` is valid on `F_D`.

*Proof.* Let `w ∈ ker ρ ∩ F_D`. By section-closure, all its sections lie in `F_D`.

*Step 1 (conservation).*
`Σ_{v ∈ X^{(n+1)p}} λE(w|_v) = Σ_{v ∈ X^{np}} (λ + λN) E(w|_v)`. On vectors supported on
`D`, `λN = Σ c_μ μ` with `μ ∈ L` by (i). Each `w|_v` is a relator in `F_D`, so its
`λN`-term vanishes. Hence `Σ_{v ∈ X^{np}} λE(w|_v) = λE(w)` for all `n`.

*Step 2 (threads).* Let `τ_n` be the total number of top letter occurrences at level `np`.
By (c), `τ_n` is non-increasing, so it is constant from some `n_0` on. From then on, every
top occurrence is a cycle letter whose top letter goes to exactly one child. So the number
of vertices carrying top letters is non-decreasing and at most `τ_{n_0}`, hence eventually
constant. After that, each such vertex has exactly one such child. This gives finitely
many *threads* `v_j(n)`.

Along a thread, `z_j(n) = w|_{v_j(n)}` is a single iterated section, so its count is
non-increasing and eventually constant. The next word `z_j(n + 1) = z_j(n)|_x` is
determined by `z_j(n)`, because `x` is the unique child carrying top letters. There are
finitely many words of a given count. So `z_j(n)` is eventually periodic, say with a
period of `m/p` steps.

Take `n` beyond all these stabilizations. Then:
- each thread word `z_j = z_j(n)` satisfies `z_j|_{u_j} = z_j` for its thread path
  `u_j ∈ X^m`;
- because the count is constant, every letter of `z_j` keeps a state letter along `u_j`;
- `z_j` is a relator.

So Lemma A applies: `E(z_j) ∈ C_D` and `N E(z_j) = 0`. Also `L E(z_j) = 0` by validity of
`L`. So `E(z_j) ∈ K_D`, and `λE(z_j) = 0` by (ii).

*Step 3 (the rest).* Every other vertex `v` at level `np` carries a relator `w|_v` with no
top letter, so `w|_v ∈ F_{D_low}`. By (iii), `λ` agrees on `D_low` with some
`μ ∈ span Λ_{low}`, so `λE(w|_v) = μE(w|_v) = 0`.

By Step 1, `λE(w) = Σ_j λE(z_j) + Σ_{\text{other}} λE(w|_v) = 0`. ∎

Each fixpoint round adds only functionals that are valid given the previous round, so
induction on rounds and on `|D|` shows that every `Λ_D` computed by `descent.py` is valid.

**Corollary.** Every `λ ∈ Λ_S` gives a homomorphism `λ ∘ E : G → Q` with image in a
finitely generated subgroup. Linearly independent functionals give independent maps, so
`b_1(G) ≥ dim Λ_S`.

## 2. The chain (a,a,e) survivor has H_1 = Z^3 (items 1 and 2)

The recursion (from `family("chain","a","a","e","","","")`, where `a = α` and `e = β`):
- `s = α` with `s|_0 = s`, `s|_1 = a`, `s|_2 = e`, `s|_3 = t`;
- `t = α` with `t|_0 = t`, `t|_4 = a`, `t|_5 = u`;
- `u = β` with `u|_0 = u`, `u|_6 = a`;
- all other sections are trivial.

(U) holds, and the section digraph is `s → t → u` with a self-loop at each letter, so `p = 1`.
In the basis `(e_s, e_t, e_u)`, `M e_s = e_s + e_t`, `M e_t = e_t + e_u` and `M e_u = e_u`.
So `N = M − I` sends `e_s ↦ e_t ↦ e_u ↦ 0`, and `λN = (λ_t, λ_u, 0)`.
(T_1) holds because each letter has exactly one section containing itself.

The level-1 loop graph has three edges, all from `0` to `0^α = 0^β = 1`, labelled `s`, `t`
and `u`. Hence `C_S = ⟨e_s − e_u, e_t − e_u⟩` and `N(a(e_s − e_u) + b(e_t − e_u)) = a e_t + b e_u`.
So `C_D ∩ ker N = 0` for every `D`, and (ii) is empty throughout.

- `D = {u}`, `D_low = ∅`. Column `u` of `N` is zero, so (i) holds for every `λ`, and
  `Λ_{u} = ⟨e_u⟩`.
- `D = {t,u}`, `D_low = {u}`. Round 1 (`L = ∅`): (i) asks `(λ_u, 0) = 0` on the columns
  `t, u`. This gives `e_t`. Round 2 (`L = ⟨e_t⟩`): `(λ_u, 0)` is a multiple of `(1, 0)`, and
  (iii) is automatic. This gives `Λ_{t,u} = ⟨e_t, e_u⟩`.
- `D = S`, `D_low = {t,u}`. Rounds 1, 2 and 3 give `⟨e_s⟩`, then `⟨e_s, e_t⟩`, then
  `Λ_S = Q^3`, in the same way.

`descent.py` (with no arguments) prints exactly these spaces and returns `(1, 3, I_3)`.

So by §1, `E : F → Z^3` factors through `G`, and it is onto because `E(s), E(t), E(u)` is the
standard basis. By item 1 of `unit-weight-polynomial-recursions-split-over-loop-edges`,
`G' = ⟨⟨P⟩⟩_G` (since `P = M_11` is perfect). So `G/G'` is generated by the images of
`s, t, u`, and it is abelian and surjects onto `Z^3`. Hence **`H_1(G; Z) = G/G' ≅ Z^3` via
`E`**, and `b_1(G) = 3`.

## 3. The loops generate G (item 1)

`H = ⟨s, t, u⟩`. These are the three level-1 loops `ℓ_s = s`, `ℓ_t = t`, `ℓ_u = u`, and
they are nontrivial. For `x ∈ X`, let `H_x = {h|_x : h ∈ H, x^h = x}`, and let
`ι_x(g)` be the element with section `g` at `x` and trivial root and other sections.

**(R1) `H_x = G` for all `x`.** First take `x = 0`. The elements `u^5`, `sU`, `tU`, `s^{11}` and
`t^{11}` fix `0` (`β` has order 5, `α` has order 11, `0^α = 0^β = 1`). Their sections at `0`
are `u`, `sU`, `tU`, `s·a·e·t` and `t·a·u`. So `H_0 ∋ s, t, u, a, e`, which gives `H_0 = G`.
`H` is transitive on `X` (`s` has root `α`), so `H_x` is conjugate to `H_0` in `G` and equals
`G`.

**(a) A coordinate element.** Put `d = [sT, (sT)^{sUSSS}] ∈ H`. `loops_generate.py`
checks exactly (by `R.trivial`) that `d` has trivial root and that `d|_x = 1` for `x ≠ 2`.
It also checks that `δ := d|_2` has nontrivial root. So `d = ι_2(δ)`.

**(b)** Put `K_2 = {g ∈ G : ι_2(g) ∈ H}`. This is a subgroup containing `δ`. If `h ∈ H`
fixes `2`, then `h^{-1} ι_2(g) h = ι_2(g^{h|_2})`, and by (R1) `h|_2` runs over `G`. So
**`K_2 ⊴ G`**. The root image of `K_2` is a nontrivial normal subgroup of the simple group
`M_11`, so it is all of `P`.

**(c) `K_2 ⊇ N_1 := ∏_x ι_x(G')`.** Take `k ∈ K_2` whose root moves some `y` to `y' ≠ y`, and
take `g, h ∈ G`. Then `[k, ι_y(g)] = ι_{y'}(g_1)·ι_y(g)` for some `g_1`, because
`k^{-1} ι_y(g)^{-1} k = ι_{y'}(·)`. Coordinates at different vertices commute, so
`[[k, ι_y(g)], ι_y(h)] = ι_y([g, h])`. The left side lies in `K_2` by normality, so
`ι_y(G') ⊆ K_2`. `K_2` is normal and `G` is transitive on `X`, so `ι_x(G') ⊆ K_2` for every
`x`.

**(d) `K_2 ⊇ G'`.** By §2, `G/N_1 = (G/G')^X ⋊ P = (Z^3)^X ⋊ P`. Take `k ∈ K_2` with root
`π ≠ 1`, and write `k ≡ v π` modulo `N_1`. Then `[k, ι_x(g)] ≡ ḡ e_{x^π} − ḡ e_x` or its
negative, depending on the side convention. Here `ḡ = E(g)` is an arbitrary vector of
`Z^3`. Letting `x` and `π` vary over the root image `P` of `K_2`, which is transitive,
these elements generate the sum-zero sublattice `Z_0 ⊂ (Z^3)^X`. So `K_2 ⊇ N_1 Z_0`.

Modulo `N_1 Z_0`, `G` becomes `Z^3 × P`, with `P` acting trivially on `(Z^3)^X / Z_0 ≅ Z^3`.
Then `[k, σ] ≡ [π, σ]` for `σ ∈ P`. As `π` runs over `P`, these commutators generate
`[P, P] = P`. So every `σ ∈ P` lies in `K_2 · N_1 Z_0 = K_2`, and
`K_2 ⊇ ⟨⟨P⟩⟩_G = G'`.

**(e) `H ⊇ N_1`.** From (d), `ι_2(G') ⊆ H`. For `h ∈ H` with `2^h = x`,
`h^{-1} ι_2(g) h = ι_x(g^{h|_2})`, and `G'` is normal. So `ι_x(G') ⊆ H` for all `x`.

**(f) `H N_1 = G`.** `lat1.py` computes the image of `H` in
`G/N_1 = Z^{33} ⋊ M_11`, where the coordinates are `(E(g|_x))_x` and the root is exact.
- The root image has order 7920.
- The 23760 Schreier generators of the root kernel of `H` span a lattice of rank 33 and index 1
  in `Z^{33}` (a triangular basis whose diagonal entries are all 1).

So `H` maps onto `G/N_1`. With (e), **`H = G`**.

**Consequence.** In the star of `unit-weight-polynomial-recursions-split-over-loop-edges`,
item 3, the leaf `F(ℓ_s, ℓ_t, ℓ_u)` maps onto `G`. So condition (iii) of the
tree-of-factors obstruction fails, and no star splitting separates this survivor. It is a
genuine (γ)-case. §2 kills it by homology instead.

## 4. Classification of the 1373 survivors (item 4)

`classify.py` reruns the exact screen `analyse` of `poly_star_screen.py` over the four
families (root words from the 8 permutation words, decorations `{"", a}`). On every
survivor it runs `certify`, which asserts (U), (T_p) and the nilpotence of `N`.
None of the assertions fails.

| family | `p` | survivors | `dim Λ_S = 3` | `= 2` | `= 1` | `= 0` |
|---|---|---|---|---|---|---|
| chain  | 1 | 792 | 637 | 155 |  0 | 0 |
| fan    | 1 | 358 |   0 | 337 | 21 | 0 |
| cycle  | 2 | 202 |   0 | 181 | 21 | 0 |
| scycle | 4 |  21 |   0 |   0 | 21 | 0 |
| total  |   | 1373 | 637 | 673 | 63 | 0 |

- The 21 fan survivors with `dim = 1` all have `Λ_S = ⟨e_s + e_u⟩`, so the sink letter's
  own sum `e_t` is killed there.
- The 21 cycle survivors with `dim = 1` have `Λ_S = ⟨e_s + e_t⟩` (the sum over the section
  cycle `s ↔ t`), and the 21 scycle survivors have `Λ_S = ⟨e_u⟩`.

**Sanity check (`sanity.py`).** On every 16th member of all four families (1024 recursions,
survivors or not), a large sample of words was tested. The test words were the letters,
the products `s t^{±1}`, and the level-`p` loops. 64 of them have finite order `≤ 60` in `G`,
and every certified `λ` vanishes on every such word. This is consistent with §1, since a
functional that descends to `G → Q` kills torsion.

## 5. Not finitely presented (items 2 and 4)

Every survivor has `b_1(G) ≥ dim Λ_S ≥ 1` by §1. Item 3 of
`fully-self-replicating-fp2-groups-have-odd-cyclic-h1` says a fully self-replicating group
of type `FP_2` has finite `H_1`. So **no survivor is of type `FP_2`, and none is finitely
presented.** Independently, item 3(d) of `fully-self-replicating-fp-infinity-groups-are-acyclic`
(`d = 11 ≥ 4`) kills the 1310 survivors with `dim Λ_S ≥ 2`. By item 5 of the `FP_2` node,
their Tits hosts `(G ≀ F) *_{G×G} (G ≀ F)` are not finitely presented either.

Combined with item 5 of `unit-weight-polynomial-recursions-split-over-loop-edges`, **all
16,384 members of the four screened families are not finitely presented.**
