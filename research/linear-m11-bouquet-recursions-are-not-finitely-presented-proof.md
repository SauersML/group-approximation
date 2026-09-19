---
rg: 2
id: linear-m11-bouquet-recursions-are-not-finitely-presented-proof
kind: route
title: Proof that a finite-image shared sub-basis turns the stable presentation into an amalgam over a finite group, that one-endedness then forces a factor onto G, and that every two-letter bouquet under (U) and (L1), in particular every linear M_11 bouquet, meets the hypotheses
target: linear-m11-bouquet-recursions-are-not-finitely-presented
requires:
  - pure-loop-self-replicating-groups-are-not-fp
  - same-point-loop-recursions-reduce-to-loop-graph-words
  - linear-bouquet-recursions-ray-loop-and-contraction
artifacts:
  - experiments/bouquet-amalgam-obstruction-2026-09-19/bouquet_amalgam.py
  - experiments/bouquet-amalgam-obstruction-2026-09-19/bouquet_amalgam.out
  - experiments/bouquet-amalgam-obstruction-2026-09-19/survivor_kurosh.py
  - experiments/bouquet-amalgam-obstruction-2026-09-19/survivor_kurosh.out
---

**Status: ESTABLISHED (unreviewed).** §1 and §2 are proofs by hand. §3 is a finite exact
check. The only outside facts are two standard ones from Bass–Serre theory and ends
(Serre, *Trees*, I.4 and I.6; Stallings), stated where they are used. Notation is that of the
claim.

## 1. The finite-edge amalgam obstruction (item 1)

Suppose `G = F/⟨⟨R⟩⟩` is finitely presented, with hypotheses (i)–(iii).

**Retraction.** By item 1 of `pure-loop-self-replicating-groups-are-not-fp`, for `k ≥ k_0`
the endomorphism `T_k` of `F` satisfies `T_k(K) ⊆ ⟨⟨Q^∞⟩⟩`, and `T_k(w)` represents `w` in `G`.
So, for every normal `N` with `⟨⟨Q^∞⟩⟩ ⊆ N ⊆ K`, `T_k` induces `τ_N : G → F/N` with
`ρ_N τ_N = id`, where `ρ_N : F/N ↠ G`. In particular `τ_N` is injective.

**The amalgam.** `F_0` is a finitely generated free group, and `N_0 = ker(ρ|_{F_0})` has
finite index in it by (i). So `N_0` is the normal closure in `F_0` of a finite set `R_0`.
By (ii), each word of `Q^∞` is conjugate to a word of `F_1` or of `F_2`. Let `Q_i` be the
chosen conjugates that lie in `F_i`, and put
`Γ_i = F_i / ⟨⟨Q_i ∪ R_0⟩⟩_{F_i}` and `N = ⟨⟨Q^∞ ∪ R_0⟩⟩_F`.
- `F = F_1 *_{F_0} F_2`, and `N` is the normal closure of subsets of the two factors. So
  `F/N` is the pushout of `Γ_1 ← D → Γ_2`, where `D = F_0/N_0`.
- Both maps `D → Γ_i` are injective. Their composites with `Γ_i → G` are the embedding
  `F_0/N_0 ≅ ρ(F_0)`. These composites are well defined since `Q_i ∪ R_0 ⊆ K`.
- A pushout of two injections is the amalgamated free product (Serre I.1). So
  `F/N = Γ_1 *_D Γ_2`, with `D` finite. Also `⟨⟨Q^∞⟩⟩ ⊆ N ⊆ K`, so `τ = τ_N` exists.

**One-endedness.** `G` is finitely generated, infinite and one-ended (item 2 of
`pure-loop-self-replicating-groups-are-not-fp`). Let `τ(G) ≅ G` act on the Bass–Serre tree
of `Γ_1 *_D Γ_2`, without inversions. Its edge stabilizers lie in conjugates of `D`, so they
are finite.
- Suppose `τ(G)` fixed no vertex. A finitely generated group acting on a tree without a
  global fixed point splits nontrivially, as an amalgam or an HNN extension, over an edge
  stabilizer (Serre I.6.5 and I.4.3).
- A nontrivial splitting over a finite group gives more than one end (Stallings).
- This contradicts one-endedness, so `τ(G)` fixes a vertex: `τ(G) ≤ g Γ_i g^{-1}` for some
  `i` and some `g ∈ F/N`.

**Conclusion.** Apply `ρ_N`. Then `G = ρ_N τ(G) ≤ h ρ(F_i) h^{-1}` with `h = ρ_N(g)`, since
`ρ_N(Γ_i) = ρ(F_i)`. So `ρ(F_i) ⊇ h^{-1} G h = G`, contradicting (iii). ∎

With `B_0 = ∅`, `D = 1` and this is the free-product argument of the cited item 2. The new
point is that the two factors may share letters, provided their common image is finite.

## 2. Two-letter bouquets (item 2)

Assume (U) and (L1), with state letters `s, t` only and `Γ_1` a bouquet at `z`. Write
`ℓ_s = S = A s B` and `ℓ_t = T = C t D` for the loops, `s|_{x_s} = S` and `t|_{x_t} = T`,
where `A, B, C, D` are rooted. Let `F_{rt}` be the free group on the rooted letters.

**(a) Which letter reaches which.** Call `s` *reaches* `t` if `t` occurs in some `s|_x` with
`x ≠ x_s`.
- By (L1), `s|_x` for `x ≠ x_s` contains no `s`, since that would be a second self-loop.
- If `s` reached `t` and `t` reached `s`, the digraph would have a cycle `s → t → s` of
  length two, or `s → t^{-1} → s`, or one of their signed variants. (L1) forbids this.
- Relabel so that `t` does not reach `s`. Then every `t|_x` with `x ≠ x_t` is a rooted word,
  so `t` is bounded. If `s` does not reach `t` either, then `s` is bounded too. `G` is then a
  bounded automaton group, and it is not finitely presented by the bounded kill in item 5 of
  `same-point-loop-recursions-reduce-to-loop-graph-words`.
- So assume `s|_{x'}` contains `t^{±1}` for some `x' ≠ x_s`. By item 4 of the same node,
  `s` is then unbounded.

**(b) Sections.** `S|_y = s|_{y^{π_A}}` because rooted letters have trivial sections, and
`y^{π_A} = x_s` exactly when `y = r_s = z`. The same holds for `T`. Hence:
- `S|_z = S` and `T|_z = T`, and `π_S`, `π_T` fix `z` (`w_s = w_t = z`);
- for `y ≠ z`, `S|_y ∈ F(rooted, t)` by (a), and `T|_y ∈ F_{rt}`;
- `F_1 := F(rooted, t) = F(rooted, T)` is section-closed, since `t|_{x_t} = T` and the other
  sections of `t` are rooted.

Let `u` be a reduced word over `S^{±1}, T^{±1}`, read at a point `y`. Every letter fixes
`z` and no other point is sent to `z`. So:
- if `y = z`, every letter is read at `z` and `u|_z = u`;
- if `y ≠ z`, every letter is read away from `z` and `u|_y ∈ F_1`.

By induction on `|v|`, `u|_v = u` if `v = z^n`, and `u|_v ∈ F_1` otherwise.

**(c) Hypothesis (ii).** Suppose `G` is finitely presented. By §2 of the proof of
`same-point-loop-recursions-reduce-to-loop-graph-words` (item 2 there), every `q ∈ Q^∞` has
the form `q''|_{v'}`, where `q'' ∈ C_c ∩ K` for a point `c`.
- `Γ_1` has only the two loops at `z` as edges, so `C_c = 1` for `c ≠ z`, and
  `C_z = λ(π_1(Γ_1, z)) = F(S, T)`.
- Since `q'' ≠ 1`, `q''` lies in `F(S, T)`, and by (b), `q` lies in `F_2 := F(S, T)` or in
  `F_1`.
- In the basis `{rooted letters, T, S}`, `F_1 = F(B_1 ∪ B_0)` and `F_2 = F(B_0 ∪ B_2)` with
  `B_0 = {T}` and `B_2 = {S}`. So (ii) holds, without any conjugation.

**(d) Hypothesis (i): `T` has finite order.** Let `m` be the order of `π_T`. Then:
- `(T^m)|_z = T^m`, since `π_T` fixes `z`;
- for `y ≠ z`, `(T^m)|_y` is a product of rooted words, so it represents an element `r_y`
  of `P`;
- `T^m` acts trivially on level 1.

Let `n` be the least common multiple of the orders of the `r_y`, and put `g = T^{mn}`. Then
`g` has trivial root, `g|_z = g`, and `g|_y = r_y^n = 1` for `y ≠ z`. By induction on the
level, `g` fixes every vertex, so `g = 1` in `G`. Hence `ρ(F_0) = ⟨ρ(T)⟩` is finite.

**(e) Hypothesis (iii).**
- `ρ(F_2) = ⟨S, T⟩` fixes `z`, while `G ⊇ P` does not. So `ρ(F_2) ≠ G`.
- `ρ(F_1) = ⟨rooted, t⟩` is generated by bounded automorphisms (finitary rooted letters and
  the bounded `t`), and bounded automorphisms form a group (Sidki).
- `s` is unbounded by (a), so `s ∉ ρ(F_1)` and `ρ(F_1) ≠ G`.

Item 1 now applies, and `G` is not finitely presented. ∎

## 3. The 472 linear M_11 bouquets (item 3)

The recursions are those of `bouquets()` in
`experiments/bouquet-ray-loop-2026-09-19/bouquets.py`
(`linear-bouquet-recursions-ray-loop-and-contraction`). That library asserts the bouquet
condition `r_s = w_s = r_t = w_t = z` for each of them.

Membership in the family already gives the hypotheses of §2:
- (U) and (L1) hold (item 6 of `same-point-loop-recursions-reduce-to-loop-graph-words`);
- the recursion is fully self-replicating with (SF) (Lemma S there);
- `P = M_11` is transitive;
- `t = π_t (C t D, 1, 1, 1, α, 1, …)` does not reach `s`;
- the linear section `s|_3 = t` makes `s` reach `t`.

`bouquet_amalgam.py` rechecks all of this from the letter data for each of the 472
recursions:
- (B), (Tb), (Sb) and (W) of the claim, as exact comparisons of reduced words;
- the level-1 sections of `S` and `T` away from `z`, which lie in `F(a, e, t)`;
- the order of `T`. `R.order` scans the multiples of the root order upward, and returns the
  first `j` with `T^j` trivial, which is the exact order. Triviality is decided exactly: the
  section closure of `T^j` is finite, and every word in it has trivial root.

The output is in `bouquet_amalgam.out`. `survivor_kurosh.py` computes the section closure
of `{[S, T], T^{ord T}}` in the basis `{a, e, S, T}` for the 20 commuting survivors of the
cited node. It finds `{[S, T], T^o, a^11}` in every case, each word in `F(S, T)` or
`F(a, e)`, which matches (c). It is not needed for the proof.
