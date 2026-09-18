---
rg: 2
id: fp-rsgs-have-fp-full-closures
kind: claim
title: Every finitely presented rational similarity group has a finitely presented full closure (BBMZ-hyperbolic Question 1.4)
distinct_from:
  contracting-rsgs-embed-in-fp-simple-groups: that imports Theorem B, finite presentation of FULL contracting RSGs; this asks whether finite presentation of an arbitrary RSG passes to its full closure, with no contracting hypothesis.
  contracting-rsgs-have-fp-full-closures: that settles the contracting case of this question; this is the question itself.
  fp-clopen-transitive-full-cantor-groups-have-type-a-actions: that turns a finitely presented FULL Cantor group into a type (A) actor; this asks when fullness can be added without losing finite presentation.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**OPEN.**

**The printed question.** Belk--Bleak--Matucci--Zaremsky, *Hyperbolic groups satisfy the
Boone--Higman conjecture*, arXiv:2309.06224, TeX source line 236 (local copy
`$GQ/src/bh-free-03/bbmz2-2309.06224.tex`), verbatim:

> "If $G$ is a finitely presented RSG, then must the full closure of $G$ also be finitely presented?"

The preceding sentence (line 233) motivates it by Scott's theorem that the
Röver--Nekrashevych group `V_d(G)` of a finitely presented self-similar group `G` is
finitely presented (and Skipper--Witzel--Zaremsky's higher version).

**Terms** (BBMZ, as quoted in `contracting-rsgs-embed-in-fp-simple-groups`). `Σ_Γ` is the
edge shift of a finite graph, `R_{Γ,E}` the group of rational homeomorphisms of a nonempty
clopen `E` (finitely many local actions). An RSG is a subgroup `G ≤ R_{Γ,E}` that realizes
the canonical similarity between any two proper cones with the same terminal vertex. The
full closure `[[G]]` is the group of homeomorphisms of `E` that locally agree with `G`.
`G` is contracting if `Σ_Γ` has an irreducible core and the nucleus `N_G` (local actions
occurring infinitely often, over `g ∈ G`) is finite.

**Why it matters for Boone--Higman.** A finitely presented full clopen-transitive Cantor
group is a type (A) actor (`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`).
So a positive answer turns every finitely presented RSG into a type (A) host. That is the
Cantor-host gap between `decidable-groups-embed-in-fp-locally-moving-groups` and
`boone-higman-conjecture`, restricted to rational hosts.

## Known cases

- **Contracting inputs:** yes, by `contracting-rsgs-have-fp-full-closures` (BBMZ Theorem B
  applied to `[[G]]`). So any counterexample is non-contracting.
- **Full inputs:** trivially yes (`[[G]] = G`). This covers Röver--Nekrashevych groups of
  finite-state self-similar groups, which BBMZ note are full RSGs (TeX line 657).
- **The first open family:** `v-normalizer-rsgs-contract-iff-finite-outer-order`. For every
  homeomorphism `t` normalizing Thompson's `V` whose class in `Out(V)` has infinite order,
  `Γ_t = ⟨V, t⟩ = V ⋊ ⟨t⟩` is a finitely presented, non-contracting, non-full RSG. For order
  at least 3 its core is asynchronous
  (`synchronous-cores-in-out-v-have-order-at-most-two`), so neither Theorem B nor the
  synchronous Scott/Skipper--Witzel--Zaremsky theory applies to `[[Γ_t]]`. The family was
  first noted in bh-free-23's artifact, without claims.

## Attempts

1. **The germ groupoid of the test family (bh-higman-classic, 2026-09-18).** *Reduction, not decided.*
   - **The groupoid.** Take `t` of infinite order in `Out(V)`. By
     [[v-normalizer-groupoids-carry-lag-cocycle-iff-lipschitz]], `[[Γ_t]]` is the topological full group
     of `O ⋊_t Z`, and the lag cocycle extends iff `t` is Lipschitz.
   - **The Lipschitz case** (`t ∈ L_2 ≅ Inert(σ_2)`). The groupoid is Z-graded: a "rank-two Cuntz"
     groupoid built from the commuting pair `(σ, F)` of the full 2-shift and an inert `F`. That is the
     nearest known shape to the `k`-graph groupoids whose full groups X. Li proves are of type `F_∞`
     (`li-finite-k-graph-full-groups-are-f-infinity`).
   - **Why Li does not apply as stated.**
     - His self-similar and Zappa–Szép cases need a degree-preserving action.
     - An inert `F` of infinite order is intrinsically asynchronous
       ([[synchronous-cores-in-out-v-have-order-at-most-two]]).
     - Recoding by higher blocks makes `F` causal, but `F^{-1}` then still needs lookahead. Only one-sided
       automorphisms (the identity and the flip) are causal both ways.
   - **No homological obstruction expected (heuristic).** A Wang-type exact sequence for `O ⋊ Z`, together
     with `H_*(O_2) = 0`, would give `H_*(G_t) = 0`. That sequence was not checked at source.
   - **Next.** Either (a) a Garside or Stein–Farley complex for `[[Γ_t]]` built from the lag grading
     (Lipschitz case), or (b) an obstruction for non-Lipschitz `t`, where no Z-grading exists.
2. **A Scott-type presentation (bh-higman-classic, 2026-09-18).** *One step missing.*
   - **Setting.** Let `V ≤ G ≤ N(V)`, which covers every `Γ_t`. By
     [[v-by-normalizer-groups-are-self-similar]], `G` is self-similar up to `V`,
     `[[G]] = ⟨V, ι_0(G)⟩`, every element has a cone-partition normal form `w · ∏ ι_{u_i}(g_i)`, and a
     normal form is trivial iff its pieces cancel against `V`.
   - **The candidate presentation.** Take a finite presentation `G = ⟨S | R⟩` with `S ⊇ S_V`, and
     adjoin hatted letters `Ŝ` (intended `ι_0(s)`), with these relations:
     - `R` and its hatted copy `R̂`;
     - `[ŝ, y] = 1` for `y` in a finite generating set of `V_{C_1}`;
     - `v̂ = ι_0(v)` for `v ∈ S_V`, the right side written as a `V`-word;
     - disjoint-support commutators `[ŝ, c t̂ c^{-1}]` and `[ŝ, d t̂ d^{-1}]`, where `c, d ∈ V` send `C_0`
       prefix-wise onto `C_1` and onto `C_{10}`;
     - for each `s ∈ S`, the one-level expansions `s = w_s · ι_0(s_0) ι_1(s_1)` and
       `ŝ = ι_0(w_s) · ι_{00}(s_0) ι_{01}(s_1)`, where `w_s ∈ V` matches `{C_0, C_1}` with
       `{s(C_0), s(C_1)}` and `s_a ∈ G` are the normalized restrictions.
     All of these are finite in number.
   - **What is proved.** The natural map onto `[[G]]` is surjective. It is injective on every element
     that the relations bring to normal form (item 4 of the self-similarity node, plus faithfulness of
     the copies of `G` and `V`).
   - **The missing step: normalization.** Moving a `V`-element `w` past a cone copy `ι_y(g)` needs an
     expansion of `ι_y(g)` to a depth fixed by `w`.
     - For asynchronous `g` the images of depth-`d` cones are clopens described only at depth
       `d + ℓ`. So the `V`-parts created by an expansion must be moved past the other factor, which
       has to be expanded `ℓ` deeper. That creates new `V`-parts, and so on.
     - For Scott's synchronous groups `ℓ = 0`: the `V`-parts are level permutations, and the descent
       stops. That is why Scott needs only finite presentation of `G`.
     - For contracting groups (Theorem B) the finite nucleus bounds the descent.
     - For `Γ_t`, `ℓ` is the delay of `t`: bounded per step when `t` is Lipschitz, growing with the
       word when it is not.
   - So Question 1.4 for this family comes down to whether the descent terminates, or can be avoided
     by a cleverer normal form. A proof that no finite set of relations stops it would give a
     negative answer.
3. **Narrowing the gap with restriction-closed generators (bh-higman-classic, 2026-09-18).**
   *Progress, still one step missing.*
   - **The generating set.** For `V ≤ G ≤ N(V)`, take generators `S = S_V ∪ {h_1, …, h_m}`. Each
     normalized restriction of `h_i` lies in `h_i V = V h_i` (item 1 of
     [[v-by-normalizer-groups-are-self-similar]]). So every generator restricts to a single generator,
     up to `V` on either side (the case "K = 1").
   - **Pure one-sided expansions.** Add, for each `h_i`, one left and one right one-level expansion
     relation:
     - left: `ĥ_i = ι_0(W_i) · ι_{00}(v_0 h_i) ι_{01}(v_1 h_i)`;
     - right: `ĥ_i = ι_{00}(h_i v'_0) ι_{01}(h_i v'_1) · ι_0(E_i)`.
     Then every cone copy of a generator has a pure left expansion (`V` only on the left) and a pure
     right expansion to every finer partition. The derivation is a recursion that strictly lowers
     the depth, because restrictions of generators are generators times `V`.
   - **Layered normal forms.** Pushing each `V`-element to the right end uses only pure right
     expansions of generator copies. So every word of the candidate presentation equals
     `L · Λ_1 ⋯ Λ_m · R`, where `L, R ∈ V` and each layer `Λ_k` is a product of generator copies over a
     cone partition.
   - **What remains.** Collapse the layers to one partition, so that the triviality test of item 4
     applies.
     - Two layers collapse: left-expand the first, right-expand the second, and combine the pieces.
     - The combined pieces are products of two generators, whose derived expansions are two-sided.
     - Pure one-sided expansions of products such as `t^n`, `n ≥ 2`, are not obtained this way. Every
       recursion tried produces a `V`-part between two layers, because the `V`-parts of asynchronous
       expansions send cones to non-cones.
   - **Where it now stands.** Question 1.4 for every finitely presented `V ≤ G ≤ N(V)` (in particular
     every `Γ_t`) reduces to deriving pure one-sided expansions of `ι_u(h^n)` from the finitely many
     relations. Equivalently, it reduces to a normal form that never has to multiply pieces. A
     Stein–Farley complex whose cells are layered normal forms is the natural next tool.
