---
rg: 2
id: rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph
kind: claim
title: V_2(Z/2 wr Z) for the lamplighter automaton is the full group of the one-vertex 2-graph e_i f_j = f_i e_{i+j}, hence of type F_infinity, integrally acyclic and simple, although Z/2 wr Z is not even finitely presented
distinct_from:
  rn-lamplighter-is-a-function-field-stein-group: that identifies V_2(Z/2 wr Z) with PAff(F_2[[1+t]]; R) and builds a proper contractible complex, leaving F_n open; this finds a 2-graph inside Aff(R) and settles F_infinity through Li's theorem, with no Morse theory.
  rover-nekrashevych-group-of-lamplighter-automaton-is-fp: that proves finite presentation of the same group through lift ideals; this proves type F_infinity and computes the integral homology.
  rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp: that proves V_q(F_q wr Z) finitely presented; this proves F_infinity and rational acyclicity for the same family.
  li-finite-k-graph-full-groups-are-f-infinity: that is Li's theorem for k-graphs; this recognises a Roever-Nekrashevych group of a non-finitely-presented self-similar group as one of them.
  primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple: that embeds 2-graph full groups in F_infinity simple groups; this shows one Roever-Nekrashevych group is itself a 2-graph full group.
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/two_graph.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-two-graph.txt
---

**ESTABLISHED (proof in `rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph-proof`; unreviewed).** Parts 1, 2 and
4 are proved in full here. The finiteness and homology conclusions are imports of Li's theorems, applied to a groupoid
whose hypotheses are checked in the proof.

## Setting

- `G = Z/2 ≀ Z` acts on the binary tree through the lamplighter automaton `a = σ(a, b)`, `b = (a, b)`. This is the
  same action as the affine automaton `x ↦ tx + c` on `O = F_2[[π]]`, `π = 1 + t`, with splitting maps
  `λ_x(y) = x + πy`.
- `R = F_2[t, 1/t, 1/π]` and `R^× = t^Z × π^Z`. By `rn-lamplighter-is-a-function-field-stein-group`,
  `V_2(G) = PAff(O; R)`, the full group of the germ groupoid `𝒢` of `Aff(R) = R ⋊ R^×` acting on `K_π`, restricted
  to `O`.
- Put `ρ_* = (F_2[[t]], t^{-1}F_2[[t^{-1}]])`, a vertex of `T_0 × T_∞` of level `1`. At that level `G` acts simply
  transitively.

## Statement

1. **A 2-graph inside `Aff(R)`.** The set
   `P = {a ∈ Aff(R) : a(O) ⊆ O and a(ρ_*) is an ancestor of ρ_* in T_0 × T_∞}`
   is a submonoid with trivial units. The map `d(ux + b) = (log_2|u|_0, log_2|u|_∞)` is a homomorphism
   `Aff(R) → Z²` that sends `P` into `N²`, and `(P, d)` is a one-vertex 2-graph.
   - Its edges are `e_c(x) = (π/t)x + c/t` of degree `(1, 0)` and `f_c(x) = πx + c` of degree `(0, 1)`, for `c ∈ {0, 1}`.
   - Its factorisation rule is `e_i f_j = f_i e_{i+j}`, with indices mod 2.
   - Explicitly, `P_{(m,n)} = {t^{-m}π^{m+n}x + b : b ∈ span(t^{-m}, ..., t^{n-1})}`, and `a ↦ a(O)` is a bijection
     from `P_{(m,n)}` onto the balls of depth `m + n` in `O`.
   - `f_c = λ_c`, `e_0 = λ_0 ∘ t^{-1}x` and `e_1 = λ_1 ∘ t^{-1}(x+1)`, so the edges are Roever–Nekrashevych
     elements built from `G`.
2. **The groupoid.** Let `Λ` be this 2-graph. Its Kumjian–Pask path groupoid `G_Λ` is isomorphic to `𝒢`, through
   `Λ^∞ ≅ O`. Hence
   `V_2(Z/2 ≀ Z) = PAff(O; R) = F(G_Λ)`.
3. **Finiteness.** `V_2(Z/2 ≀ Z)` is of type `F_∞`. This follows from Li's theorem
   (`li-finite-k-graph-full-groups-are-f-infinity`), since `Λ` has two edges of each colour at its only vertex.
4. **Homology.** `H_*(𝒢; Z) = 0` in every degree. There are two independent computations:
   - directly, through `H_*(Aff(R); C_c(K_π, Z))`;
   - through the Koszul complex of the 2-graph, with vertex matrices `(2)`, `(2)`, which is exact over `Z`.
5. **Acyclicity and simplicity.** `V_2(Z/2 ≀ Z)` is integrally acyclic: `H_k(V_2(G); Z) = 0` for every `k > 0`. It is
   perfect, and it is simple. This is Li's Corollary D (arXiv:2209.08087), with minimality, comparison and the
   absence of isolated points checked in the proof. Simplicity follows because the commutator subgroup of a minimal
   effective ample Cantor groupoid's full group is simple, and here `F = D`.
6. **All `q`.** For a prime power `q` and `a ∈ F_q^*`, the affine lamplighter automaton on `F_q[[t-a]]` gives
   `V_q(F_q ≀ Z) = F(G_{Λ_q})`, where `Λ_q` is the one-vertex 2-graph with `q` edges of each colour and
   `e_i f_j = f_{i/a} e_{j-i/a}`. It is of type `F_∞`, and `H_0(G_{Λ_q}) = H_1(G_{Λ_q}) = Z/(q-1)`, with all other
   groups zero. So `V_q(F_q ≀ Z)` is rationally acyclic, and its abelianisation surjects onto `Z/(q-1)`.
7. **Not Brin's `2V`.** `2V` is the full group of the product 2-graph `e_i f_j = f_j e_i`, and is also `F_∞` and
   acyclic. The groupoids differ:
   - in `𝒢`, every isotropy group is trivial or `Z²`, the latter exactly at `O ∩ F_2(t)`;
   - the groupoid of `2V` has points with isotropy `Z`.

   With the spatial realisation of full groups (Matui; Rubin), `V_2(Z/2 ≀ Z)` is not isomorphic to `2V`. This part
   is citation-level: the spatial theorem is not re-checked here.

## Why it matters for the lane

- This is the first Roever–Nekrashevych group of a self-similar group that is **not finitely presented** shown to
  be of type `F_∞`. Skipper–Witzel–Zaremsky and Li (Theorem C, Corollary F) both need `G` of type `F_n`.
- The mechanism is not a Morse-theoretic rescue of `G`. The whole of `V_2(G)` is re-coordinatised: the
  self-similar structure over the non-f.p. group `G` is traded for a 2-graph structure with trivial units. The
  "level 1 is simply transitive" fact of `rn-lamplighter-is-a-function-field-stein-group` is exactly what makes the
  units trivial.
- The Morse function `Σ_i c^{|β(ρ_i)-1|}` proposed for the decorated Stein–Farley complex has local minima at every
  vertex whose leaves all sit at height `1`. There, merges cost `c - 2 > 0`, and splits and tree moves ascend. So its
  descending links are empty at unbounded height, and Brown's criterion cannot be run with it. This is recorded in
  the Attempts of `rn-lamplighter-is-a-function-field-stein-group`. The 2-graph route makes that complex unnecessary.
