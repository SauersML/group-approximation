---
rg: 2
id: one-steinberg-group-contains-every-gl-n-q
kind: claim
title: For any ring S containing Q and a binary Leavitt pair, the single group St_4(S) contains SL_m(Q) and GL_n(Q) for every m and n
distinct_from:
  leavitt-pairs-embed-sl-n-q-in-steinberg-groups: that puts SL_N(Q) in St_(6N+1)(S), a rank growing with N, by a self-contained swindle; this puts every SL_(4m)(Q), hence every GL_n(Q), in the one fixed group St_4(S), through Morita blocks over Q and the classical K_2 of matrix rings over a field.
  gl-n-q-explicit-natural-fp-overgroup: that is the question (Problem 2.7), with a group Gamma_n allowed to depend on n; this gives one group for all n at once when S is finitely presented.
  finitely-presented-divisible-ring-engine: that builds the finitely presented Q-algebra D; this uses D (or any S with a Leavitt pair) as the coefficient ring.
  non-ibn-rational-hosts-have-infinite-elementary-centre: that shows E_n(S) has infinitely generated centre, closing the projective-simple route; this is about the Steinberg group and makes no simplicity claim.
---

**OPEN (proof claimed by lane `gq-deep-free-1`, 2026-09-17; under review by
`gq-referee-a`, `gq-referee-b`, `gq-referee-c`).**

**Statement.** Let `S` be a unital ring with `Q ⊆ S` (unitally) and elements
`x_1, x_2, y_1, y_2` with `y_i x_j = δ_ij` and `x_1 y_1 + x_2 y_2 = 1`. Then:

1. For every `m >= 1` and every Cuntz family `t_1, ..., t_m` in `S` (`t_i^* t_j = δ_ij`,
   `Σ t_i t_i^* = 1`, where `t_i^*` denotes the chosen partner), the unital ring map
   `ι_m : M_m(Q) -> S`, `a -> Σ a_ij t_i t_j^*`, induces a homomorphism
   `St_4(ι_m) : St_4(M_m(Q)) -> St_4(S)` whose kernel is exactly `K_2(4, M_m(Q))`.
   Its image is a copy of `E_4(M_m(Q)) = SL_(4m)(Q)` inside `St_4(S)`.
2. Hence `SL_k(Q)` and `GL_n(Q)` embed in `St_4(S)` for all `k, n >= 1`
   (`GL_n(Q) <= SL_(n+1)(Q) <= SL_(4m)(Q)` for `4m >= n+1`).
3. If `S` is finitely presented, `St_4(S)` is **one** finitely presented group containing
   every `GL_n(Q)` (`steinberg-finite-presentation-and-kazhdan-theorem`). For
   `S = D` of `finitely-presented-divisible-ring-engine` (6 generators, 7 relations) this
   is explicit.

`D` has a Leavitt pair: `x_1 = w`, `y_1 = v`, `x_2 = s w`, `y_2 = v t`. Indeed `vw = 1`;
`vt·sw = v(ts)w = 1`; `sw·vt = s(wv)t = 1 - wv`, so `x_1y_1 + x_2y_2 = 1`; and
`v·sw = v(1 - wv)sw = 0`, `vt·w = vt(1 - wv)w = 0`, using `sw = (1-wv)sw` and
`vt = vt(1-wv)`, which follow from `x_2 y_2 x_2 = x_2`, `y_2 x_2 y_2 = y_2`.

**Credit and scope** (priority check, `research/artifacts/gq-gq-lit-arxiv-priority.md` §8).
- **Existence is classical.** Some finitely presented group contains every `GL_n(Q)`:
  `GL_∞(Q)` is countable and computably presented, so Higman--Neumann--Neumann and Higman
  embed it in a finitely presented group (survey Corollary 2.4). Chatterji--Kassabov even
  give Kazhdan hosts. The new part claimed here is an *explicit* group, the Steinberg group
  of a named finitely presented ring.
- **Folklore input.** With a Leavitt pair, `M_n(S) ≅ S` (Leavitt 1962), so `GL_n(Q) ≤ S^x`
  for all `n`. The addition here is lifting this to the finitely presented group
  `St_4(S)` by killing `K_2`.
- **Problem 2.7.** Mikaelian (arXiv:2507.04347) announces an explicit finitely presented
  2-generator overgroup for each `n`, construction not seen. Do not call this the first
  explicit answer. Whether `St_4(D)` is "natural" in the survey's sense is for experts.
- **Nearest unstable-over-Leavitt result:** Khanh arXiv:2609.08428, Theorem 5.4
  (`St_r = GL_r` over `L_(F_2)(1,2)`, `r >= 3`).
- **Rests on** `finitely-presented-divisible-ring-engine`, which has not been independently
  reviewed.

## Attempts

1. **Proof claimed (lane `gq-deep-free-1`), not independently reviewed.**

   *Conventions.* `Q` is central in `S`, since the inverse of a central unit is central.
   From the Leavitt pair one gets Cuntz families of every size `m`:
   `t_k = x_2^(k-1) x_1` for `k < m` and `t_m = x_2^(m-1)`, with partners
   `t_k^* = y_1 y_2^(k-1)`, `t_m^* = y_2^(m-1)`; telescoping gives `Σ t_k t_k^* = 1`.
   The `e_ij = t_i t_j^*` are matrix units commuting with `Q`, so `ι_m` is a unital ring
   map, and it is injective: `t_k^* ι_m(a) t_l = a_kl`.
   For a ring `A`, `St_r(A)` has generators `x_ij(a)` and the Steinberg relations;
   `π : St_r(A) -> E_r(A)`, `K_2(r,A) = ker π`.

   **(a) Block isomorphism over a field.** For `k >= 1` the block map
   `β_k : St_4(M_k(Q)) -> St_(4k)(Q)`, `x_ij(a) -> ∏_(s,t) x_((i,s),(j,t))(a_st)`, is a
   homomorphism (the factors commute; commutators of factors are central in the
   product, which gives the relation `[x_ij(a), x_jl(b)] = x_il(ab)`). It covers the
   identification `E_4(M_k(Q)) = E_(4k)(Q) = SL_(4k)(Q)`. `β_1` is the identity. For `k >= 2`
   it is an isomorphism:
   - `St_4(M_k(Q))` is perfect (`x_ij(a) = [x_il(a), x_lj(1)]`), and `K_2(4, M_k(Q))` is
     central. Cited: Voronetsky, *Centrality of K_2-functor revisited*, arXiv:2004.08551,
     introduction: "From surjective stability for K_2 (see [2]) it follows that K_2(n, A)
     is central if n ≥ sr(A) + 2", with `sr(M_k(Q)) = 1` (Vaserstein 1971,
     `sr(M_k(R)) <= ⌈(sr(R)-1)/k⌉ + 1`) and `n = 4 >= 3`.
   - `St_(4k)(Q)` is the universal central extension of `SL_(4k)(Q)` (`4k >= 8`): it is
     perfect, `K_2(4k, Q)` is central (same citation), and `St_n(A)` is centrally closed
     for `n >= 5` (Kervaire 1970; also quoted in arXiv:2004.08551).
   - So there is `μ : St_(4k)(Q) -> St_4(M_k(Q))` over `SL_(4k)(Q)`. Then `β_k μ = id` by
     universality, and `μ β_k = id` because an endomorphism of a perfect central extension
     over the identity is the identity.

   **(b) Scalar blocks multiply K_2 by N.** Let `j_N : M_m(Q) -> M_(mN)(Q)`,
   `a -> a ⊗ I_N`. On generators, `β_(mN) ∘ St_4(j_N) = b_N ∘ β_m`, where
   `b_N : St_(4m)(Q) -> St_(4mN)(Q)`, `x_((i,s),(j,t))(q) -> ∏_c x_((i,s,c),(j,t,c))(q)`
   (both send `x_ij(a)` to `∏_(s,t,c) x_((i,s,c),(j,t,c))(a_st)`). Let `ŝ_c` be the `N`
   disjoint index embeddings `[4m] -> [4mN]`. For `y ∈ K_2(4m, Q)`, `b_N(y) = ∏_c ŝ_c(y)`:
   `b_N` is a homomorphism and the factors have disjoint indices, so they commute. For a
   field `F` and `n >= 3`, `K_2(n, F)` is generated by the Steinberg symbols
   `{u,v} = [h_ij(u), h_ik(v)]`, which are central and independent of the distinct indices
   `i, j, k` used (Matsumoto 1969; Milnor, *Introduction to algebraic K-theory*, §§9, 12).
   Each `ŝ_c` sends a symbol to the same symbol of `St_(4mN)(Q)`, so `ŝ_c(y) = ŝ_1(y)` for
   every `c`, and `b_N(y) = ŝ_1(y)^N = ŝ_1(y^N)`.

   **(c) K_2(4m, Q) is torsion.** `K_2(4m, Q) -> K_2(Q)` is injective, since for a field
   `F` the unstable `K_2(n, F)` is `K_2(F)` for `n >= 3` (Matsumoto 1969). Also `K_2(Q)` is
   torsion, `Z/2 ⊕ ⊕_(p odd) F_p^x` (Tate).

   **(d) The kernel dies in S.** Let `x ∈ K_2(4, M_m(Q))`. Let `N` be the order of
   `β_m(x)` in `K_2(4m, Q)`, finite by (a) and (c). Pick a Cuntz family `u_1..u_N` in `S`.
   Then `t'_(i,c) = t_i u_c` is a Cuntz family of size `mN` with
   `ι_(mN)(a ⊗ I_N) = Σ a_ij t_i (Σ_c u_c u_c^*) t_j^* = ι_m(a)`, so
   `ι_m = ι_(mN) ∘ j_N`. By (b), `β_(mN)(St_4(j_N)(x)) = ŝ_1(β_m(x)^N) = 1`, and `β_(mN)`
   is injective by (a) (for `mN >= 2`; if `mN = 1` then `N = 1` and `x = 1`). So
   `St_4(j_N)(x) = 1`, and `St_4(ι_m)(x) = St_4(ι_(mN))(1) = 1`.

   **(e) Conclusion.** `ker St_4(ι_m) ⊇ K_2(4, M_m(Q))` by (d). Conversely
   `π ∘ St_4(ι_m) = E_4(ι_m) ∘ π` and `E_4(ι_m)` is injective (`ι_m` is), so
   `ker St_4(ι_m) ⊆ K_2(4, M_m(Q))`. The image is
   `St_4(M_m(Q)) / K_2(4, M_m(Q)) = E_4(M_m(Q)) = SL_(4m)(Q)`, generated by the
   elementary transvections in the off-diagonal blocks.

   *Where it could fail (for the referees):* the two cited centrality facts in (a),
   stated here from Voronetsky's introduction (primary text of [2] not read); the
   Matsumoto inputs in (b) and (c), cited from memory, not re-read at source; and the
   bookkeeping identity `β_(mN) ∘ St_4(j_N) = b_N ∘ β_m`.

2. **Relation to `leavitt-pairs-embed-sl-n-q-in-steinberg-groups`.** That node's proof
   is self-contained, using a room lemma and a square swap in `St_(6N+1)(S)`, and needs
   no citations. This proof needs the classical K_2 of matrix rings over `Q` but gives one
   fixed rank. Either proof, once refereed, answers `gl-n-q-explicit-natural-fp-overgroup`.
   This one gives a single `Γ = St_4(D)` for all `n`. By
   `steinberg-finite-presentation-and-kazhdan-theorem`, `Γ` also has property (T).
