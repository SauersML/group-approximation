---
rg: 2
id: amenable-edge-assemblies-delta2-sofic-locus-proof
kind: route
title: Normalising degenerate graph-of-groups assemblies with a 0-prime oracle and max-n on the edges
target: amenable-edge-assemblies-have-delta2-sofic-locus
requires: []
---

Notation is as in [[amenable-edge-assemblies-have-delta2-sofic-locus]].  Facts used:

- (F1) **Bass-Serre.**  In the fundamental group of a graph of groups whose edge maps are injective (a
  *genuine* graph of groups), every vertex group and every edge group embeds.  (Serre, *Trees*, I.5.)
- (F2) **Soficity permanence.**
  - Subgroups of sofic groups are sofic.
  - The fundamental group of a finite graph of groups with sofic vertex groups and amenable edge groups is
    sofic.  References: Elek-Szabo (Proc. AMS 139 (2011)) and Paunescu (J. Funct. Anal. 261 (2011)) for
    amalgams; Collins-Dykema (Münster J. Math. 4 (2011)) for HNN extensions; Ciobanu-Holt-Rees (Pacific J.
    Math. 271 (2014), arXiv:1212.2739) for finite graphs of groups.
- (F3) **Post / limit lemma.**  `A <=_T 0'` iff `A` is `Delta^0_2`.  `INF = {i : W_i infinite}` is
  `Pi^0_2`-complete, hence not `Sigma^0_2`, hence not `Delta^0_2`.  (Soare, *Recursively enumerable sets and
  degrees*, IV.3.2 and III.)
- (F4) **Edge classes.**
  - Finitely generated abelian groups: Noetherian, with uniform word problems for quotients by Smith normal
    form.
  - Polycyclic-by-finite groups: max-n, since every subgroup is finitely generated.  Uniform algorithms:
    Baumslag-Cannonito-Robinson-Segal, J. Algebra 142 (1991).
  - Finitely generated metabelian groups: max-n by P. Hall (Proc. LMS 4 (1954)); they are finitely presented
    in the variety `A^2`, so `E/<<S>>` is again such a group, given effectively.  Uniform word problem:
    Baumslag-Cannonito-Robinson, Proc. Royal Soc. Edinburgh 124A (1994).
  - All three classes are amenable (elementary amenable).

Two conventions:
- For an edge `eps` with ends `o = o(eps)` and `t = t(eps)`, write `pi_v : V_v -> P_e` for the canonical map.
- The two composites `E_eps -> P_e`, namely `pi_o iota_(eps,o)` and `pi_t iota_(eps,t)`, differ by
  conjugation by `tau_eps`.  So they have the **same** kernel `N_eps`.

For finite (or arbitrary) normal subgroups `M_eps ⊴ E_eps`, write
`V^M_v = V_v / <<iota_(eps,*)(M_eps) : eps incident to v, both ends>>` and let `G^M` be the fundamental group
of the graph of groups with vertex groups `V^M_v`, edge groups `E_eps/M_eps` and the induced edge maps.

## Lemma 1 (quotient invariance)

If `M_eps ⊆ N_eps` for every `eps`, then the obvious map `P_e -> G^M` is an isomorphism.

*Proof.*
- A presentation of `G^M` is the presentation of `P_e` with the extra relators `iota_(eps,o)(m)` and
  `iota_(eps,t)(m)` for `m in M_eps`.
- The relations of `E_eps/M_eps` do not add anything else: the edge relations are imposed on generator
  images only.
- Each extra relator already holds in `P_e`, because `m in N_eps` and both composites have kernel `N_eps`.
- So the added relators are trivial and the two presentations define the same group.  ∎

## Lemma 2 (genuineness criterion)

Let `M_eps ⊆ N_eps` for all `eps`.  The following are equivalent:
- (i) `M_eps = N_eps` for every `eps`;
- (ii) every induced map `E_eps/M_eps -> V^M_v` (both ends) is injective.

*Proof.*
- **(i) ⇒ (ii).**  Let `x in E_eps` with `iota_(eps,o)(x) = 1` in `V^M_o`.  Since `M ⊆ N`, the map `pi_o`
  factors through `V^M_o`.  So `x` dies in `P_e`, that is `x in N_eps = M_eps`.  The end `t` is the same.
- **(ii) ⇒ (i).**
  - By (ii) the graph of groups defining `G^M` is genuine.
  - By (F1), `E_eps/M_eps` embeds in `G^M`.
  - By Lemma 1, `G^M = P_e`, and the embedding is the map induced by `E_eps -> P_e`.
  - Hence `ker(E_eps -> P_e) = M_eps`, so `N_eps = M_eps`.  ∎

## Proof of (A)

Take `M = N`.
- By Lemma 2 the graph of groups with vertex groups `V*_v = V^N_v` and edge groups `E_eps/N_eps` is genuine.
- By Lemma 1 its fundamental group is `P_e`.
- By (F1), `V*_v` embeds in `P_e`.  Its image is `pi_v(V_v)`, since `V_v -> V*_v` is onto.
- **Soficity.**
  - If `P_e` is sofic, every subgroup `V*_v` is sofic (F2).
  - Conversely, the edge groups `E_eps/N_eps` are quotients of amenable groups, hence amenable.  If all
    `V*_v` are sofic, then `P_e` is sofic by (F2).
- Lemma 1, Lemma 2 and the first two clauses use no hypothesis on the edge groups.  Only the soficity clause
  uses amenability.  ∎

## Proof of (B)

Assume every `E_eps` lies in a Noetherian decidable class.  Run the following algorithm with oracle `0'`.

1. **Start** with `S_eps = ∅` for every edge.
2. **Ask `0'`** the question `Q(S)`: do there exist an edge `eps`, an end `v` of `eps` and a word `u` in the
   generators of `E_eps` such that
   - `u ∉ <<S_eps>>` in `E_eps`, and
   - `iota_(eps,v)(u) = 1` in `V^S_v`?
3. **If the answer is yes**, search for such a triple and put `u` into `S_eps`.  Go to step 2.
4. **If the answer is no**, output `(S_eps)`.

**Q(S) is Sigma^0_1, uniformly in `e` and `S`.**
- The first condition is decidable by (N2).
- `V^S_v` has the finite presentation of `V_v` together with the finite set `iota(S)`, so its word problem is
  r.e.
- An existential quantifier over a decidable relation and an r.e. relation is `Sigma^0_1`.
- So `0'` answers `Q(S)`.  When the answer is yes, the search in step 3 terminates, by dovetailing the r.e.
  enumeration of relations of `V^S_v`.

**Invariant: `<<S_eps>> ⊆ N_eps` for every `eps`.**  By induction on the number of steps.
- It holds for `S = ∅`.
- Suppose it holds, and `u` is added with `iota_(eps,v)(u) = 1` in `V^S_v`.
- By the invariant, `pi_v` factors through `V^S_v`.  So `u` dies in `P_e`, that is `u in N_eps`.

**Termination.**
- Each yes-step strictly enlarges one of the normal subgroups `<<S_eps>> ⊴ E_eps`, since `u ∉ <<S_eps>>`.
- There are finitely many edges, and each `E_eps` satisfies max-n, the ascending chain condition on normal
  subgroups (N1).
- So only finitely many yes-steps occur.

**Correctness.**
- At halt, `Q(S)` is false.  That says exactly that every induced map `E_eps/<<S_eps>> -> V^S_v` is injective.
- By Lemma 2, `<<S_eps>> = N_eps`.  So `V*_v = V^S_v`, whose finite presentation the algorithm outputs.  ∎

*Remark.*  Max-n alone does not give a computable bound on the number of steps.  This is why the oracle is
`0'` and not a bounded number of queries, and why (C) gives `Delta^0_2` rather than a finite difference level.
(D) recovers a computable bound when the edge kernels are tame.

## Proof of (C)

- **The locus is `0'`-computable.**  On input `e`:
  - run (B) to get `S` with `V*_v = V^S_v`;
  - use hypothesis (V) to decide from `0'` whether every `V^S_v` is sofic.  (V) is applied only to the final
    `S`, which has `<<S_eps>> = N_eps`;
  - by (A) that is whether `P_e` is sofic.
  So `L <=_T 0'`, and `L` is `Delta^0_2` by (F3).
- **No reduction of `INF`.**
  - Suppose a computable `f` has `i in INF` iff `P_(f(i))` is sofic, and the family `(A_(f(i)))` satisfies
    the hypotheses.
  - Then `INF <=_m L`, so `INF` is `Delta^0_2`.  That contradicts (F3).
  - The same argument works for every `Pi^0_2`-complete set, and for Turing reductions as well.  ∎

## Proof of (D)

Assume each `E_eps` is generated by an element `x_eps` and is tame: `N_eps in {1, E_eps}`.

- **The kill set.**  Put `K_e = {eps : N_eps = E_eps} = {eps : x_eps = 1 in P_e}`.
  - `K_e` is a subset of the finite edge set, of size `k_e`, computable from `e`.
  - Membership is `Sigma^0_1`, uniformly, because `P_e` is finitely presented.
  - Let `K^s` be the set of edges `eps` for which a proof of `x_eps = 1` appears by stage `s`.  Then `K^s` is
    increasing, `K^s = K_e` for large `s`, and it changes at most `k_e` times.
- **Soficity from the kill set.**  By tameness, `N_eps = <<x_eps>>` for `eps in K_e` and `N_eps = 1`
  otherwise.  By (A),
  `P_e` is sofic iff `tau(e, v, K_e)` holds for every vertex `v`, where `tau(e, v, K)` means that
  `V_v/<<iota(E_eps) : eps in K>>` is sofic.
- **The approximation.**
  - By hypothesis there are computable functions `tau_s(e, v, K)` and `b(e, v, K)`, defined for every subset
    `K` of the edges.  For each `K`, `tau_s(e, v, K)` changes at most `b(e, v, K)` times in `s`, and its limit
    is `tau(e, v, K)` whenever `K ⊆ K_e`.  Only subsets of `K_e` are ever needed, because `K^s ⊆ K_e`.  Every
    relator added for `K ⊆ K_e` already dies in `P_e`.
  - Put `L_s(e) = AND_v tau_s(e, v, K^s)`.
- **Convergence.**  For large `s`, `K^s = K_e` and each `tau_s(e, v, K_e)` has settled, so `L_s(e) -> [e in L]`.
- **Change bound.**  Consider a stage where `L_s(e)` changes.
  - Either `K^s` changes, which happens at most `k_e` times;
  - or, for the current `K = K^s`, some `tau_s(e, v, K)` changes, which happens at most `b(e, v, K)` times in
    total for each pair `(v, K)`.
  - So the number of changes is at most `k_e + SUM_(K ⊆ edges) SUM_v b(e, v, K)`.  This bound is computable
    from `e`, because there are `2^(k_e)` subsets.
- **Conclusion.**  `L` is omega-c.e. with a computable change bound.
- **Sharpness.**  [[sofic-fp-hard-for-every-finite-difference-level]] shows that every omega-c.e. set with a
  computable change bound many-one reduces to `NONSOFIC_fp`.  It does so by assemblies of this tame cyclic
  kind.
  - The kill and collapse gadgets there have edge groups `Z` or `1`.
  - Each `Z` edge is either genuine (`w != 1`) or killed outright (`w = 1`).
  So inside the calculus the lower bound and the ceiling coincide at the bounded-change level, and the
  hypothesis of (D) is the only extra input.  ∎

## Nests

In a nested assembly, a vertex group `V_v` is itself the output `P_(e')` of an inner assembly.  Suppose every
edge word `iota_(eps,v)(x)` is conjugate into a vertex group `V_w` of the inner assembly.
- Then `V_v / <<iota(S)>>` is presented by adding finitely many relators supported in vertex groups `V_w`.
- That is the presentation of the inner assembly with `V_w` replaced by `V_w/<<...>>`.
- So hypothesis (V) for the outer level follows from (B) and (C) applied to the modified inner assemblies,
  provided the inner edges are Noetherian decidable and the base vertex groups satisfy (V).
- By induction, nests of any computable finite depth stay `Delta^0_2`.

The finite nest depth matters.  A computable family whose nest depth is unbounded in `e` is still covered, as
long as the depth is computable from `e`.  The recursion is uniform.

## Where the argument would fail, and why each escape is genuine

The four escapes listed in the claim are exactly the hypotheses used.
- **Amenability of the edges** is used only in the last clause of (A).  Without it, soficity of `P_e` is not
  determined by the vertex groups.
- **(N1) max-n** is used only for termination in (B).
- **(N2)** is used only to make `Q(S)` a `Sigma^0_1` question.  If `E_eps` has an undecidable word problem,
  as for the Kharlampovich-Myasnikov-Sapir `A_p^2 A` machine groups, then "`u ∉ <<S_eps>>`" is `Pi^0_1`.
  - `Q(S)` becomes `Sigma^0_2`, so `0'` can no longer run the normalisation.
  - Whether such an edge also violates max-n is not needed for the obstruction to lapse.
- **Hypothesis (V)** is used only in (C).
- **Colimits.**  The algorithm only uses that `P_e` is a finite graph-of-groups colimit.  Constructions that
  are not colimits, such as lamp modules and wreath-type amplifiers, fall outside it.

**Calibration on known cases.**
- **All vertex groups amenable.**  Then (A) gives `L = all e`, trivially `Delta^0_2`.  This matches the fact
  that amenable-edge graphs of amenable groups are sofic.
- **The seed-release gadgets of the finite-difference node.**  They are tame cyclic assemblies.  (D)
  reproduces their omega-c.e. ceiling, and their lower bound shows (D) cannot be improved.
- **The Higman rope `K_e *_(L_e) (L_e x Z)`.**  Its edge `L_e` is non-amenable.  (A) fails and no
  `Delta^0_2` bound is claimed.  That rope is the only landed compiler that could reach `Pi^0_2`, consistent
  with the escape list.
