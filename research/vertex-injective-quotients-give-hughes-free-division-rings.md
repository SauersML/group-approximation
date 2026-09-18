---
rg: 2
id: vertex-injective-quotients-give-hughes-free-division-rings
kind: claim
title: A graph of groups is hereditarily Hughes-free embeddable exactly when it maps to such a group injectively on vertex groups, so q:HF holds for free products and retract trees in every characteristic
distinct_from:
  fsp-q-hf-reduces-to-hyperbolic-kernel-pairs: that settles q:HF for pairs with locally elliptic kernel inside the coproduct field, and leaves the hyperbolic-kernel pairs open; this settles every pair, hyperbolic kernels included, for each graph of groups with a vertex-injective map to a hereditarily HFE group, by producing the Hughes-free field first and identifying it with the coproduct field afterwards.
  fsp-graph-of-rings-and-linnell-extension-imports: that imports the embedding of a graph of Hughes-free vertex rings into a division ring; this shows that for the graphs of groups above that division ring is Hughes-free.
  universal-division-rings-do-not-iterate-over-graphs-of-groups: that shows universality does not iterate over graphs of groups and identifies the Linnell iteration with q:HF; this answers q:HF positively on an explicit class, without any universality statement.
  higman-bs-amalgam-has-hughes-free-division-rings: that gives Hughes-free rings for the BS(1,2) amalgams inside Higman's group; this is a general closure theorem, and its free-product and fold cases do not need Baumslag-Solitar vertex groups.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this adds no case of it or of its division-ring embedding form for one-relator groups, since H consists of locally indicable groups (Higman, Burns-Hale; Lewin-Lewin for one-relator groups), and it enlarges only the class with Hughes-free division rings in positive characteristic and for crossed products.
---

**ESTABLISHED** (new class and strict reduction) by [[vertex-injective-quotients-give-hughes-free-division-rings-proof]].

**Setting.** `k` and `E` are arbitrary division rings, in any characteristic. "HFE" is as in
[[hughes-extension-lemma-and-fsp-universal-field-imports]]: every crossed product `E * Γ` over every division
ring has a Hughes-free division ring. Let `𝓗` be the class of groups all of whose subgroups are HFE
(*hereditarily HFE*).

**Theorem.**
1. **The class.** `𝓗` is closed under subgroups, extensions and directed unions. It contains every free group,
   every locally indicable amenable group, every bi-orderable group, every residually torsion-free nilpotent
   group and every free-by-cyclic group.
2. **Vertex-injective criterion.** Let `G` be the fundamental group of a graph of groups `(G_v, G_e; Γ)`. Then
   `G ∈ 𝓗` if and only if there is a homomorphism `φ: G -> Q` with `Q ∈ 𝓗` that is injective on every vertex
   group. The kernel of such a `φ` is free, and `G` is free-by-`φ(G)`.
3. **Amalgams and HNN extensions as embedding problems.**
   - `A *_C B ∈ 𝓗` if and only if `A` and `B` embed in a common group of `𝓗` by embeddings that agree on `C`.
   - `B *_θ ∈ 𝓗`, for `θ: A -> C` an isomorphism of subgroups of `B`, if and only if `B` embeds in some
     `Q ∈ 𝓗` in which `θ` is conjugation by an element of `Q`.
4. **Free products.** If `A, B ∈ 𝓗`, then `A * B ∈ 𝓗`. This works in every characteristic: the kernel of
   `A * B -> A × B` is free.
5. **Folds.** `A *_C A` (the double), and `A *_C B` with `C ≤ B ≤ A`, lie in `𝓗` when `A ∈ 𝓗`.
6. **Retract trees.** Let `𝒯` be a tree of groups with every vertex group in `𝓗`. Orient `𝒯` toward a vertex,
   or toward an end. Suppose every vertex group except the root retracts onto the edge group of its outgoing
   edge. Then `π_1(𝒯) ∈ 𝓗`. In particular, if `B ∈ 𝓗` retracts onto `A` or onto `C = θ(A)`, then
   `B *_θ ∈ 𝓗`.
7. **Consequences for q:HF and the compatibility statement.** Let `G ∈ 𝓗` split as a graph of groups. Then, for
   every crossed product `k * G`:
   - `D_{k*G}` exists;
   - FSP's embedding into `U(DG_Γ)` is Hughes-free, for every splitting;
   - for every subgroup `N ≤ G`, in particular every normal subgroup `N ⊴ H ≤ G` with `N` containing a
     hyperbolic element, the division closure of `k*N` in `U(DG_Γ)` is `k*N`-isomorphic to the universal field
     of the graph of rings that `N` inherits from any action on a subtree. This includes the minimal subtree
     `T_H`.

   This is the compatibility statement of [[fsp-q-hf-reduces-to-hyperbolic-kernel-pairs]], for every pair of
   such a `G`.

**The brief's test case.** Free products (`C = 1`) in characteristic `p` are settled positively by item 4. If
`A, B ∈ 𝓗`, then `U(D_{kA} *_k D_{kB})` is the Hughes-free division ring of `k[A * B]`. Its hyperbolic-kernel
pairs satisfy the Hughes condition.

**What is new.** The Cohn-coproduct route of `fsp-q-hf-reduces-to-hyperbolic-kernel-pairs` works inside `U` and
stalls on hyperbolic kernels. This theorem does not look inside `U`. It builds the Hughes-free field by Hughes'
extension lemma over the free kernel of a vertex-injective map, and then identifies it with `U` through FSP
Lemma 7.6. The ring-theoretic question for these splittings becomes a purely group-theoretic embedding problem
(item 3). I have not found items 2–6 stated in the literature. Item 4 in particular may be folklore; I have not
confirmed either way.

**Where it stops.** Item 2 is an equivalence, so nothing is lost for membership in `𝓗`. But it gives nothing when
no vertex-injective map to `𝓗` is known.
- The retract condition in item 6 fails for general Magnus hierarchies of one-relator groups, whose edge groups
  are Magnus subgroups that need not be retracts.
- A bi-infinite line cannot, in general, be handled by a single solvable target. In the Baumslag–Gersten kernel,
  every vertex generator lies in every derived subgroup (see [[baumslag-gersten-group-is-hughes-free-embeddable]]).
  So directed unions of finite segments are essential.
- Whether `𝓗` equals the class of HFE groups (that is, whether HFE passes to subgroups) is not settled here.
