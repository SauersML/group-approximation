# Tight routes, compact limits and treeability: a gate for Bernoulli cost compactness

Lane b-p-fp4 (swarm-0917), transplanter via stability-approximation, 2026-09-17.
Target hole: `fpbs-bernoulli-cycle-tail-compactness`.

## 0. What this note does

The target hole asks for near-minimizing graphings of the Bernoulli action whose finite-cycle
dimension is "compact" in the length scale. The most natural way to get compactness is the
stability paradigm: near-minimizers should be close to an exact minimizer, obtained as a limit.
This note makes that paradigm exact and shows where it dies.

* **Theorem A (gate).** For an infinite finitely generated group, the Bernoulli action has a
  near-minimizing sequence of graphings with uniformly tight routes and labels if and only if it
  is weakly equivalent to a free treeable action. Either condition implies Fixed Price for the
  group.
* **Corollary B (obstruction).** For every non-treeable group (every infinite Kazhdan group, and
  every nonamenable group admitting a free action of cost one) no near-minimizing sequence of any
  free action has uniformly tight routes and labels. Every compactness or stability argument that
  passes near-minimizers to a weak limit and keeps generation dies at the generation step. The
  invariant that kills it is treeability.

Theorem A generalizes the cost-one Cayley-subgraph statement `fpbs-cost-one-routes-cannot-be-uniformly-tight`
(percolation note, Section 7, Proposition 5). That statement covers invariant random spanning subgraphs of one
Cayley graph with mean degree tending to two. Theorem A covers arbitrary graphings, which may use infinitely many
group labels, at every cost level. It also proves the converse direction, and it ends in Fixed Price rather than in
amenability.

## 1. Conventions and imports

Γ is an infinite group with finite symmetric generating set S. Actions are left actions.
b is the Bernoulli shift of Γ on X=[0,1]^Γ with μ=λ^Γ, λ Lebesgue. It is essentially free.
By Abért–Weiss Theorem 1 all free factors of i.i.d. processes are weakly equivalent. So by cost
constancy (import 3) the choice of base does not affect any statement below.

A graphing Φ of a free action a on (Z,ρ) that generates a subrelation of R_a is, by freeness,
the same thing as a family of Borel sets A_g ⊂ Z (g∈Γ∖{e}): an unordered edge {z,gz} is present
iff z∈A_g. Symmetry means g A_g = A_{g^{-1}}. The label of the edge from z to gz is g. Cost is

    c(Φ) = (1/2) ∫ deg_Φ dρ = (1/2) Σ_g ρ(A_g).

Choose one element from each pair {g,g^{-1}} with g≠g^{-1}. For an involution g, choose a Borel set T_g with
T_g ⊔ gT_g = A_g, which exists because g acts freely on A_g. The restrictions of g to these sets are then a
graphing in Gaboriau's sense (a family of partial isomorphisms), with total domain measure c(Φ) and the same
unoriented edges. So c(Φ) is Gaboriau's cost C(Φ), and "treeing" has the same meaning on both sides.

Imports. The verbatim text is recorded in the citation nodes named here.

1. **Weak containment.** Abért–Weiss, arXiv:1103.1063v2, §1 (definition following Kechris): "we say that f weakly
   contains g (f⪰g) if for all Borel subsets Y₁,…,Yₙ∈𝒞, finite sets S⊆Γ and ε>0 there exist Borel subsets
   X₁,…,Xₙ∈ℬ such that |μ(fᵧXᵢ∩Xⱼ)−ν(gᵧYᵢ∩Yⱼ)|<ε (1≤i,j≤n,γ∈S)." Write g ≺ f.
2. **Abért–Weiss Theorem 1** (`abert-weiss-free-actions-weakly-contain-bernoulli`): every free p.m.p. action weakly
   contains every Bernoulli action.
3. **Kechris monotonicity** (`cost-is-constant-on-weak-equivalence-classes`): for Γ finitely generated and free
   actions, b ≺ a implies C(a) ≤ C(b).
4. **Bernoulli is maximal** (`fpbs-bernoulli-maximal-cost`): C(b) = C^*(Γ) = sup over free actions, and C(b) ≤ |S|/2 < ∞.
5. **Gaboriau, lecture notes (3 Oct 2025), Proposition 2.23**: "If Φ is a graphing of a p.m.p. equivalence relation
   R such that C(Φ)=C(R)<∞, then Φ is a treeing." (`gaboriau-attained-finite-cost-graphing-is-treeing`)
6. **Gaboriau, lecture notes, Theorem 2.24**: "If Ψ is a treeing of a p.m.p. equivalence relation R then C(Ψ)=C(R)."
   **Corollary 2.26**: "If Γ admits a free p.m.p. treeable action, then this action realizes the infimum C∗(Γ)."
   (`gaboriau-treeable-free-action-realizes-min-cost`)
7. **Gaboriau, lecture notes, Theorem 2.22 [Adams–Spatzier]**: "Infinite groups with Kazhdan property (T) do not
   admit any treeable free action." Also the second sentence of Corollary 2.26: "if a non-amenable Γ admits a
   cost=1 free p.m.p. action, then Γ is non treeable." These are used only in Corollary B.
   (`kazhdan-groups-admit-no-treeable-free-action`; the second sentence is in import 6's node.)

## 2. Definitions

Let Φ_n be graphings generating R_b, with label sets A^n_g, and c(Φ_n) → C(b). A *route* for s∈S at x is a
Φ_n-path x=x_0,x_1,…,x_m=sx. Its *pattern* is the label word (g_1,…,g_m) with x_i=g_i x_{i-1} and
g_m⋯g_1 = s.

**(T) Uniform route-and-label tightness.** For every η>0 there are an integer M and a finite set F⊂Γ such that for
every n and every s∈S,

    μ{ x : some route for s at x in Φ_n has length ≤ M and all labels in F } ≥ 1−η.

For graphings drawn inside one Cayley graph, labels lie in S automatically and (T) is tightness of route length.
That is the hypothesis of `fpbs-cost-one-routes-cannot-be-uniformly-tight`.

## 3. Theorem A

**Theorem A.** Let Γ be an infinite finitely generated group and b its Bernoulli action. The following are equivalent.

(i) Some near-minimizing sequence of graphings of b satisfies (T).

(ii) There is a free p.m.p. action a' of Γ with a' ≺ b and a graphing Ψ generating R_{a'} with c(Ψ) = C(a') = C(b).

(iii) b is weakly equivalent to a free treeable action of Γ.

Moreover, under these conditions every free action of Γ has cost C(b), so Γ has fixed price.

### 3.1 (i) ⇒ (ii): compact limit

*Step 1: factor codings.* Put Y = [0,1]^Γ × {0,1}^{Γ×Γ}, a compact metrizable space with the continuous Γ-action

    (h·(u,ω))(γ) = u(γh),   (h·ω)(γ,g) = ω(γh,g).

Define π_n: X → Y by π_n(x) = (u,ω) with u(γ)=ξ(γx) and ω(γ,g)=1[γx∈A^n_g], where ξ(x)=x(e) is the base
coordinate. Then π_n(hx) = h·π_n(x): writing π_n(hx)=(u',ω'), we get u'(γ)=ξ(γhx)=u(γh), and likewise
ω'(γ,g)=1[γhx∈A^n_g]=ω(γh,g). Hence ν_n = (π_n)_*μ is Γ-invariant and π_n is a factor map
from b onto (Y,ν_n). The [0,1]^Γ-marginal of ν_n is the law of (ξ(γx))_γ. This law is the Bernoulli measure λ^Γ,
up to the fixed relabelling γ↦γ^{-1} of coordinates, and it does not depend on n.

*Step 2: the limit.* By compactness pass to a subsequence with ν_n → ν weak*. Then ν is Γ-invariant and its
[0,1]^Γ-marginal is still the Bernoulli measure. So a' := (Y,ν) has a free Bernoulli factor and is free.

*Step 3: a' ≺ b.* Let 𝒜 be the algebra of finite Boolean combinations of cylinder sets
{u(γ)<t}, {u(γ)≤t} with t outside the countable set of atoms of the marginals of ν, and {ω(γ,g)=1}. Their
boundaries are ν-null, so every C∈𝒜 is a ν-continuity set. So is hC∩C' for h∈Γ and C,C'∈𝒜, since h acts by
homeomorphisms preserving ν. The algebra 𝒜 generates the Borel σ-algebra of Y, so it is dense in the measure
algebra of ν.

Given Borel Y_1,…,Y_k ⊂ Y, finite K⊂Γ and ε>0, choose C_i∈𝒜 with ν(Y_iΔC_i)<ε/8. Then
|ν(hY_i∩Y_j)−ν(hC_i∩C_j)|<ε/4. By the portmanteau theorem, ν_n(hC_i∩C_j)→ν(hC_i∩C_j). Take n large and
X_i := π_n^{-1}(C_i). Equivariance gives μ(hX_i∩X_j)=ν_n(hC_i∩C_j). So
|μ(hX_i∩X_j) − ν(hY_i∩Y_j)| < ε for all i,j and h∈K. This is import 1, so a' ≺ b.

*Step 4: the limit graphing.* Let D_g = {ω(e,g)=1}, which is clopen. Then (h·ω)(e,g)=ω(h,g) gives
h^{-1}D_g = {ω(h,g)=1}. Let Ψ be the graphing of a' with label sets D_g. The symmetry
gA^n_g = A^n_{g^{-1}} says ω(γ,g)=ω(gγ,g^{-1}) ν_n-a.s. This is a closed condition on finitely many
coordinates for each (γ,g), so it holds ν-a.s. and Ψ is a symmetric graphing. Its edges join y to gy, so Ψ
generates a subrelation of R_{a'}. By weak* convergence on clopen sets and Fatou's lemma for series,

    c(Ψ) = (1/2) Σ_g ν(D_g) = (1/2) Σ_g lim_n μ(A^n_g) ≤ liminf_n c(Φ_n) = C(b) < ∞.

In particular deg_Ψ is integrable, so Ψ is locally finite a.e.

*Step 5: generation.* Fix s∈S and η>0, and take M,F from (T). For a pattern w=(g_1,…,g_m) with m≤M, g_i∈F and
g_m⋯g_1=s, let γ_i=g_i⋯g_1 (γ_0=e). The event that w is a route at the root is

    E_w = ∩_{i=1}^m {ω(γ_{i-1},g_i)=1}.

Under π_n this is exactly the event that w is a Φ_n-route for s at x. It is clopen and there are finitely many
such w. So ν(∪_w E_w) = lim ν_n(∪_w E_w) ≥ 1−η, and on E_w the point y is Ψ-connected to sy. Letting η→0, ν-a.e.
y is Ψ-connected to sy for every s∈S. The set G_s of such y has full measure and so does each translate hG_s. So for
a.e. y and every word s_k⋯s_1, the points y, s_1y, s_2s_1y, … are successively Ψ-connected. Thus Ψ generates R_{a'}.

*Step 6: attainment.* By import 2, b ≺ a', so import 3 gives C(a') ≤ C(b). Step 3 and import 3 give
C(b) ≤ C(a'). Hence C(a')=C(b), and C(a') ≤ c(Ψ) ≤ C(b) = C(a'), so c(Ψ)=C(a')=C(b). This is (ii).

### 3.2 (ii) ⇒ (iii)

c(Ψ) = C(R_{a'}) < ∞, so by import 5 Ψ is a treeing, and a' is a free treeable action. b ≺ a' by import 2 and
a' ≺ b by hypothesis, so they are weakly equivalent.

### 3.3 (iii) ⇒ fixed price, and (iii) ⇒ (ii)

Let a' be free, treeable, and weakly equivalent to b, with treeing Ψ. Import 3 in both directions gives
C(a')=C(b). Import 6 (Theorem 2.24) gives c(Ψ)=C(a'). Import 6 (Corollary 2.26) gives C(a') = C_*(Γ), the infimum
over free actions. Import 4 gives C(b)=C^*(Γ). So C_*(Γ)=C^*(Γ) and every free action has cost C(b). This proves
the "moreover" clause, and (ii) holds with this Ψ.

### 3.4 (ii) ⇒ (i): transfer a minimizer into b

Let a' on (Y,ν) be free with a' ≺ b and let Ψ (label sets D_g) generate R_{a'} with c(Ψ)=C(b). Take the numbers
η_k = 2^{-k}. Every Ψ-route is finite a.e. and has finitely many labels. So choose increasing M_k and finite
symmetric F_k ⊇ S, nested in k and not containing e, such that for each s∈S the Ψ-route events with length ≤ M_k and labels in F_k have total ν-measure
≥ 1−η_k.

*Construction at stage n.* Let K_n = (F_n∪{e})^{M_n}. Let P_n be the finite partition of Y generated by the sets
γ^{-1}D_g (γ∈K_n, g∈F_n), and let A_1,…,A_p be its atoms. Apply import 1 to the family {A_i} ∪ {D_g : g∈F_n}, the
finite set K_n^{-1}K_n ∪ F_nK_n, and a tolerance ε_n. This gives sets B_i, B_g ⊂ X with all pairwise translate
statistics within ε_n. Let Φ_n^0 be the graphing on X with label sets B'_g = B_g ∩ g^{-1}B_{g^{-1}} (g∈F_n). This
set rule is symmetric. For s∈S let U_{n,s} be the set of x with no Φ_n^0-route for s of length ≤ M_n. Put
Φ_n = Φ_n^0 ∪ {s-edges on U_{n,s}, s∈S}. It generates R_b.

*Cost.* deg_{Φ_n^0} ≤ Σ_{g∈F_n} 1_{B_g}, so

    c(Φ_n) ≤ (1/2)Σ_{g∈F_n} μ(B_g) + Σ_s μ(U_{n,s})
          ≤ (1/2)Σ_{g∈F_n} ν(D_g) + |F_n|ε_n + Σ_s μ(U_{n,s})
          ≤ C(b) + |F_n|ε_n + Σ_s μ(U_{n,s}).

*Routes survive.* Let w be a pattern of level (M_k,F_k) with k ≤ n, and let A_i ⊂ E_w be an atom. Each condition of
E_w says γ_{i-1}y ∈ D_{g_i}, with γ_{i-1}, γ_i=g_iγ_{i-1} ∈ K_n. The corresponding X-condition is
γ_{i-1}x ∈ B_{g_i} ∩ g_i^{-1}B_{g_i^{-1}}, that is, γ_{i-1}x∈B_{g_i} and γ_ix∈B_{g_i^{-1}}. For every γ∈K_n and
g∈F_n with A_i ⊂ γ^{-1}D_g we have

    μ(B_i ∖ γ^{-1}B_g) = μ(B_i) − μ(γB_i∩B_g) ≤ ν(A_i) − ν(γA_i∩D_g) + 2ε_n = 2ε_n.

Here μ(B_i)=μ(B_i∩B_i) is within ε_n of ν(A_i). Also, for i≠j,
μ(B_i∩B_j) ≤ ν(A_i∩A_j)+ε_n = ε_n. By Bonferroni, μ(∪_{A_i⊂∪_wE_w} B_i) ≥ Σ ν(A_i) − pε_n − p²ε_n. For each such
atom fix one pattern w with A_i ⊂ E_w. It has at most M_n edge conditions, hence at most 2M_n set conditions, and
each bad part has measure ≤ 2ε_n. Removing the bad parts, the Φ_n^0-route events of level (M_k,F_k) for s have
μ-measure at least 1−η_k−(2p²+4pM_n)ε_n. This holds simultaneously for all k ≤ n and s∈S. Choose ε_n (after p=p(n)
is known) so small that (2p²+4pM_n)ε_n + |F_n|ε_n ≤ η_n.

For k=n this gives μ(U_{n,s}) ≤ 2η_n, so c(Φ_n) ≤ C(b) + η_n + 2|S|η_n → C(b): the sequence is near-minimizing.
For tightness, let η>0 and pick k with 2η_k<η. For n ≥ k the level (M_k,F_k) route events have measure
≥ 1−2η_k ≥ 1−η. The finitely many Φ_n with n<k are generating graphings, so a larger (M,F) works for them at
level η. Routes on U_{n,s} have length 1 and label s∈F_k. So (T) holds.

This completes Theorem A. ∎

## 4. Corollary B: the obstruction

**Corollary B.** Let Γ be an infinite finitely generated group that admits no free treeable action. Then no
near-minimizing sequence of graphings of any free action a of Γ satisfies (T).

*Proof.* Run §3.1 with a in place of b. Steps 1–5 use only that b is a free action coded by its i.i.d. coordinate.
For a general free action a on (X,μ), code a itself instead of an i.i.d. coordinate. Fix a compact metrizable
model of a, i.e. a compact metrizable space Z with a continuous Γ-action and an invariant measure isomorphic to
(X,μ,a) (such a model exists by Varadarajan's theorem; this is the only extra input, see §6). Put
Y' = Z × {0,1}^{Γ×Γ} and π_n(x) = (x, (1[γx∈A^n_g])_{γ,g}). Steps 3–5 apply
verbatim, and the first marginal of ν is the law of a, so a' is free. Step 6 needs only a' ≺ a and a ≺ a'. The
first holds by Step 3. The second holds because a is a factor of a', since the first marginal is a itself. So
Ψ attains C(a')=C(a), and import 5 makes a' a free treeable action of Γ. Contradiction. ∎

The Bernoulli case, which is all the target needs, uses only §3.1 as written.

*Named members of the killed class.*

* Every infinite Kazhdan group (import 7, Theorem 2.22). By Hutchcroft–Pete (recorded in the notes, Question 2.67)
  these have cost one, and their Fixed Price is open. So any proof of Fixed Price or of the target hole for
  Kazhdan groups must use near-minimizers whose routes or labels escape to infinity with probability bounded away
  from zero.
* Every nonamenable group with a free action of cost one (import 7, Corollary 2.26). Examples are F_2×F_2, groups
  with an infinite normal subgroup of finite cost and infinite quotient (Theorem 2.56 of the notes), and Artin
  groups with connected defining graph that are nonamenable (Theorem 2.55).

*Where every member dies.* A compactness, stability or ultralimit argument takes near-minimizers Φ_n, extracts a
limit object and proves a property of the limit, such as attainment, cycle-freeness or convergence of z_L. To
transfer that property back it must keep generation of the full relation. By §3.1, generation of the limit is
exactly what (T) supplies. By Corollary B, (T) fails for non-treeable Γ. So the limit generates a proper subrelation,
as the F_r×Z example of `fpbs-dead-limit-graphing-connectivity` shows concretely. The invariant is treeability of
free actions in the weak-equivalence class of b.

## 5. Consequences for the Cairn routes

1. `fpbs-bernoulli-cycle-tail-compactness` survives: condition (9.1) of `cost-cycle-structure.md` is a statement
   about τ_L, not about routes. But it cannot be proved through (T) on any non-treeable group, and those contain
   the open Kazhdan cases. The reduced-circulation hypothesis (6.3) of that note, which permits divergent routes, is
   the surviving quantitative channel. The F_r×Z calculation of its Section 8 is consistent with Corollary B: there
   the route lengths are geometric with mean ~1/ε and (T) fails, while the reduced mass stays bounded.
2. Theorem A gives a self-contained sufficient condition for Fixed Price: **b is weakly equivalent to a free
   treeable action**. That is a different prerequisite from cost–Betti equality and it can fail independently. It
   fails for all non-treeable groups. Whether it holds for treeable but not strongly treeable groups is open here.
3. Under (i), cost–Betti equality C(b)=1+β_1^(2)(Γ) would follow from Gaboriau's formula for treeable relations
   (2002, Corollaire 3.23 there). That formula is **not** imported verbatim in this note. So the node records only
   the Fixed Price consequence.

## 6. What is not claimed

* No new group is shown to have fixed price. We know of no group satisfying (iii) that was not already known to
  have fixed price (for example amenable groups and free groups, where b itself is treeable).
* Corollary B for a general free action a relies on a continuous compact model of a (§4). The Bernoulli case,
  which is what the target and the claim node use, needs no such model.
* Label tightness is part of (T). A version with route-length tightness alone, where labels may escape, is not
  addressed. The limit construction genuinely loses edges whose labels escape.
