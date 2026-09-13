# Review: STW Problem L and the six-loop Kirchberg answer

Lane `l-verify`, 2026-09-13, main tip `b4271455d`. Under review, and unchanged at that tip except for the becc912bd
wipe and its 3f71a3a50 restore:

- the root `research/stw99-problem-l-explicit-automorphism-loops.md`;
- `research/artifacts/stw50-rotation-loop-retraction-2026-09-04.md` (497438b84);
- `research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md` (98bba0c8a);
- `research/artifacts/stw50-six-loops-independent-recheck-2026-09-04.md` (dccd7b328);
- the 14 `research/stw50-*` nodes:
  - six-kirchberg-circle-loops{,-proof}
  - kernel-basis-completes-explicit-loop-problem
  - explicit-basis-of-rotation-retraction-kernel
  - kirchberg-kernel-loops-proof
  - kirchberg-loop-{classification-inputs,inputs-proof}
  - rotation-loops-form-a-direct-summand
  - rotation-summand-proof
  - torus-loop-retraction-proof
  - unit-retraction-splits-torus-loops
  - bott-and-rotation-unit-{citation,inputs}
  - stably-finite-six-loop-basis

## Verdict: PASS for the Kirchberg alternative

As printed, Problem L is a disjunction. Its second disjunct asks for explicit loops generating π_1(Aut(A)), where A is
the unital UCT Kirchberg algebra with the K-theory of A_θ. This disjunct belongs to the printed question; it is not a
side remark. The artifact answers it:

- Six circle actions on A = B ⊗_min B form a ℤ-basis of π_1(Aut(A), id).
- Four of these actions are edge-phase actions on a second graph model C, moved to A by one fixed classification
  isomorphism ψ : C → A.
- Their invariant matrix has determinant 1.

Every finite step was re-derived here (§3). The one heavy import, Lemma 1, was checked against the printed text of
Dadarlat's Theorem 6.3 (§4). No mathematical error was found.

Three caveats must travel with this PASS.

1. **Explicitness.**
   - Every loop is an explicit circle action on a finite graph algebra or on a tensor factor.
   - The identifications have no formula on generators. They are nonconstructive Kirchberg–Phillips isomorphisms:
     ψ : C → A, and, for the kernel form, χ : A → A_θ ⊗ O_∞.
   - The paragraph right after Problem L proposes this kind of model: a groupoid or Cuntz–Krieger model, identified
     with A_θ ⊗ O_∞ by a classification isomorphism.
   - The answer uses two models where that paragraph imagines one, so no single presentation shows all six loops.
   - Generation holds for every ψ, so the choice of isomorphism does not matter.
2. **Scope.** The stably finite disjunct, loops in Aut(A_θ) itself, is not answered. It stays open as
   `stw50-stably-finite-six-loop-basis`. The "More generally" sentence is not claimed.
3. **Status.** This review checks the written proof against its sources. It is not expert review. Nothing is
   machine-checked except the integer certificate script `experiments/stw50_six_kirchberg_loops_check.py`.

## 1. The printed problem

**Source.** C. Schafhauser, A. Tikuisis and S. White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902v2, §14
"Finding loops of automorphisms", Problem L (TeX label `q:pi1`). I read it in the v2 TeX source and the v2 PDF text,
and the wording agrees. By footnote 101, Aut(A) carries the point-norm topology.

**Printed text** (TeX source):

> Find explicit loops generating the group $\pi_1(\mathrm{Aut}(A_\theta))\cong \mathbb Z^6$, or the group
> $\mathrm{Aut}(A)$, where $A$ is the unital UCT-Kirchberg algebra with the same $K$-theory as $A_\theta$.  More
> generally obtain explicit descriptions of generators of $\pi_1(\mathrm{Aut}(A))$ for other UCT-Kirchberg or
> monotracial classifiable $C^*$-algebras $A$.

**Scope decisions.**

1. **"the group Aut(A)" is a slip for π_1(Aut(A)).** Loops generate a fundamental group, not Aut(A). The paragraph
   just before Problem L poses the analogous question for π_1(Aut(A_θ ⊗ O_∞)).
2. **The Kirchberg algebra is a printed disjunct.** The first sentence says: find loops for A_θ, or for A. Answering
   the second disjunct answers that sentence as printed. The Kirchberg case is not an aside:
   - the preceding paragraph builds this counterpart (γ ⊗ id on A_θ ⊗ O_∞);
   - the following paragraph expects the Kirchberg case to be the easier one.
3. **A is determined only up to isomorphism.** By Kirchberg–Phillips, the unital UCT Kirchberg algebra with
   (K_0, [1], K_1) ≅ (ℤ², (1,0), ℤ²) is unique up to isomorphism. So B ⊗ B and A_θ ⊗ O_∞ are both "the" A, and any
   concrete presentation of A comes with a classification isomorphism.
4. **"More generally …" is a research direction.** The answer claims nothing there.
5. **The summand request is separate.** Before Problem L, STW suspect that the two rotation loops span a ℤ² direct
   summand, and they ask for a proof. `stw50-rotation-loops-form-a-direct-summand` proves this for A_θ and for
   A_θ ⊗ O_∞ (§3.6). That request is not part of Problem L.

## 2. The answer under review

This summarizes artifact §§1–7.

- **Lemma 1.** Let D be a unital UCT Kirchberg algebra with free K-groups and primitive unit. Then
  π_1(Aut(D), id) ≅ Hom(K_1D, K_0D) ⊕ Hom(K_0D/ℤ[1], K_1D). The map is Δ_α = [α̂] − [id] ∈ KK(D, SD), where
  α̂(a)(z) = α_z(a).
- **Graphs and unitaries.** The graph E(u) has a loop d_i at each vertex i and u_j edges i → j. Its rows R_i give
  unitaries W_i = R_iR_n^*.
- **Edge phases.** The edge phase g_{ij,z} multiplies the one edge a_{ij}^{(1)} by z. Then
  Δ_{g_{ij}}[W_k] = δ_{ik}[p_j].
- **Models.**
  - C = C\*(E(1,1,2)) carries four loops h_1, …, h_4.
  - B = C\*(E(1,2)) carries one loop γ.
  - On A = B ⊗ B, the tensor actions ρ_1 = γ ⊗ id and ρ_2 = id ⊗ γ supply the other two directions.
- **Basis.** With σ_j = ψh_jψ^{-1}, the six classes have the unimodular matrix L.
- **Kernel loops.** The products σ_2, σ_4, ρ_1σ_1^{-1} and ρ_2σ_3^{-1}, conjugated by χ, form a basis of the kernel
  of the rotation retraction on A_θ ⊗ O_∞.

## 3. Re-derivations

### 3.1 Graph K-theory

**General graph.** E(u) has adjacency matrix M(u)_{ij} = δ_{ij} + u_j.

- The relations s_a^*s_a = p_{r(a)} and Σ_{s(a)=i} s_as_a^* = p_i give [p_i] = Σ_j M_{ij}[p_j], that is,
  Σ_j u_j[p_j] = 0.
- So K_0 = ℤ^n/ℤu. This agrees with coker(I − M^t), since I − M^t = −u1^t.
- K_1 = ker(I − M^t) = {x : Σx_i = 0} ≅ ℤ^{n−1}.
- The formula gives [[2,1,2],[1,2,2],[1,1,3]] for u = (1,1,2) and [[2,2],[1,3]] for u = (1,2), as in the artifact.

**The model C.** Take e_C = (1,1,1) and b = [p_1].

- 2e_C − b − [p_2] = (1,1,2) = u and −e_C − [p_3] = −u, which gives (7).
- The columns u, e_C, b have determinant −1, so {e_C, b} is a basis of K_0(C).

**The model B.** The map (x,y) ↦ 2x − y has kernel ℤ(1,2). It sends e_B, [p], [q] to 1, 2, −1, which gives (9).

### 3.2 Rows and the edge-phase identity

**Row lemma.**

- The edge entries of R_i are exactly the edges out of i, so their range projections sum to p_i. Each other column
  contributes p_j for j ≠ i. So R_iR_i^* = 1.
- Column (j,k) has initial projection p_j for every i, and the cross terms vanish. So R_i^*R_i = P.
- Hence R_i = R_iP, and W_i = R_iR_n^* is unitary.

**Edge-phase identity.** Let i < n and g = g_{ij,z}, and put a = a_{ij}^{(1)}. The phase g fixes R_n and every R_k
with k ≠ i, so

  g(W_i)W_i^* = g(R_i)PR_i^* = g(R_i)R_i^* = 1 + (z−1)s_as_a^*.

Use the convention that the loop 1 + (z−1)p has Bott class [p]. Since s_as_a^* ∼ p_j, this gives
Δ_g[W_i] = [p_j], which is (5).

**The K_1 → K_0 part of Δ.** At a unitary w, the reduced part of Δ_α is the Bott class of z ↦ α_z(w)w^*. This is
because [α̂(w)] = [α̂(w)w^*] + [w] in K_1(C(𝕋) ⊗ D).

**Continuity.** Each g_z preserves the relations and has inverse g_{z̄}. For a polynomial x in the generators,
z ↦ g_z(x) is a Laurent polynomial, and ‖g_z‖ ≤ 1. Density then gives point-norm continuity. The same argument gives
γ ⊗ id on B ⊗_min B.

### 3.3 Invariant tables

**The model C.** Put U_1 = R_1R_3^* and U_2 = R_2R_3^*.

- h_1 = g_{13,z^{-1}} gives Δ[U_1] = −[p_3] = e_C, and h_2 = g_{11,z} gives Δ[U_1] = [p_1] = b.
- h_3 and h_4 give the same values on U_2.
- Δ[U_k] = 0 for the other k, and K_0 is fixed. So the table in artifact §3 is correct.
- {[U_1], [U_2]} is an integral basis of K_1(C). The functionals φ_i = −(e_C-coefficient of Δ_{g_{i3}}) satisfy
  φ_i[U_k] = δ_{ik}, so ℤ² → K_1(C) splits, and a rank-2 summand of ℤ² is all of ℤ².

**The model B.** γ scales a_{12}^{(1)} by z^{-1}, so Δ_γ[V] = −[q] = e_B. Since K_1(B) ≅ ℤ and e_B generates K_0(B),
v = [V] generates K_1(B).

**The algebra A = B ⊗ B.** The torsion-free Künneth theorem gives the bases:

- K_0(A) = ℤe ⊕ ℤβ, with β = v ⊠ v;
- K_1(A) = ℤx ⊕ ℤy, with x = v ⊠ e_B and y = e_B ⊠ v.

The tensor actions act as follows:

- ρ_1: Δx = e, Δy = 0 and Δβ = e_B ⊠ v = y.
- ρ_2: Δy = e and Δx = 0. Also Δβ = −x, because the odd Bott generator moves past the odd v.

This matches artifact §5.

### 3.4 L, its determinant and inverse, and the kernel

**Columns of L.** Use the coordinates ((Δx)_e, (Δx)_β, (Δy)_e, (Δy)_β, (Δβ)_x, (Δβ)_y). ψ sends e_C, b, [U_1], [U_2]
to e, β, x, y, and Δ is natural under conjugation. So the columns are:

- σ_1, σ_2, σ_3, σ_4 give e_1, e_2, e_3, e_4;
- ρ_1 gives e_1 + e_6, and ρ_2 gives e_3 − e_5.

This is (15).

**Determinant.** L is block upper-triangular: the upper-left 4×4 block is I and the lower-right block is [[0,−1],[1,0]].
So det L = 1. The conclusion does not depend on sign conventions. Flipping the Bott or Koszul sign changes only
signs inside the same pattern, and the determinant stays ±1.

**Inverse.** Solving c_1 + c_5 = a, c_2 = b, c_3 + c_6 = c, c_4 = d, −c_6 = f and c_5 = g gives
(a−g, b, c+f, d, g, −f), which is (16).

**Kernel columns.** The kernel loops have columns col2, col4, col5 − col1 = (0,0,0,0,0,1) and
col6 − col3 = (0,0,0,0,−1,0), which is (18). In the coordinates (b, d, f, g) of {a = c = 0} they form a matrix of
determinant 1.

**Any ψ.** ψ_* is an automorphism of (K_0, e, K_1), and:

- the σ_j span the intrinsic summand Hom(K_1A, K_0A), whatever ψ is;
- ρ_1 and ρ_2 project to a basis of Hom(K_0A/ℤe, K_1A).

The block-triangular argument then gives a basis. So the claim "for any ψ" in artifact §6 is correct.

### 3.5 Cross-check of the target group in Lemma 1

- Let C_uA be the mapping cone of ℂ → A. The unit map is injective, so the six-term sequence gives
  K_0(C_uA) ≅ K_1(A) and K_1(C_uA) ≅ K_0(A)/ℤ[1].
- Since Ext vanishes, KK^1(C_uA, SA) = Hom(K_1A, K_0A) ⊕ Hom(K_0A/ℤ[1], K_1A). This is the right side of (1), of rank 6.
- It agrees with Dadarlat's Corollary 5.10, π_n(Aut(A)) ≅ KK(C_uA, S^{n+1}A), and with the formula that STW quote.

### 3.6 Rotation retraction and the kernel basis

**The lemma.** Take a torus action γ, unitaries u_j with γ_z(u_j) = z_ju_j, and ε : K_0 → ℤ with ε[1] = 1. Put
ρ([α]) = (ε Bott[α_t(u_j)u_j^*])_j. Then ρ∘γ_* = id, and the proof is correct:

- α ↦ α(u)u^* is a based continuous map, so it induces a homomorphism on π_1;
- π_1 of a topological group is abelian.

**Application to A_θ and A_θ ⊗ O_∞.** For A_θ, Pimsner–Voiculescu gives 0 → ℤ[1] → K_0(A_θ) → ℤ → 0, so ε exists. It
also gives the K_1 basis [U], [V]: [U] comes from the circle, and ∂[V] = ±[1]. The unital inclusion
A_θ → A_θ ⊗ O_∞ is a KK-equivalence, which carries all of this to the O_∞ case.

**Kernel step.** χ sends x, y to [U ⊗ 1], [V ⊗ 1] and e, β to [1], q, and ε reads the [1]-coefficient. So
r(χαχ^{-1}) = ((Δ_αx)_e, (Δ_αy)_e), and ker r = {a = c = 0}.

- The loops χκ_jχ^{-1} form a basis of ker r.
- Adding the two loops γ ⊗ id gives a basis of π_1(Aut(A_θ ⊗ O_∞)).
- As the 09-04 recheck notes, columns 1 and 3 of L already split r, so this step does not need the retraction
  artifact.

## 4. Lemma 1 against Dadarlat's text

**Source.** M. Dadarlat, *The homotopy groups of the automorphism group of Kirchberg algebras*, J. Noncommut. Geom. 1
(2007) 113–139, read from the PDF text.

- **Theorem 6.3.** Let A be a Kirchberg algebra, and let X be compact metrizable with (A, X) KK-continuous. If X is path
  connected and x_0 ∈ X, there is an exact sequence
  1 → K_1(C(X,x_0) ⊗ A)/∼ → [X, Aut(A)]_0 → id_A + KK(A, C(X,x_0) ⊗ A)_0 → 1.
  For X = 𝕋, C(𝕋, 1) ⊗ A = SA.
- **The kernel.**
  - Before Theorem 3.6, K_1(B)/∼ is defined as K_1(B)/Image(Q). Here Q is restriction along ℂ → A followed by the
    boundary map (Prop. 3.4).
  - For B = SD, after Bott periodicity, this is K_0(D) modulo the image of evaluation at [1_D] on KK(D, D).
  - The UCT makes that evaluation surjective: the map with e_D ↦ a, a complement ↦ 0 and K_1 ↦ 0 lifts to KK(D, D).
  - So the kernel is trivial, as the artifact says.
- **The image.** KK(A, SA)_0 is the set of classes that kill [1_A]. With free K-groups this is the right side of (1).
- **Hypotheses and group law.** Examples 5.4 give KK-continuity for locally contractible X. Remark 6.4 makes the
  product of reduced classes vanish when X is a path-connected H′-space, and 𝕋 is one. So the group law is additive.
- **Basepoints.** Based and unbased classes into the identity component agree, via H(1,t)^{-1}H(z,t), as in artifact §1.

Every use of Dadarlat in Lemma 1 matches the printed statements.

## 5. Imported theorems

I opened and checked two sources in this session: STW v2 and Dadarlat 2007. The rest are standard results; they are
cited but were not opened here.

1. Dadarlat 2007: Theorem 6.3; the definition of Q before Theorem 3.6 (Prop. 3.4); Examples 5.4; Remark 6.4; and, as
   a cross-check, Corollary 5.10. [opened]
2. The Rosenberg–Schochet UCT, Duke Math. J. 55 (1987): surjectivity of KK(D, D) onto Hom, and vanishing of Ext.
3. Bates–Pask–Raeburn–Szymański, New York J. Math. 6 (2000), §5: the graph algebras are simple and purely infinite.
4. Kumjian–Pask, New York J. Math. 6 (2000), Theorem 5.5: nuclearity and the bootstrap class. Alternatively, the gauge
   crossed product is AF, and Takai duality applies.
5. Drinen–Tomforde, arXiv:math/0103036, Theorem 3.1: K_0 is generated by vertex classes with these relations, and
   K_1 = ker(I − M^t).
6. The torsion-free Künneth theorem (Schochet, Pacific J. Math. 98 (1982)), with the graded sign. Permanence: B ⊗ B is
   simple, purely infinite, nuclear and in the bootstrap class.
7. Unital Kirchberg–Phillips classification (Phillips, Doc. Math. 5 (2000), funct-an/9506010; Kirchberg): ψ and χ
   exist and realize the prescribed scaled K-theory isomorphisms.
8. Pimsner–Voiculescu, J. Operator Theory 4 (1980): the K-theory of A_θ, with the bases {[1], q} and {[U], [V]}.
9. O_∞ is KK-equivalent to ℂ through the unital inclusion (Cuntz). So A_θ ⊗ O_∞ is a unital UCT Kirchberg algebra with
   the K-theory and unit class of A_θ.
10. Stabilized Bott periodicity, K_1(SD) ≅ K_0(D), with the convention [1 + (z−1)p] ↦ [p].
11. π_1 of a topological group is abelian (Eckmann–Hilton).
12. The universal property of graph C\*-algebras, which gives the edge phases, and automorphisms α ⊗ id on ⊗_min.

These imports carry the analytic weight, and none is claimed as new. Artifact §8 says the same.

## 6. Novelty search to 2026-09-13

The search was bounded, so it does not prove absence.

- **STW v2** (arXiv:2506.10902v2) still poses Problem L and says it is unclear where the other four generators come from.
- **Papers citing STW**, from the Semantic Scholar list checked 09-13: arXiv 2609.11297, 2609.08892, 2607.04300,
  2602.10616 (journal version in Proc. London Math. Soc.), 2601.23029, 2601.08779, 2508.07938 and 2508.04837. None of
  them studies loops in automorphism groups.
- **Gabe–Schafhauser**, the work in progress STW cite for the stably finite computation. Nothing on homotopy groups of
  automorphism groups appears on Gabe's research page (checked 09-13) or on Schafhauser's homepage, and a web search
  for 2026 preprints found nothing.
- **Matsumoto–Sogabe.**
  - arXiv:2404.06115: abstract identifications only, no loop formulas.
  - arXiv:2502.18126, Münster J. Math. 18 (2025) 249–291, §7, Theorem 7.1: an isomorphism
    π_1(Aut(O_A)) → π_1(Aut(Ô_A)) that sends the gauge class to the gauge class. It gives no basis of loops.
  - arXiv:2511.06760: no loops.
- **Kamikawa, arXiv:2606.09212**: equivariant homotopy groups via KK, abstract, with no explicit loops and no mention of
  Problem L.
- **Sogabe, arXiv:2607.16755** (18 Jul 2026): the inner automorphism groups of Cuntz algebras have the same homotopy
  groups as Aut. No loops for this K-theory.
- **Not done.** The arXiv API for a math.OA listing sweep was unavailable (HTTP 429, then a timeout). The search
  therefore rests on citation data, author pages and web search.

No explicit six-loop basis was found, and no other answer to either disjunct of Problem L.

## 7. What is established and what is open

**Established** (written proof, reviewed here):

- the six-loop basis of π_1(Aut(B ⊗ B)), for every ψ;
- the four kernel loops on A_θ ⊗ O_∞, for the marking (19);
- the rotation direct summand, for A_θ and for A_θ ⊗ O_∞.

**Open:**

- explicit loops generating π_1(Aut(A_θ)), the stably finite disjunct;
- one presentation on which all six loops are visible, as STW's groupoid suggestion asks;
- formulas for ψ and χ;
- the "More generally" direction.

**Record nit.** The six-loop artifact's filename says 2026-09-05, but its commit 98bba0c8a is dated 2026-09-04, like
the recheck that reviews it. This affects dates only, not the mathematics.

## 8. Lean cost

**Smallest faithful statement.** This is sent to l-lean.

- **Definitions.** B := C\*(E(1,2)) and C := C\*(E(1,1,2)) are universal graph algebras, A := B ⊗_min B, and
  D_θ := A_θ ⊗_min O_∞. Aut_pn(X) is X ≃⋆ₐ[ℂ] X with the point-norm topology.
- **(a) The models are "the" algebra.** For irrational θ, Nonempty (A ≃⋆ₐ[ℂ] D_θ) and Nonempty (C ≃⋆ₐ[ℂ] A).
- **(b) Generation and independence.** Let ψ : C ≃⋆ₐ[ℂ] A be arbitrary. Consider the based loops
  t ↦ ψ∘h_j(e^{2πit})∘ψ^{-1} for j = 1, …, 4, t ↦ ρ_1(e^{2πit}) and t ↦ ρ_2(e^{2πit}). Their classes generate
  π_1(Aut_pn A, id). They are also independent: if the ordered product of [loop_j]^{n_j} is 1, then n = 0.

Part (a) ties A to STW's algebra without Kirchberg or UCT predicates.

- **Imports for (b):** Dadarlat's Theorem 6.3, the UCT, graph K-theory, Künneth and Bott periodicity.
- **Imports for (a):** Kirchberg–Phillips, BPRS, Kumjian–Pask and Pimsner–Voiculescu.

**What exists.**

- The Mathlib pin 81a5d257 has no K-theory, no graph C\*-algebras and no ⊗_min.
- The repository tip has:
  - an abstract `KasparovTheory` structure with no inhabitant;
  - `KZero` over it;
  - `CStarKOne`;
  - `SatisfiesUCT`;
  - a spatial tensor product that is not yet ⊗_min, because Takesaki's independence theorem is unproved.

So an unconditional Lean proof of (a) or (b) is far out of reach.

**Formalizable now, unconditionally:**

- the integer certificate: L, det L = 1, the inverse (16), the kernel minor, the bases (7) and (9), and I − M^t = −u1^t;
- the algebraic row lemma in a star ring satisfying the graph relations;
- the edge-phase identity (4).
