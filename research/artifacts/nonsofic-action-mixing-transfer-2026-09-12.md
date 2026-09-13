# Mixing transfer for nonsofic actions of lattices in Howe--Moore groups (2026-09-12)

Lane `ex-nonsofic-action-relative`. Everything marked THEOREM or LEMMA has a complete proof here.
Unreviewed by `ex-verify-*` at landing time.

## 0. Summary

* **LEMMA ED.** A p.m.p. action of a countable group whose ergodic components are almost all sofic is
  sofic. So a group outside Păunescu's class `𝒮` has a free *ergodic* nonsofic action.
* **THEOREM MT.** Let `H` be a second countable locally compact group with the Howe--Moore property and
  `Γ <= H` a lattice. If `Γ` has an ergodic nonsofic p.m.p. action `Z`, then the restriction to `Γ` of
  the induced action `H ↷ H ×_Γ (Z × {0,1}^Γ)` is essentially free, mixing, and not sofic.
* **COROLLARY.** If `SL_3(Z)` has a nonsofic p.m.p. action, then `SL_3(Z)` (residually finite, hence
  sofic) has an essentially free mixing nonsofic action. So `sl3z-admits-nonsofic-action` implies
  `mixing-free-nonsofic-action-of-sofic-group`. The same holds for every lattice in a noncompact
  connected simple real Lie group with finite center, or in an isotropic simple algebraic group over a
  non-Archimedean local field.

The mechanism: nonsoficity of a free action is an orbit-equivalence invariant (Păunescu Theorem 1.5),
and inducing through `H` produces an action orbit equivalent to one that has the seed as a factor,
while Howe--Moore makes the induced action mixing. This gets around
`kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions`: that theorem says no fixed-algebra argument
applied *to* a mixing action proves it nonsofic, but nonsoficity can still be carried *onto* a mixing
action along an orbit equivalence from a non-mixing one.

## 1. Imports (verbatim from the PDFs, read 2026-09-12 via pdftotext of the arXiv files)

L. Păunescu, *On sofic actions and equivalence relations*, arXiv:1002.0605v5 (J. Funct. Anal. 261
(2011)). Definition 1.4, Proposition 1.15, Theorem 3.1 are already transcribed in
`research/artifacts/free-nonsofic-action-sources-verified-2026-09-11.md`. Additionally:

> **Theorem 1.5.** Let α and β be two free orbit equivalent actions. If α is hyperlinear (sofic) then
> also β is hyperlinear (sofic).

> **Lemma 1.6.** Let {e_i | i ∈ N} be projections in Π_{k→ω} D_{n_k} such that Σ_i e_i = 1. Let
> {u_i | i ∈ N} be unitary elements in Π_{k→ω} P_{n_k} such that Σ_i u_i^* e_i u_i = 1. Then
> v = Σ_i e_i u_i is a unitary in Π_{k→ω} P_{n_k}.

(Its proof begins: "Using Σ_i e_i = 1 we can easily construct projections e_i^k ∈ D_{n_k} such that:
1. e_i = Π_{k→ω} e_i^k; 2. Σ_i e_i^k = 1_{n_k}." This lifting is used in Lemma LC below.)

C. Ciobotaru, *A unified proof of the Howe--Moore property*, arXiv:1403.0223:

> **Definition 2.6.** Let G be a locally compact group and let G ∪ {∞} be the one point
> compactification of G. We say that G has the Howe–Moore property if the set of all unitary
> representations of G is the union of the ones having non-zero G–invariant vectors and the ones for
> which all matrix coefficients are C_0.

> **Theorem 1.1.** Let G be a connected, non-compact, simple real Lie group, with finite center, or an
> isotropic simple algebraic group over a non Archimedean local field, or a closed, topologically
> simple subgroup of Aut(T) that acts 2–transitively on the boundary ∂T, where T is a bi-regular tree
> with valence ≥ 3 at every vertex. Then G admits the Howe–Moore property.

(Ciobotaru, Introduction: "This property was first established by Howe and Moore [HM79] and Zimmer
[Zim84], around 1977, for connected, non-compact, simple real Lie groups that are with finite center.")
C_0 there means: for every ε > 0 the set {g : |c_{v,w}(g)| >= ε} is compact.

A. Furman, *A survey of measured group theory*, arXiv:0901.0678, p. 5: "The standard example of a
non-uniform lattice is Γ = SL_n(Z) in G = SL_n(R)."

From the graph: Lemma A of `sofic-action-class-commensurability-proof` (a factor of a restriction of a
sofic action is sofic).

## 2. LEMMA LC (finite models)

Let `G` be countable, `G ↷ (X,μ)` p.m.p., `M = L^∞(X) ⋊ G` with trace `τ(a u_g) = δ_{g,1} ∫ a dμ`.
Fix finite partitions `P_1 <= P_2 <= ...` of `X` into Borel sets generating the Borel σ-algebra mod
null sets, and finite sets `F_1 ⊆ F_2 ⊆ ...` exhausting `G`. Let `𝒲_m` be the finite set of words of
length `<= m` in the letters `u_g, u_g^*` (`g ∈ F_m`) and `1_p` (`p ∈ P_1 ∪ ... ∪ P_m`). A **model of
level `m` and error `ε`** is a finite set `Y`, a map `σ : F_m → Sym(Y)` and a partition
`(Y_p)_{p ∈ P_m}` of `Y`, such that for every `w ∈ 𝒲_m`

```text
| tr_Y( w(σ, 1_Y) ) − τ( w(u, 1) ) | < ε ,
```

where `u_g ↦ σ(g)` (a permutation matrix), `1_p ↦ Σ_{q ∈ P_m, q ⊆ p} 1_{Y_q}` (a diagonal projection),
and `tr_Y` is the normalized trace.

**LEMMA LC.** The action is sofic (Păunescu Definition 1.4) iff it has a model of every level `m` and
every error `ε > 0`.

*Proof.* (⇒) Let `Θ : M → Π_{k→ω} M_{n_k}` be a sofic embedding. The atoms of `P_m` form a partition of
unity in `L^∞(X)`, so their images lift, as in the proof of Păunescu Lemma 1.6, to partitions
`(Y^k_q)_{q ∈ P_m}` of `[n_k]` with `Θ(1_q) = Π_{k→ω} 1_{Y^k_q}`. Coarser `1_p` are sums of atoms, and
their lifts are the corresponding unions. Lift `Θ(u_g)` (`g ∈ F_m`) to permutations `σ_k(g)`. For each of
the finitely many `w ∈ 𝒲_m`, `tr(w(σ_k, 1_{Y^k})) → tr_ω(Θ(w)) = τ(w)` along `ω`, so some `k` gives a
model of error `ε`.

(⇐) Choose models `(Y_m, σ_m, (Y_{m,p}))` of level `m` and error `1/m`, and a free ultrafilter `ω` on
`N`. Put `U_g = Π_{m→ω} σ_m(g)` (defined for `m` with `g ∈ F_m`, arbitrary before) and, for
`p ∈ P_{m_0}`, `E_p = Π_{m→ω} Σ_{q ∈ P_m, q ⊆ p} 1_{Y_{m,q}}`. These are permutations and diagonal
projections. Each word `w` lies in `𝒲_m` for all large `m`, so `tr_ω(w(U,E)) = τ(w(u,1))`. Let `𝒜_0 ⊆ M`
be the ∗-algebra generated by `{u_g}` and `∪_m span{1_p : p ∈ P_m}`; it is weakly dense in `M`. The words
are closed under products and adjoints, so for scalars `c_i` and words `w_i`

```text
‖ Σ c_i w_i(U,E) ‖_2^2 = Σ c̄_i c_j tr_ω(w_i^* w_j (U,E)) = Σ c̄_i c_j τ(w_i^* w_j) = ‖ Σ c_i w_i(u,1) ‖_2^2 .
```

So `Σ c_i w_i(u,1) ↦ Σ c_i w_i(U,E)` is a well-defined, trace-preserving ∗-homomorphism on `𝒜_0`. It
sends unitaries to unitaries and projections to projections, so it is bounded on the generators, and it
extends to a normal trace-preserving ∗-embedding `Θ` of `M`. `Θ(L^∞(X))` is the weak closure of the
image of `∪_m span 1_{P_m}`, which lies in the von Neumann subalgebra `Π_{m→ω} D_{|Y_m|}`, and
`Θ(u_g) = U_g` is a permutation. ∎

## 3. LEMMA ED (ergodic integrals)

**LEMMA ED.** Let `G ↷ (X,μ)` be p.m.p. with ergodic decomposition `μ = ∫ μ_t dν(t)`. If for ν-almost
every `t` the action `G ↷ (X,μ_t)` is sofic, then `G ↷ (X,μ)` is sofic.

*Proof.* Fix `P_m, F_m` as in Lemma LC (they generate mod `μ_t`-null sets as well, for every `t`). For a
word `w = u_{g_1}^{±} 1_{p_1} ⋯`, moving the unitaries to the right gives `w = 1_{B_w} u_{h_w}` with
`h_w` the product of the group letters and `B_w` a Borel intersection of translates of the `p_i`. So
`τ_μ(w) = δ_{h_w,1} μ(B_w)`, affine in the measure, and `t ↦ τ_{μ_t}(w)` is measurable with
`τ_μ(w) = ∫ τ_{μ_t}(w) dν(t)`.

Fix `m`, `ε`, and let `T_0` be a ν-conull set of sofic components. The vector
`v_μ = (τ_μ(w))_{w ∈ 𝒲_m} ∈ [−1,1]^{𝒲_m}` is the ν-integral of `t ↦ v_{μ_t}`, so it lies in the closed
convex hull of `{v_{μ_t} : t ∈ T_0}`. Choose `t_1, ..., t_r ∈ T_0` and positive integers `a_1, ..., a_r`
with `b = Σ a_j` and `max_w |Σ_j (a_j/b) v_{μ_{t_j}}(w) − v_μ(w)| < ε/2`. By Lemma LC (⇒) for
`μ_{t_j}` there is a model `(Y_j, σ_j, (Y_{j,p}))` of level `m` and error `ε/2` for `(X, μ_{t_j})`. Put
`N = Π_i |Y_i|`, `c_j = a_j N / |Y_j|`, and `Y = ⊔_j Y_j × [c_j]` with `σ(g) = ⊔_j σ_j(g) × id` and
`Y_p = ⊔_j Y_{j,p} × [c_j]`. Then `|Y_j × [c_j]| / |Y| = a_j / b`, and normalized traces of words are
averages over the blocks:

```text
tr_Y(w) = Σ_j (a_j/b) tr_{Y_j}(w),   so   |tr_Y(w) − τ_μ(w)| < ε/2 + ε/2 .
```

So `(X,μ)` has models of every level and error, and it is sofic by Lemma LC (⇐). ∎

**COROLLARY ED.** If `G ∉ 𝒮`, then `G` has an essentially free ergodic nonsofic p.m.p. action.

*Proof.* By Păunescu Theorem 3.1 some free action `G ↷ (X,μ)` is not sofic. The non-free set is
μ-null, hence `μ_t`-null for a.e. `t`. By Lemma ED, the set of `t` for which `(X, μ_t)` is not sofic is
not contained in any ν-null set, so it meets the conull set of `t` for which `μ_t` is ergodic and the
action is `μ_t`-essentially free. ∎

## 4. LEMMA EQ (equal measure sets in an ergodic relation)

**LEMMA EQ.** Let `R` be a countable Borel equivalence relation on a finite measure space `(X,m)` with
`m` `R`-invariant and `R` ergodic. If `A, B ⊆ X` have `m(A) = m(B)`, there is a partial isomorphism
`φ ∈ [[R]]` from a conull subset of `A` onto a conull subset of `B`.

*Proof.* By Feldman--Moore, `R = ∪_j graph(θ_j)` for Borel automorphisms `θ_j` with graph in `R`. Put
`φ_0 = ∅`, and at stage `j` let `C_j = (A ∖ dom φ_{j−1}) ∩ θ_j^{−1}(B ∖ ran φ_{j−1})` and
`φ_j = φ_{j−1} ∪ θ_j|_{C_j}`. Then `φ = ∪_j φ_j ∈ [[R]]` and invariance gives
`m(A' ) = m(B')` for `A' = A ∖ dom φ`, `B' = B ∖ ran φ`. If `m(A') > 0`, ergodicity makes the
saturation `[A']_R` conull, so `m(B' ∩ [A']_R) > 0` and some `j` has `m(A' ∩ θ_j^{−1}(B')) > 0`. But
`A' ⊆ A ∖ dom φ_{j−1}` and `B' ⊆ B ∖ ran φ_{j−1}`, so that set lies in `C_j ⊆ dom φ`, a contradiction. ∎

Section 5 (the theorem) continues in part 2:
`research/artifacts/nonsofic-action-mixing-transfer-part2-2026-09-12.md`.
