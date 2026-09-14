# sk-exchange plan: is LC(X,F) ⋊ Z an exchange ring? (2026-09-14)

Lane sk-exchange, wave 12. Problem: for a minimal homeomorphism `T` of the Cantor set `X` and a field `F`, is `R = LC(X,F) ⋊_T Z` an exchange ring? By sk-algebraic-putnam (reviewed twice by sk-verify-16), a yes gives `sr(R) = 1` (Camillo–Yu), which is the algebraic Putnam theorem. Open nodes: `minimal-cantor-crossed-product-is-an-exchange-ring` and `minimal-cantor-crossed-product-has-stable-rank-at-most-two`.

## 0. What is already on main
- Laurent elements `p ∈ F[u^{±1}]` are suitable. The tower CRT witness works because right ideals `qR` are columnwise (Lemma C).
- Idempotents of `M_n(R)` are similar to clopen diagonals, and `R` has internal cancellation.
- Pairs `(a, e)` with `e` idempotent are stable, regular elements are unit-regular, and exchange ⇒ `sr = 1`.
- Why the lane got stuck: for general `a`, `aR` is not characterized columnwise, and block witnesses do not glue across cuts.

## 1. Three reductions (derived by hand in this lane; not yet reviewed)

**Lemma 1 (clean elements are suitable).** If `a = e + g` with `e² = e` and `g ∈ R^×`, then `f := g(1−e)g^{−1}` is an idempotent with `f ∈ aR` and `1 − f ∈ (1−a)R`.
- *Proof.* `a(1−e) = g(1−e)`, so `f ∈ aR`. `(1−a)e = e − e − ge = −ge`, so `1 − f = geg^{−1} ∈ (1−a)R`. ∎
- This is the elementwise form of Nicholson's "clean ⇒ exchange" (Trans. AMS 229 (1977), Prop. 1.8; locator to be checked at source).
- So it suffices to show that `R` is clean: every element is an idempotent plus a unit.

**Lemma 2 (local membership).** `z ∈ aR` iff there is `ρ` such that for every `x ∈ X` and `t ∈ Z`, in the orbit representation of `x`, `zδ_t ∈ a(span{δ_s : |s−t| ≤ ρ})`.
- *Only if*: the columns of `r` have propagation `w_r`.
- *If*: the set of points where radius `ρ` suffices at `t = 0` is clopen (finite window) and shift-covariant. These sets exhaust `X`, so compactness gives a uniform `ρ`. Choose preimages by a fixed rule per window type (finitely many types). The resulting `r` has locally constant entries, so `r ∈ R` and `ar = z`. ∎
- This generalizes sk-algebraic-putnam's Lemma C, where the division algorithm supplied the radius.

**Lemma 3 (nilpotent cut correction).** Let `a` have propagation `w`. Take a Kakutani–Rokhlin partition `𝒫` with heights `h ≥ L ≫ w`, refined so that the local data of `a` determine the atoms.
- Write `a = D + N`: `D ∈ A_𝒫 ≅ ∏ M_h(F)` is the block compression, and `N` collects the entries across cuts.
- `N` kills every interior coordinate (distance `> w` from all cuts) and maps into the boundary windows `Bd`.
- Suppose `f ∈ A_𝒫` is idempotent and `g := D − f ∈ A_𝒫^×` satisfies `g^{−1}(Bd) ⊆ Int`, block by block.
- Then `(g^{−1}N)² = 0`. So `a − f = g(1 + g^{−1}N)` is a unit, with `(1 + g^{−1}N)^{−1} = 1 − g^{−1}N ∈ R`, and `a` is clean. ∎
- Refinement: it is enough that `g^{−1}(im N) ⊆ ker N` blockwise.

## 2. The obstruction to the naive Block Lemma
- Lemma 3 needs a finite-dimensional **Block Lemma**: for the compression `D ∈ M_h(F)` of each block type, there is an idempotent `f` with `D − f` invertible and `(D−f)^{−1}(Bd) ⊆ Int`.
- It FAILS for degenerate compressions. For `D = 0`, invertibility forces `f = 1` and `g^{−1}(Bd) = Bd`. `D = 1` is similar.
- Changing `D` on the `Bd × Bd` block (absorbed into `N`) does not help. The condition reduces to (i) `(D−f)|_Int` is injective with image containing `Bd`, and (ii) a bijection `Bd → Int/(Int ∩ (D−f)(Int))`. Neither involves `D_22`.
- So the scheme must use the refined condition `g^{−1}(im N) ⊆ ker N`, adaptive cuts, or non-block-diagonal `f`.

## 3. Plan
- **P1, refined Block Lemma.** Classify the block types where the naive lemma fails. Show that they force `N` to be degenerate enough for the refined condition, or that shifting the cut positions (a second partition with cuts at mid-levels) removes them. Model-test `a = e_W`, `a = e_Wu`, `a = u + u²`, and `2×2` blocks over `F_2`.
- **P2, first-order reduction.** By the Morita compression along long returns (sk-free-7), `R ≅ End_S(S^h ⊕ Q)` with `S` an induced system, where elements of propagation `< L` become tridiagonal with propagation `≤ 1`. Exchange is Morita invariant, so first-order banded operators suffice, and their kernel and cokernel along orbits are governed by transfer matrices. Aim for residue-map witnesses as in Theorem S, with transfer-matrix residues in place of `F[u]/(p_0)`.
- **P3, gluing via DP.** Use sk-algebraic-putnam's one-cut Laplace splitting to turn a blockwise clean decomposition with window defects into a global one. The idempotent part already glues (Theorem DP); what needs gluing is invertibility of `g`.
- **P4, literature.** Check at source: Nicholson 1977 Prop. 1.8; Han–Nicholson, Comm. Algebra 29 (2001), on corners of clean rings; Camillo–Yu 1994; Ara's exchange results for crossed products and Steinberg algebras; Ara–Goodearl–O'Meara–Pardo 1998 (C*-algebras: exchange iff real rank zero).
- **P5, obstruction hunt.** Necessary conditions already hold: nonzero one-sided ideals contain idempotents, and `V(R) ≅ K^0(X,T)^+` is a refinement monoid. Look for an element whose suitability would force a non-local projection.

## 4. Search bound so far
Two web searches ("Steinberg algebra exchange ring ample groupoid"; "algebraic crossed product minimal homeomorphism Cantor exchange ring stable rank one") found no algebraic exchange or clean theorem for these rings. The hits are C*-level: Putnam; Archey–Phillips arXiv:1505.00725; Phillips math/0408291; arXiv:2008.03361. Their norm approximations have no exact algebraic analogue.
