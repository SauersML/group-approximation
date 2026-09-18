---
rg: 2
id: unimodular-maslov-cantorization-proof
kind: route
title: Proof that unimodular Maslov cells give a minimal, expansive, topologically free Cantor model of the Lagrangian Grassmannian
target: unimodular-maslov-cantorization-is-minimal-expansive
requires:
  - lagrangian-thompson-group-contains-deligne-lattice
---

The notation is that of the target. The proof uses two moves on frames.

- **Translation.** For `R ∈ Sym_n(R)`, let `u_R` fix `f` and send
  `e_i ↦ e_i + Σ_j R_ij f_j`.
  - It is symplectic, and it lies in `Γ` iff `R` is integral.
  - It acts in the chart by `S ↦ S + R`.
  - Hence the frame `(e + Rf, f)` has chart coordinate `S − R`.
- **Levi move.** For `A ∈ GL_n(Z)`, the frame `(Ae, A^{-T}f)` has coordinate `A S A^T`.
  - To see this, take the rows `Σ_i A_mi (e_i + Σ_l S_il f_l)`.
- **Swap.** `(f, −e)` is a frame. On `C_k(e,f)` its coordinate is `−S^{-1}`.

## Step 1. One frame separates (item 2)

Let `L ≠ L'`.
- Rational Lagrangians are dense, and transversality is open and dense. So pick a
  rational `B` transverse to both, and a frame with `L_f = B`.
- In that chart, `L = φ(S)` and `L' = φ(S')`, with `D = S' − S ≠ 0`.

**Case n ≥ 2.**
- The quadratic form `w ↦ w^T D w` is nonzero, so it does not vanish on some open cone.
- That cone contains primitive integer vectors of arbitrarily large norm, for example
  those of a rational plane meeting it.
- So there is a primitive `w` with `|w^T D w| > 1`. Take `A ∈ GL_n(Z)` with first row
  `w`, and replace the frame by its Levi move.
- Now `S̃ = A S A^T` and `S̃' = A S' A^T` satisfy `|S̃_11 − S̃'_11| > 1`.
- Choose an integer `ρ` strictly between `S̃_11` and `S̃'_11`, and put
  `R = diag(ρ, M, …, M)` with `M ∈ Z` large.
- With `T = S̃ − R`, the lower `(n−1)`-block `S̃_22 − M I` is negative definite. The
  Schur complement is `T_11 − b^T (S̃_22 − M I)^{-1} b → S̃_11 − ρ ≠ 0`, where `b` is the
  off-diagonal column of `S̃`.
- So for large `M`, `T` is invertible with `(n−1) + [S̃_11 < ρ]` negative eigenvalues.
- In the same way, `T' = S̃' − R` has `(n−1) + [S̃'_11 < ρ]` negative eigenvalues, and the
  two indices differ.
- The frame `(e + Rf, f)` is unimodular and has coordinates `T` and `T'`. So `L` and `L'`
  lie in different cells of it.

**Case n = 1.**
- As `B → L` with `B ≠ L` rational, the chart coordinate `s` of `L` tends to `±∞`, while
  that of `L'` stays bounded.
- Pick `B` with `|s − s'| > 1`, and translate by an integer `ρ` strictly between them.

In both cases `L ∈ C_k` and `L' ∈ C_{k'}` with `k ≠ k'`. ∎

## Step 2. Cantor model (item 1)

**Normal form.**
- Inside `Λ^0`, the complement of `C_k(e,f) ∩ Λ^0` is the union of the other cells of the
  same frame, intersected with `Λ^0`.
- So every element of `𝔅_u` is `W ∩ Λ^0`, where `W` is a finite union of finite
  intersections of cells. In particular `W` is open.
- An element is zero iff `W = ∅`, because `Λ^0` is dense.

**Cantor set.**
- `𝔅_u` is countable.
- It is atomless. A nonzero `W ∩ Λ^0` contains two points of `Λ^0`. By Step 1 some frame
  puts them in different cells `C_k` and `C_{k'}`, and these split the element into two
  nonzero parts.
- A countable atomless Boolean algebra has the Cantor set as its Stone space.

**π is well defined.**
- The sets `cl(B)`, for `B ∈ y`, have the finite intersection property, so
  `∩_{B ∈ y} cl(B)` is nonempty.
- Suppose `L ≠ L'` both lie in it. Take the frame of Step 1, with `L ∈ C_k` and
  `L' ∈ C_{k'}`.
- The ultrafilter `y` contains exactly one cell `C_j` of that frame.
- Cells are open and pairwise disjoint, so `L ∈ cl(C_j)` forces `j = k`, and
  `L' ∈ cl(C_j)` forces `j = k'`. This is a contradiction.

**π is continuous.**
- Let `V ∋ π(y)` be open.
- The compact sets `cl(B) ∖ V`, for `B ∈ y`, have empty intersection. Since `y` is closed
  under meets, one of them is empty.
- So `[B] ⊆ π^{-1}(V)`.
- The same argument gives, for every compact neighborhood `K` of `π(y)`, some `B ∈ y`
  with `cl(B) ⊆ K`.

**π is onto.**
- For `L ∈ Λ`, the set `I_L = {B : L ∉ cl(B)}` is a proper ideal, since
  `cl(B_1 ∪ B_2) = cl(B_1) ∪ cl(B_2)`.
- A maximal ideal containing `I_L` has as complement an ultrafilter `y` with
  `L ∈ cl(B)` for all `B ∈ y`. So `π(y) = L`.

**π is injective over Λ^0.**
- Let `L ∈ Λ^0`. Then `L` lies in one cell of each frame, so it lies in one atom of each
  finite subalgebra.
- The other atoms are open sets that miss a neighborhood of `L`.
- So only the principal ultrafilter `{B : L ∈ B}` maps to `L`.

**Equivariance.** `π` is equivariant because `γ cl(B) = cl(γB)`. ∎

## Step 3. Expansive (item 3)

- If `y ≠ y'`, some `A ∈ 𝔅_u` lies in `y` but not in `y'`.
- The frames occurring in `A` generate a finite subalgebra, and `y`, `y'` contain
  different atoms of it.
- Atoms are intersections of one cell per frame, so a single frame `γ(e_0,f_0)` puts `y`
  and `y'` in different cells.
- That means `γ^{-1}y` and `γ^{-1}y'` lie in different sets `[C_k(e_0,f_0)]`.
- Hence `y ↦ (k(γ^{-1}y))_{γ ∈ Γ}` is a continuous, equivariant injection into
  `{0,…,n}^Γ`. It is a subshift embedding, which is expansivity in the sense of
  `nekrashevych-expansive-groupoid-criteria`, item 6. ∎

## Step 4. Local contraction and minimality (items 4, 5)

**Parabolic contraction.**
- Let `M` be rational and take a frame with `L_f = M`.
- Given a finite-index `Δ ≤ Γ`, put `u = u_{dI}` with `d ≥ 1` such that `u ∈ Δ`.
  Such `d` exists because `Δ ∩ ⟨u_I⟩` has finite index in `⟨u_I⟩`.
- Then `u^m φ(S) = φ(S + mdI)`.
- In the swapped chart this point has coordinate `−(S + mdI)^{-1}`, which tends to `0`
  uniformly for `S` in compact sets. The coordinate `0` is the point `M`.
- So `u^m → M` uniformly on compact subsets of `Λ ∖ Σ(M)`.

**Local contraction (item 4).**
- Write `A = W ∩ Λ^0` with `W ≠ ∅` open, and fix an open `W'` with `cl(W') ⊆ W`.
- Pick a rational `M ∈ W'` transverse to `L = π(y)`. This is possible because such
  Lagrangians are open, dense and rational-dense.
- Pick a compact neighborhood `K` of `L` in `Λ ∖ Σ(M)`, and `B ∈ y` with `cl(B) ⊆ K`
  (Step 2).
- For large `m`, `u^m K ⊆ W'`. Since `u` preserves `Λ^0`, this gives
  `u^m B ⊆ W ∩ Λ^0 = A`.
- Take `N = [B]`.

**Minimality (item 5).**
- This is item 4.
- Item 4 allows any finite-index `Δ`, so no congruence subgroup property is needed.
  This matters for `n = 1`, where non-congruence subgroups exist.
- The same contraction shows that `u^m L → M` for every `L` and every rational `M`
  transverse to `L`. So `Γ ↷ Λ` is minimal, with no citation.

**The even-n factor.**
- Let `v, v' ∈ F`. Take `δ ∈ Γ` with `δv = v'`, and apply item 4 with `Δ = Γ(3)` to the set
  `δ^{-1}[A]`.
- Then `γ = δu^m` sends `(y, v)` into `[A] × {v'}`. ∎

## Step 5. Topologically free (item 6)

- The kernel of `Sp_{2n}(R)` on `Λ = Sp/P` is its center `{±I}` (textbook).
- For `γ ∉ {±I}`, the fixed set of the analytic map `γ` on the connected analytic
  manifold `Λ` has empty interior.
- Suppose a nonempty `[A] = [W ∩ Λ^0]` lay in `π^{-1}(Fix γ)`.
  - The principal ultrafilters of the points of `A` lie in `[A]`, so `A ⊆ Fix γ`.
  - Then `W ⊆ cl(A) ⊆ Fix γ`, which is a contradiction.
- On `Y_u × F`, the element `−I` has no fixed point, because it acts by `v ↦ −v` and
  `3` is odd. ∎

## Step 6. Decidable (item 7)

- By the normal form of Step 2, equality of two words reduces to emptiness of an open
  set `W`.
- `W` is a Boolean combination of sets defined by polynomial inequalities with integer
  coefficients in the matrix entries of `S`, over a finite atlas of charts.
- Emptiness of such a set is decidable by Tarski–Seidenberg (textbook). ∎

## Step 7. Scope (item 8)

Steps 4 and 5 use only three facts: the normal form `W ∩ Λ^0`, the separation of points
of `Λ` (through `π`), and `Γ`-invariance of `Λ^0`. The Cantorization `Y_Λ` of
`lagrangian-thompson-group-contains-deligne-lattice` refines `Y_u` and has all three.
Step 3, however, used that the algebra is generated by translates of one finite
partition. ∎
