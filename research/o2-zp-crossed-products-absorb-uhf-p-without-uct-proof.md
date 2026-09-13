---
rg: 2
id: o2-zp-crossed-products-absorb-uhf-p-without-uct-proof
kind: route
title: Meyer--Nest homotopy colimit for the UHF tower plus invertibility of p in KK(C,C)
target: o2-zp-crossed-products-absorb-uhf-p-without-uct
requires: [o2-zp-crossed-products-invert-p-in-kk]
---

**Source.**  Meyer--Nest, *The Baum--Connes conjecture via localisation of
categories*, arXiv:math/0312292, §2.4.  Read on MSI, 2026-09-12, from a
ghostscript text extraction of the arXiv PDF.

* **Definition 2.5.**  An inductive system `(A_m; α_m^n)` is called admissible
  if the natural map `T(A_m; α_m^n) → ΣA_∞` from the mapping telescope is
  invertible in KK.
* **Proposition 2.6.**  "We have `lim(A_m; α_m^n) = ho-lim(A_m; α_m^n)` for
  admissible inductive systems."  The proof produces an exact triangle
  `⊕ A_m --(id − S)--> ⊕ A_m → A_∞ → Σ ⊕ A_m`, where `S` is the shift.
* **Lemma 2.7.**  "An inductive system `(A_m; α_m^n)` is admissible if there
  exist equivariant completely positive contractions `φ_m : A_∞ → A_m` such that
  `α_m^∞ ∘ φ_m : A_∞ → A_∞` converges in the point norm topology towards the
  identity."

We use the trivial group and a one-point space.

**Step 1: admissible.**  Put `A_m = C ⊗ M_(p^m)` with connecting maps
`x ↦ x ⊗ 1_p`, so `A_∞ = C ⊗ M_(p^∞)`.  Let `E_m : M_(p^∞) → M_(p^m)` be the
trace-preserving conditional expectation and `φ_m = id_C ⊗ E_m`.  These are
completely positive contractions, and `(α_m^∞ ∘ φ_m)(x) → x` for every `x`:
exactly on the algebraic tensor products, and by uniform contractivity on the
closure.  Lemma 2.7 applies.

**Step 2: Milnor sequence.**  Apply `KK^*(−, D)` to the triangle of
Proposition 2.6.  KK is countably additive in the first variable, so
`KK^*(⊕ A_m, D) = ∏ KK^*(A_m, D)`.  The long exact sequence becomes
`0 → lim^1 KK^(*+1)(A_m, D) → KK^*(A_∞, D) → lim KK^*(A_m, D) → 0`.
The kernel and cokernel of `id − S^*` on the product are `lim` and `lim^1`.

**Step 3: the tower is a tower of isomorphisms.**  Under the Morita
identifications `KK^*(A_m, D) ≅ KK^*(C, D)`, the connecting map
`x ↦ x ⊗ 1_p` induces multiplication by `p`.  By
`o2-zp-crossed-products-invert-p-in-kk`, `p · [id_C]` is a unit of `KK(C, C)`,
so multiplication by `p` is bijective on `KK^*(C, D)`.  A tower of bijections has
`lim^1 = 0`, and its `lim` maps isomorphically onto the first term.  Hence
`ι^* : KK^*(C ⊗ M_(p^∞), D) → KK^*(C, D)` is bijective for every separable `D`.
By Yoneda, `[ι]` is invertible: take `D = C` to get `y` with `ι^* y = [id_C]`,
then use injectivity at `D = C ⊗ M_(p^∞)`.  This proves item 1.

**Step 4: item 2.**  For outer `α`, `C` is a unital Kirchberg algebra (simple,
purely infinite, nuclear, separable), and so is `C ⊗ M_(p^∞)`.  `ι` is unital,
so `[ι]` carries `[1_C]` to `[1]`.  Kirchberg--Phillips, KK form, no UCT: some
isomorphism `C → C ⊗ M_(p^∞)` induces `[ι]`.

**What this repairs.**  In Barlak--Li II Theorem 4.16, (i) ⟹ (ii), statement (i)
is applied to `O_2 ⋊_α Z_p`.  Step 3 shows that the algebra lies in the class
statement (i) quantifies over, for every action and with no UCT.
