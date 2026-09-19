---
rg: 2
id: finite-field-polynomial-growth-hosts-bound-commuting-rank
kind: claim
title: Over a finite field, s+1 commuting operators of bounded propagation on spaces of growth r^s are algebraically dependent; so every gauge-homogeneous F_q[Z^4] embedding in B_Ω ⊗ L_∂ dies in the gauge core
distinct_from:
  algebraic-core-gradings-bound-homogeneous-laurent-rank: that needs the units homogeneous for the full Z^3-grading (lattice plus gauge), or a locally-matrix-over-commutative host. This needs gauge-homogeneity only; the B_Ω-components are arbitrary, and B_Ω is a Z^2-SFT crossed product, which is not locally matrix over commutative algebras.
  f2-z4-embeds-in-z2-sft-boundary-product-hosts: that is the open fork. This kills one class of candidate YES constructions for it and does not decide it.
  leavitt-commuting-units-are-algebraically-dependent: that concerns the exponential-growth tree column of L(1,2), where the counting below fails. This concerns polynomial-growth hosts and the gauge core.
---

**ESTABLISHED (unreviewed)** by `finite-field-polynomial-growth-hosts-bound-commuting-rank-proof`.

Let `F` be a **finite** field. A *growth-`s` family* is a set of metric spaces
`(Y_α, d_α)` with a uniform bound `|B(y, r)| <= C (1 + r)^s` for every point `y` and
radius `r`. An operator `T` on `F^(Y_α)` (finitely supported functions) has
*propagation `<= b`* if `T e_y ∈ span{e_z : d_α(y, z) <= b}` for every `y`.

**Theorem A (annihilator counting).** Let `R` be a unital `F`-algebra with a
faithful family of unital representations `π_α : R -> End_F(F^(Y_α))`, indexed by a
growth-`s` family. Let `x_1, …, x_m ∈ R` commute, with `m >= s + 1`, and suppose each
`π_α(x_i)` has propagation `<= b`, with `b` independent of `α` and `i`. Then some
`0 != q ∈ F[t_1, …, t_m]` has `q(x_1, …, x_m) = 0`.

Hence `R` contains no polynomial ring `F[x_1, …, x_{s+1}]`, unital or not, and no
Laurent ring `F[Z^{s+1}]`. Every finitely generated commutative subalgebra has
Krull dimension `<= s`.

**Corollary B (hosts).** Let `Γ` be finitely generated with `|B_Γ(r)| <= C(1 + r)^s`,
acting on a compact totally disconnected space `X`. Then the following contain no
`s + 1` commuting algebraically independent elements:
- `LC(X, F) ⋊ Γ`, and its matrix algebras and corners;
- `(LC(X, F) ⋊ Γ) ⊗ D` for every unital locally finite `F`-algebra `D`.

In particular, for every `Z^2`-Cantor system `Ω`, the algebra `B_Ω ⊗ L(E_d)_0` has
commuting rank `<= 2`. Here `B_Ω` need not be SFT, free or minimal, and
`L(E_d)_0` is the gauge core.

**Corollary C (gauge-homogeneous kill).** Put `H = B_Ω ⊗ L_∂ ≅ B_Ω ⊗ L(E_d)` over
`F`, `Z`-graded by the gauge degree of the second factor. Let `φ : F[Z^4] -> H` be a
unital embedding, or an embedding into a corner `eHe` with `e` of gauge degree `0`.
- The group elements `g ∈ Z^4` with `φ(g)` gauge-homogeneous form a subgroup of rank
  `<= 3`.
- In particular, `φ` cannot send four independent elements of `Z^4` to
  gauge-homogeneous units.

This holds whatever the `B_Ω`-components are: arbitrary finite sums `Σ f_a δ_a`,
inhomogeneous in the `Z^2`-grading.

**General form.** Let `L` be graded by an abelian group of torsion-free rank `r`,
with unital locally finite core. Let `B` be as in Corollary B, with growth `s`.
Then commuting units of `B ⊗ L` that are homogeneous in `L` generate no Laurent ring
of rank `> r + s`.

**Why it matters.** For the `Z^4` fork, and hence for (E) =
`decidable-algebras-embed-in-z2-sft-boundary-product-hosts`:
- `algebraic-core-gradings-bound-homogeneous-laurent-rank` (A) killed units that are
  homogeneous for the *whole* `Z^3`-grading. This kills every construction whose
  units are homogeneous for the *gauge* grading alone. That includes all units of
  the form `Σ_k b_k ⊗ ℓ_k` with every `ℓ_k` of one gauge degree, and arbitrary
  `b_k ∈ B_Ω`.
- `z4-has-no-monomial-embedding-in-boundary-product-hosts` counts orbit points of
  monomial germs. Theorem A is a linear version of that count on the
  polynomial-growth factor: it counts dimensions, so it needs no monomiality.
- A YES answer must use a rank-`>= 1` subgroup of `Z^4` whose images are
  gauge-inhomogeneous, on top of the `Z^3`-inhomogeneity already forced.
- The symmetric reduction does **not** close. For units homogeneous in the
  `B_Ω`-lattice grading, the degree-0 sublattice has rank `>= 2` and lands in
  `LC(Ω) ⊗ L_∂`, locally `M_N(L_∂)`. So that case is exactly mechanism (i): a
  rank-2 Laurent ring in matrices over `L(1,2)`, which is
  `leavitt-commuting-units-are-algebraically-dependent`.

**Precise invariant and where every member dies.**
- Invariant: the rank of the gauge-degree-0 sublattice, which is `>= 4 - 1 = 3`.
- It lands in `B_Ω ⊗ L(E_d)_0 ⊆` a directed union of `M_N(B_Ω)`. This acts on
  `Z^2 × [N]` with balls of size `N(2r + 1)^2`.
- Degree-`<= K` polynomials in 3 variables span `binom(K+3, 3) ~ K^3/6`. That
  exceeds `N(2bK + 1)^2`, so every basis vector has a nonzero annihilating polynomial.
- The product of *all* nonzero degree-`<= K` polynomials (finitely many, because
  `F` is finite) annihilates everything.

**Limits.**
- Theorem A is false over infinite fields: diagonal multiplication operators on
  `F^(Z)` with independent transcendental entries have propagation 0.
- It is false for exponential growth: one column of `L(1,2)` is a tree.
- So it says nothing about mechanism (i), and nothing about gauge-inhomogeneous
  constructions.
- For domains over arbitrary fields, a single faithful column (the Ore-domain
  column lemma posted on the swarm-0917 bus by w14-bh-pull) gives the field-free
  version of Corollary B for crossed products. Theorem A instead needs no domain
  hypothesis and covers non-groupoid bounded-propagation algebras.
