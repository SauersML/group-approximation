---
rg: 2
id: exotic-c2-tilde-simple-kazhdan-lattices-are-not-left-orderable
kind: claim
title: The simple torsion-free Kazhdan lattice of Titz Mite–Witzel on an exotic C~_2 building is not left-orderable, nor are its thickness-4 companions
distinct_from:
  higher-rank-p-adic-lattices-are-not-left-orderable: that imports Deroin–Hurtado for lattices in algebraic p-adic groups; these lattices act on exotic C~_2 buildings and are not residually finite, hence (Malcev) not linear over any field, so no import applies. The proof is a finite certificate on a product-of-trees subgroup
  irreducible-tree-product-lattices-are-not-left-orderable: that is the open general statement for products of trees; this settles two explicit irreducible instances (Radu's and Janzen–Wise's square complexes) by computation, and uses them only as subgroups
artifacts:
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/bmw_sat.py
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/bmw_sat.out
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/radu_sat.py
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/radu_sat.out
---

**ESTABLISHED (computation with a complete rewriting system, plus a literature embedding).**

**Statement.**

1. Let `S_R` be Radu's four-vertex square complex and `S_JW` the Janzen–Wise square complex
   (Titz Mite–Witzel, *Non-residually finite C~_2-lattices*, arXiv:2509.05054, Examples
   `SquareRadu` and `SquareJanzenWise`). The torsion-free irreducible lattices
   `π_1(S_R) ≤ Aut(T_3) × Aut(T_3)` and `π_1(S_JW) ≤ Aut(T_4) × Aut(T_4)` are not left-orderable.
2. Hence the following groups are not left-orderable. Each is a torsion-free uniform lattice on an
   exotic building of type `C~_2`, so it has property (T) (TMW, Main theorem).
   - `Γ^2_1 = π_1(Y^2_1)`, thickness 3. By TMW (Main theorem and the paragraph after it) `Γ^2_1`
     is its own finite residual and is not residually finite; by their Corollary (with
     Lécureux–Witzel, Theorem A) the finite residual is simple. So `Γ^2_1` is a simple Kazhdan
     CAT(0) group.
   - `Γ^3_k = π_1(Y^3_k)` for `k = 1, 2, 3, 4`, thickness 4.
   - Every group containing one of these, for example the extensions `Γ̄^q_k` and
     `Aut(X^2_1) = Γ̄^2_1`.

**Why this matters for Navas's Question 3.** A natural hope for an infinite left-orderable
Kazhdan group is a lattice that Deroin–Hurtado cannot reach: exotic, non-linear, and not
residually finite. `Γ^2_1` is one of the first known simple CAT(0) groups with property (T)
(TMW 2025). This claim removes it and the four thickness-4 lattices as witnesses. The mechanism
is general: a building lattice containing, through a locally convex subcomplex, an irreducible
product-of-trees lattice inherits every obstruction to left orders from that sublattice.

**Proof shape** (full proof in `exotic-c2-tilde-kazhdan-lattices-not-left-orderable-proof`).

1. *Word problem.* TMW Propositions `gamma33_pres` (Radu) and `JanzenWise` give
   `Γ_R = ⟨a,b,c,x,y,z | a^2,…,z^2, axax, ayay, azbz, bxbx, bycy, cxcz⟩` and
   `Γ_JW = ⟨a,b,x,y | axay, ax^{-1}by^{-1}, ay^{-1}b^{-1}x^{-1}, bxb^{-1}y^{-1}⟩`, the BMW groups
   of the two complexes. The relators give a bijection `hv = v'h'` on (horizontal, vertical)
   letter pairs. Free cancellation plus `hv → v'h'` is terminating, and all its critical pairs
   resolve (24 for Radu, 40 for Janzen–Wise). So every element has a unique normal form
   (reduced vertical word)(reduced horizontal word).
2. *The subgroups.* By TMW §2 (BMW-complexes), `π_1(S) = Γ^+` is the type-preserving subgroup,
   the kernel of `Γ → ⟨σ_A, σ_X⟩ ≅ Z/2 × Z/2`, horizontal letters to `σ_A`, vertical to `σ_X`:
   normal forms with even vertical and even horizontal length.
3. *Positive cone SAT.* One variable per nontrivial element of `π_1(S) ∩ B_r`, clauses
   `p_g ⊕ p_{g^{-1}}` and `p_g ∧ p_h ⇒ p_{gh}` whenever `gh ∈ B_r`. Unsatisfiable; CaDiCaL 1.5.3
   and Glucose 4 agree:
   - `π_1(S_R)` on `B_6`: 576 subgroup elements, 38 784 clauses.
   - `π_1(S_JW)` on `B_4`: 384 elements, 15 000 clauses.
4. *Embedding.* TMW, proof of Theorem `main_2` (Part 1) and §7: a subdivision of `S_R` is a
   locally convex subcomplex of `Y^2_1`, and a subdivision of `S_JW` one of each `Y^3_k`. By their
   Lemma `locally_convex` (Bridson–Haefliger II.4.14), `π_1(S_R) ↪ Γ^2_1` and
   `π_1(S_JW) ↪ Γ^3_k`. Left-orderability passes to subgroups.

**Calibration.** The same script builds the reducible BMW groups on the same letters with all
squares commuting. Their kernels are finite-index subgroups of a product of two free products
of cyclic groups, namely `F_2 × F_2` (Radu letters) and a finite-index subgroup of `F_2 × F_2`
(Janzen–Wise letters), which are left-orderable. Those instances are satisfiable on `B_6` and
`B_4`, with identical variable and clause counts. The independent script `radu_sat.py` gives
the same answers for Radu, and also UNSAT on `B_8` and for the other torsion-free index-4
kernel `K2`.

**Scope.**

- Covers only lattices containing `π_1(S_R)` or `π_1(S_JW)`.
- For `q = 3` the *simple* finite residuals `Γ̌^3_k` have index 4 or 8 in `Γ^3_k`. They meet
  `π_1(S_JW)` in a normal subgroup of 2-power index at most 8, which this certificate does not
  cover by itself. Those subgroups are handled in
  `simple-titz-mite-witzel-kazhdan-groups-are-not-left-orderable`.
- General lattices on exotic `C~_2` buildings are not covered.
