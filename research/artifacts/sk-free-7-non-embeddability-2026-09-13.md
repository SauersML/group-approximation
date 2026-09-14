# sk-free-7: embeddings between the groups G_X (2026-09-13)

Lane sk-free-7 (wave 10, free lane). Status: complete proofs, UNREVIEWED; queued with sk-verify-13.

G_X = EL_3(LC(X,F_2) ⋊ Z) for an infinite minimal subshift X, with the note's generators e_ij(s), s ∈ {1, u^{±1}} ∪ {e_a}.

## 0. Why this, and relation to the plan
The plan (`sk-free-7-plan-2026-09-13.md`) targets the exchange property and stable rank one of R_X. A bounded literature check this session found no citable theorem:
- Ara–O'Meara–Perera (Trans. AMS 356 (2004) 2067–2079) prove only that translation algebras over trees are exchange rings;
- Lolk (arXiv:1705.04494, source §6) obtains exchange for separated-graph algebras by degeneration to classical graph algebras with Condition (K), a graph-specific route;
- Camillo–Yu (Trans. AMS 347 (1995)): an exchange ring has stable range one iff every regular element is unit-regular. This is the reduction the plan would use.

That target stays open and the lane continues on it. On the way, two short results about *embeddings* between the G_X were found. Main has only isomorphism invariants, so these are new strengthenings.

## 1. Pairwise non-embeddable continuum (computability)
**Theorem 1** (`continuum-many-subshift-el-groups-pairwise-non-embeddable`). There are 2^{ℵ_0} Sturmian subshifts X such that the G_X are infinite, finitely generated, simple, Kazhdan and LEF, and no G_X is isomorphic to a subgroup of another.

*Proof.*
- (i) If H ↪ G are finitely generated, deg WP(H) ≤ deg WP(G): substitute fixed G-words for the generators of H. This is a many-one reduction.
- (ii) WP(G_X) ≡_T L(X), and L(X_α) ≡_T α for Sturmian X_α (`subshift-elementary-group-word-problem-degree`).
- (iii) There is a perfect set P of pairwise Turing incomparable reals (`turing-degrees-contain-continuum-antichains`; a complete finite-extension proof is in its route).
- (iv) For x ∈ P put α_x = 0.(x ⊕ c) with c computable and not eventually periodic. Then α_x ≡_T x and α_x is irrational.
- (v) An embedding G_{X_{α_x}} ↪ G_{X_{α_y}} would give x ≤_T y. ∎

**Credit.** The antichain is Sacks' construction:
- Terwijn, *On the structure of the Medvedev lattice*, arXiv:math/0606529, source l.458–460: "as in Sacks' construction of such an antichain in the Turing degrees \cite[p462]{Odifreddi}";
- the same source, l.1150–1152: "a set of pairwise Turing incomparable elements of ^ω2, which exists by a result of Sacks, cf. \cite{Odifreddi}";
- Odifreddi, *Classical Recursion Theory*, p. 462, as cited there. The page was not opened; VERIFY-PENDING with sk-verify-6.

The route into the antichain claim is self-contained (requires: []).

## 2. Complexity obstructs embeddings (dynamics)
**Theorem 2** (`positive-entropy-el-groups-avoid-low-complexity-hosts`). If G_X ↪ G_Y, then for some C and all k ≥ 1,

`p_X(k) < 7·p_Y(2001 C k^2)^4`.

*Proof.*
- **Monotonicity.** Along an embedding, L_X(r) ≤ L_Y(Cr). A local model of the Cr-ball of G_Y restricts to one of the r-ball of G_X; this is Step 2 of `recursive-lef-growth-hosts-miss-some-fp-rf-group-proof`.
- **The bounds of `subshift-elementary-group-lef-growth-complexity-bounds`.** L_X(r) ≥ 60^{p_X(⌈√(r/500)⌉)}, and log_2 L_Y(r) < 9 N_Y(4r+1)^2 ≤ 36 p_Y(4r+1)^4.
- **Combine** at r = 500k², using log_2 60 > 5.9. ∎

**Corollaries.**
- **(a) Entropy.** h(X) > 0 and log p_Y(n) = o(√n) give G_X ⊄ G_Y; in particular Y of polynomial complexity.
- **(b) Polynomial scales.** p_X(k) ≥ c k^α infinitely often and p_Y ≤ C′ n^β, with α > 8β, give G_X ⊄ G_Y.
- **(c) Strictness.** If Y is a factor of X (so G_Y ≤ G_X), h(X) > 0 and p_Y is polynomial, the inclusion is strict up to isomorphism: G_X embeds in no conjugate or isomorphic copy inside G_Y.

This strengthens the non-isomorphism consequence of `subshift-elementary-group-lef-growth-complexity-bounds` (p_X ≥ n^{4+ε} versus linearly recurrent) from isomorphism to embeddings. Theorem 2 is conditional on that node, which is unreviewed.

## 3. Model tests
- **Theorem 1.** Computable slopes are all Turing equivalent, and Theorem 1 claims nothing about them. Factor maps can embed one G into another (`lef-growth-of-subshift-el-groups-is-monotone-under-factors`), consistent with (i).
- **Theorem 2.** X = Y satisfies the inequality. Sturmian Y (p = n+1) with X of complexity ≥ k^9 infinitely often gives G_X ⊄ G_Y. Positive-entropy minimal subshifts exist (Grillenberger), so (a) is not vacuous.

## 4. Consequence for the note
Theorem 1 costs one clause and one citation in §3 (word problems): "continuum many pairwise nonisomorphic" becomes "continuum many, none isomorphic to a subgroup of another". The verbatim proposal is in `sk-free-7-proposal-2026-09-13.md`. Theorem 2 stays in Cairn.
