---
rg: 2
id: no-a3-b3-and-cyclic-type-artin-wp-citation
kind: route
title: Import the rewriting algorithm without A_3 or B_3 subdiagrams and the Garside structure on cyclic-type Artin groups times Z
target: no-a3-b3-and-cyclic-type-artin-groups-have-solvable-wp
requires: []
---

This is a citation import, together with a written check that class (1) satisfies the
hypothesis of the imported theorem under every reading. Both sources were read on
2026-09-16 from their arXiv LaTeX sources.

## Part (1)

**Source.** R. Blasco-García, M. Cumplido, D. F. Holt, R. Morris-Wright and S. Rees,
*Rewriting in Artin groups without A_3 or B_3 subdiagrams*, arXiv:2412.12195v2.
- **Parts read:** the abstract, Theorem 1.1, the statement of the detailed main theorem
  in the proof section, and Example "n_atleast5" with the remarks that cite it.
- **Not read:** the proofs.

**Verbatim.**
- Theorem 1.1: "Let G be an Artin group defined over its standard generating set S for
  which the associated Coxeter diagram contains no A_3 or B_3 subdiagram; in other words,
  no subset {x,y,z} of the standard generating set for G satisfies the relations
  xyx=yxy, xz=zx, (y,z)_n = (z,y)_n with n=3 or 4. Then there is a system of length
  preserving rewrite rules which, together with free reduction, can be used to reduce any
  word over S to a geodesic word in G, in quadratic time."
- Detailed theorem, same hypothesis: "There is a process that, given an input word
  w:= x_1⋯x_n, runs in quadratic time to find geodesic representatives v_0,⋯,v_n in W of
  successive prefixes of w, in each case by applying an RRS of τ-moves to the word
  v_{i−1}x_i, and hence finding a geodesic representative v_n for w, and thereby solving
  the word problem in G." Here `W` is a set of words defined in the paper.
- Usage in the proofs: "a (2,3,3) triangle (A_3 subdiagram)" and "our hypothesis that
  the Coxeter diagram has no (2,3,4)-triangles".

**Check of the hypothesis.** Assume there are no pairwise distinct `x, y, z` with
`m_xy = 3`, `m_xz = 2` and `m_yz ∈ {2, 3, 4}`. We show that no 3-subset `{x, y, z}` of `S`
meets the excluded condition, under either reading of it.

- *Diagram reading.* An `A_3` or `B_3` subdiagram on `{x, y, z}` means that for some
  labelling `m_xy = 3`, `m_xz = 2` and `m_yz ∈ {3, 4}`. The assumption excludes this.
- *Relations reading.* Suppose `xyx = yxy`, `xz = zx` and `(y,z)_n = (z,y)_n` hold in `G`
  with `n = 3` or `4`. They then hold in the Coxeter group `W_Γ`, where `x`, `y` and `z`
  are involutions.
  - First, `(xy)^3 = (xyx)(yxy) = (xyx)(xyx) = 1`.
  - Second, `(xz)^2 = 1`.
  - If `n = 3`, then `(yz)^3 = 1` in the same way.
  - If `n = 4`, then `(yz)^4 = (yzyz)(yzyz) = (zyzy)(yzyz) = 1`.
  - By the lemma below, the order of `st` in `W_Γ` is exactly `m_st`. Hence `m_xy = 3`,
    `m_xz = 2`, and `m_yz = 3` or `m_yz ∈ {2, 4}`. The assumption excludes this.

**Lemma.** For distinct `s, t ∈ S`, the element `st` of `W_Γ` has order `m_st`, and
infinite order when `m_st = ∞`.

*Proof.*
1. Let `V` be the real vector space with basis `(e_s)_{s ∈ S}`.
   - Define the bilinear form `B(e_s, e_t) = −cos(π/m_st)`, with `B(e_s, e_s) = 1` and
     `B = −1` when `m_st = ∞`.
   - Define `σ_s(v) = v − 2B(e_s, v) e_s`. Then `σ_s² = 1`.
2. Fix `s ≠ t` with `m = m_st < ∞`, and let `P = span(e_s, e_t)`.
   - The Gram matrix of `B` on `P` has diagonal entries 1 and determinant
     `sin²(π/m) > 0`. So `B|_P` is positive definite, and `V = P ⊕ P^⊥`.
   - Both `σ_s` and `σ_t` fix `P^⊥` pointwise and preserve `P`.
   - On the Euclidean plane `(P, B)` they are reflections in the lines `e_s^⊥` and
     `e_t^⊥`. Since `B(e_s, e_t) = −cos(π/m)`, these lines meet at angle `π/m`.
   - So `σ_sσ_t` is a rotation of `P` by `2π/m`. It has order exactly `m` on `V`.
3. If `m_st = ∞`, set `u = e_s + e_t`. Then `B(u, e_s) = B(u, e_t) = 0`, so `σ_s` and
   `σ_t` fix `u`.
   - We have `σ_t(e_s) = 2u − e_s` and `σ_s(e_s) = −e_s`.
   - So `σ_sσ_t(e_s) = e_s + 2u`, and by induction `(σ_sσ_t)^k(e_s) = e_s + 2ku`, which
     is not `e_s` for `k ≠ 0`.
4. By step 2, every defining relation of `W_Γ` holds for the `σ_s`, so `s ↦ σ_s` defines a
   homomorphism `W_Γ → GL(V)`.
   - The image of `st` has order `m_st`, or infinite order when `m_st = ∞`. So the order
     of `st` is at least `m_st`.
   - When `m_st < ∞`, the relation `(st)^{m_st} = 1` holds in `W_Γ`, so the order is at
     most `m_st`. ∎

**Conclusion for (1).** By Theorem 1.1 and the detailed theorem, there is an algorithm
computing from a word `w` a geodesic word for the same element. `w` represents `1` if and
only if that geodesic word is empty.

## Part (2)

**Source.** T. Haettel and J. Huang, *New Garside structures and applications to Artin
groups*, arXiv:2305.11622v2.
- **Parts read:** the introduction, the subsection listing references for Theorem D, and
  the definition of cyclic-type Coxeter groups.
- **Not read:** the proof that cyclic-type groups satisfy the Garside criterion, and the
  cited sources behind Theorem D.

**Verbatim.**
- "We say an Artin group is of cyclic type if its Dynkin diagram is a cycle without
  ∞-labeled edges, and any proper parabolic subgroup is spherical."
- The Dynkin diagram convention: "vertices that are not joined by an edge commute, and we
  drop the label 3 from edges".
- Theorem E: "Suppose A_Γ is of cyclic type. Then A_Γ×Z is a Garside group." This is
  source label `thm:main1`. The letters here and in Theorem D are worked out from the
  LaTeX counters, not from a compiled PDF.
- Theorem D, source label `thm:consequences_product_Z_garside`: "Assume that G is a group
  such that G×Z is Garside. Then the
  following hold: […] The group G is biautomatic, and in particular: […] G has solvable
  word and conjugacy problems."
  - The references subsection says this item "is a consequence of [mosher_biautomatic]".
- After the gluing theorem: "All of these consequences are new for this class, including
  the solvability of word problem."

**Conclusion for (2).**
- In the Dynkin diagram, commuting pairs (`m_st = 2`) are the non-edges, so the definition
  above is the definition in the claim.
- A proper parabolic subgroup is spherical when `W_T` is finite.
- By Theorem E, `A_Γ × Z` is Garside. Theorem D with `G = A_Γ` then shows that `A_Γ` has
  solvable word problem. ∎
