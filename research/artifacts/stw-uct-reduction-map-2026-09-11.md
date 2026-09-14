---
title: STW Problem II (the UCT problem) - verified reduction map, new results, view and plan (stw-uct lane, 2026-09-11)
---

# Scope

Lane `stw-uct` owns `stw99-problem-ii-nuclear-uct`: do all separable nuclear
C\*-algebras satisfy the Rosenberg--Schochet UCT?  This artifact records which
sources were read, what was wired into Cairn, the two derivations proved in this
lane, the side chosen and why, and the next steps.

# 1. Sources read, and exactly what was taken from each

Read from the PDF on 2026-09-11:

* **Brown--Browne--Willett--Wu, *The UCT problem for nuclear C\*-algebras* (2020
  survey).**  Theorem 2.1 (Kirchberg algebras), Theorem 2.2 (trivial K-theory,
  i.e. `O_2`), Theorem 2.4 (RFD algebras, Dadarlat), Theorem 2.6 and remark
  (tracially AF algebras with the K-theory of `Q`), Theorem 2.8 (simple unital
  algebras of nuclear dimension one), Theorem 3.4 (Cartan implies UCT),
  Theorem 3.6 (Dadarlat local UCT), Section 3.1 (permanence), Theorem 4.4
  (weak approximate ideal structures), Theorem 5.1 (Künneth under uniform
  approximate ideal structures), and the open problems of Section 4.1.
* **Dadarlat, *Some remarks on the universal coefficient theorem in KK-theory*
  (2003).**  Theorem 1.1 (local UCT), Theorem 1.2 (UCT ⟺ TAF rigidity at `Q` ⟺
  a finite-dimensional approximation property of trivial-K RFD algebras),
  Proposition 2.1 (permanence), Lemma 2.4.
* **Willett--Yu, arXiv:2104.10766v4.**  Definition 1.1 (decomposability),
  Theorem 1.2 (decomposability over nuclear UCT algebras gives nuclearity and
  the UCT), Definition 1.3 (complexity hierarchy).
* **Jaime--Willett, arXiv:2205.04704v2.**  Theorem 1.2 (second part: UCT for all
  nuclear algebras ⟺ every unital trivial-K Kirchberg algebra decomposes over
  finite-dimensional algebras), Definition 1.3, Theorem 1.4 (weak complexity
  rank ≤ 1 ⟺ nuclear dimension ≤ 1 and real rank zero, simple unital case),
  Theorem 1.5 (complexity rank ≤ 1 ⟹ `K_1` torsion free), and the abstract's
  computation for UCT Kirchberg algebras.
* **Barlak--Li, arXiv:1511.02697v3 (Adv. Math. 316 (2017)).**  Theorem 1.1,
  Corollary 1.2, Theorem 1.4, Theorem 1.5, Proposition 1.6, Theorem 1.7,
  Theorem 1.8, and the introduction's reduction to `O_2 ⋊ Z_p` for outer
  actions.

Abstracts only, cited in prose and never as the source of a Cairn claim:
Barlak--Li II (arXiv:1704.04939); Barlak--Szabó, *Approaching the UCT problem via
crossed products of the Razak--Jacelon algebra* (GGD 14 (2020), arXiv:1712.00823);
Evington--Sibbel, principal groupoid models for stable UCT Kirchberg algebras
(arXiv:2605.30147); Tikuisis--White--Winter, Ann. of Math. 185 (2017)
(arXiv:1509.08318).

**Correction made to the root node.**  Its prose said Barlak--Li handled twisted
groupoids "with torsion-free-quotient hypotheses".  Their printed Theorem 1.1
has no such hypothesis: nuclear reduced algebras of twisted étale, Hausdorff,
locally compact, second countable groupoids satisfy the UCT.

# 2. What was wired

Established literature claims (each with a `-citation` route):
`uct-class-permanence-properties`,
`kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras`,
`willett-yu-decomposability-forces-uct`,
`kirchberg-algebras-have-weak-complexity-rank-one`,
`weak-complexity-rank-one-does-not-imply-rank-one`,
`dadarlat-tracially-af-universal-uhf-reduction`,
`barlak-li-cartan-subalgebras-force-uct`,
`barlak-li-two-half-iff-z2-actions-fix-cartan`.

Open claims, each with Attempts:
`trivial-k-theory-kirchberg-algebras-are-o2`,
`trivial-k-kirchberg-algebras-have-complexity-rank-one`,
`tracially-af-rational-k0-algebras-are-universal-uhf`,
`uct-for-two-infinity-absorbing-nuclear-algebras`,
`uct-for-three-infinity-absorbing-nuclear-algebras`,
`o2-z2-actions-fix-a-cartan-subalgebra`,
`nuclear-algebra-without-uct-exists` (the negation, listed in the root's
`refuted_by`).

Routes into the root: `stw99-ii-via-trivial-k-kirchberg-algebras`,
`stw99-ii-via-complexity-rank-one`, `stw99-ii-via-tracially-af-rational-k0`,
`stw99-ii-via-coprime-uhf-absorbing-cases`.  Into the half at 2:
`uct-two-half-via-z2-actions-on-o2`.  Out of the root:
`stw99-ii-implies-ix1`.

Dead routes with established invalidators:
`trivial-k-rank-one-via-weak-rank-upgrade`, killed by
`weak-complexity-rank-one-does-not-imply-rank-one`, and
`non-uct-witness-from-cartan-respecting-automorphism`, killed by
`cartan-respecting-o2-automorphisms-give-uct-crossed-products`.

# 3. New results in this lane

**(R1) Coprime UHF splitting and the UCT-support filter**
(`coprime-uhf-stabilizations-detect-uct`, full proof in its `-proof` route).
For separable nuclear `A` and coprime supernatural `s, t ≠ 1`:
`A ∈ UCT ⟺ A ⊗ M_s, A ⊗ M_t ∈ UCT`.  The mechanism is the coprime
dimension-drop algebra `Z_{s,t}`, which has the K-theory of `C` and satisfies the
UCT, hence is KK-equivalent to `C`, together with the semisplit extension
`0 → S(A ⊗ M_s ⊗ M_t) → A ⊗ Z_{s,t} → A ⊗ M_s ⊕ A ⊗ M_t → 0` and two-out-of-three.
Consequence: `𝒫(A) = {P : A ⊗ M_{P^∞} ∈ UCT}` is upward closed and closed under
finite intersections, `A ∈ UCT ⟺ ∅ ∈ 𝒫(A)`, and a non-UCT algebra becomes
UCT after absorbing `M_{p^∞}` for at most one prime `p`.  No source read states
this; it is likely folklore and carries no priority claim.

Combined with Barlak--Li Theorem 1.8, Problem II is equivalent to the
conjunction of:

* every outer strongly approximately inner `Z_2`-action on `O_2` leaves a
  Cartan subalgebra invariant;
* the UCT for separable nuclear `M_{3^∞}`-absorbing algebras.

**(R2) Cartan-respecting automorphisms of `O_2`**
(`cartan-respecting-o2-automorphisms-give-uct-crossed-products`).  Finite-order
gauge automorphisms `λ_u` with `u` in the unitary normalizer of `D_2`, including
the Thompson group `V` of the Leavitt region, and transported tensor flips of
`O_2 ⊗ O_2` leave a Cartan subalgebra invariant.  So `O_2 ⋊ Z_p` satisfies the
UCT for all of them, by Barlak--Li Proposition 1.6.  This kills the tempting
negative route through the repository's native combinatorial automorphisms.

**(R3) Problem II ⟹ Problem IX(1)** (`stw99-ii-implies-ix1`), through the
AF-embedding theorem already in the graph.  Any non-quasidiagonal separable
nuclear algebra with a faithful trace, or any simple nuclear stably finite
non-quasidiagonal algebra through `stw99-ix1-implies-vii-simple`, is a UCT
counterexample.

# 4. The side chosen, and why

**Positive: all separable nuclear C\*-algebras satisfy the UCT.**

1. The only known mechanism for UCT failure, Skandalis's `C*_r(Γ)` for infinite
   hyperbolic Kazhdan `Γ`, is a failure of K-nuclearity.  Nuclear algebras are
   K-nuclear, so it cannot occur.
2. Every reduction ends in a class with rich local structure where one
   coherence step is missing, not a K-theoretic obstruction.  All Kirchberg
   algebras have weak complexity rank one, and only the intersection algebra is
   missing for trivial K-theory.  Uniform approximate ideal structures already
   give the Künneth formula (BBWW Theorem 5.1).
3. A witness must avoid an unusually long list of structures (see
   `nuclear-algebra-without-uct-exists`): no Cartan subalgebra and no groupoid
   model, no decomposition over UCT algebras, a proper UCT-support filter, and,
   in the `O_2 ⋊ Z_p` form, no invariant Cartan subalgebra for the action.

This is a bet, not an argument.  No attempt here reaches a proof.

# 5. Plan

1. **Half at 2 through Izumi.**  Read Izumi, *Finite group actions on
   C\*-algebras with the Rohlin property I*, Theorem 4.8, and Barlak--Li
   Section 5.  Then attack `o2-z2-actions-fix-a-cartan-subalgebra` in the dual
   picture, where strongly approximately inner `Z_2`-actions correspond to
   Rokhlin actions on the crossed product.  Look for an invariant Cartan
   subalgebra built from a Rokhlin tower rather than from the classification.
2. **Half at 3.**  Check from the source whether Theorem 1.8 has an odd-prime
   analogue, which needs Izumi's classification for `Z_3`.  Wire it if it
   exists.
3. **Intersection algebra.**  For `trivial-k-kirchberg-algebras-have-complexity-rank-one`,
   read Jaime--Willett Section 5.1, the rank-one case after Enders.  Decide
   whether Enders's decompositions use the UCT only to classify, or also to
   build the intersection algebra.  If only to classify, the construction
   might be run directly on a trivial-K Kirchberg algebra.
4. Keep the negation node current as new obstructions are proved.

# 6. Neighbour lanes

`stw-bk` (Blackadar--Kirchberg) was told that II ⟹ IX(1) ⟹ VII for simple
algebras is now wired.  So a non-quasidiagonal simple nuclear stably finite
algebra refutes the UCT, while positive progress on VII says nothing about II.
