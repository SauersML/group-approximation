---
rg: 2
id: moutzouris-k0-killing-is-local
kind: claim
title: Killing a singular K_0-subgroup by a quasidiagonal embedding is equivalent to killing it asymptotically, reduces to finitely generated subgroups, and is local (Moutzouris)
distinct_from:
  moutzouris-qd-extensions-y-class: that is the extension theorem for the class Y; this imports the three permanence propositions of Section 3 used to prove it.
  brown-dadarlat-qd-extensions-and-k0-hahn-banach: that imports the Brown-Dadarlat equivalences for the whole class of nuclear quasidiagonal algebras; this imports single-algebra transfer statements.
artifacts:
  - research/artifacts/bk-radical-trace-step-part2-2026-09-13.md
---

**Established (literature).**  I. Moutzouris, arXiv:2112.03224v3, Section 3,
read from the PDF on 2026-09-13.

1. (Proposition 3.1)  Let `0 -> A⊗K -> E -> B -> 0` with `B` separable, nuclear
   and quasidiagonal, `A` MF and σ-unital, and `[η] = 0 ∈ Ext(B, A⊗K)`.  Then `E`
   is MF.
2. (Proposition 3.2)  Let `A` be separable, nuclear and quasidiagonal, and
   `G ≤ K_0(A)` singular.  If some faithful \*-homomorphism
   `ρ : A -> Π M_(k(n)) / ⊕ M_(k(n))` has `ρ_*(G) = 0`, then some faithful
   \*-homomorphism into a quasidiagonal algebra kills `G`.  The proof builds
   `0 -> A⊗K -> E -> ⊕_N C(T) -> 0` with boundary `G` from the UCT for
   `⊕_N C(T)` and never uses singularity.
3. (Proposition 3.3)  Let `A` be separable, unital, nuclear and quasidiagonal.
   If every finitely generated singular subgroup is killed by a faithful
   \*-homomorphism into a quasidiagonal algebra, then `A` has the K_0-embedding
   property.  The proof takes a diagonal sequence of models along an increasing
   exhaustion by finitely generated subgroups.
4. (Proposition 3.5)  If `A` is locally approximated by separable, nuclear,
   quasidiagonal algebras with the K_0-embedding property, then `A` has the
   K_0-embedding property.  The proof extends ucp models of the approximating
   unitised subalgebras to `Ã` by Arveson's theorem, and uses the embedding
   property only for the lifted subgroup on each approximant.
