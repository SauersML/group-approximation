---
rg: 2
id: finite-abelian-actions-have-invariant-masas
kind: claim
title: Under an action of a finite abelian group, every maximal invariant abelian C*-subalgebra is a masa, so invariant masas exist; an A_4-action on M_2 has none
distinct_from:
  no-masa-of-o2-is-normalized-by-fixed-point-unitaries: item 5 there proves that maximal invariant abelian subalgebras are masas only for automorphisms of order two, where the eigenparts are self-adjoint; this proves it for every finite abelian group, including Z_3, where the eigenparts are not self-adjoint and their normality has to be proved, and it shows that the abelian hypothesis cannot be dropped.
  o2-z3-actions-fix-a-cartan-subalgebra: that asks for an invariant Cartan subalgebra of O_2, which needs regularity and a faithful conditional expectation; this supplies only the maximal abelian part, for every action of every finite abelian group on every C*-algebra.
  o2-z2-actions-fix-a-cartan-subalgebra: that is the Cartan question at p = 2; this is the masa part, uniformly over all finite abelian groups.
---

**ESTABLISHED (derivation, this repository; elementary, no priority claim).**
Let `G` be a finite abelian group with dual group `Ĝ`, and let
`α : G → Aut(A)` be an action on a C\*-algebra `A`. An abelian C\*-subalgebra
`C ⊆ A` is *invariant* if `α_g(C) ⊆ C` for all `g ∈ G`. A *masa* is a maximal
abelian C\*-subalgebra of `A`. No simplicity, nuclearity, unitality or
outerness is assumed.

1. **Maximal invariant abelian subalgebras are masas.** Let `D` be maximal
   among the invariant abelian C\*-subalgebras of `A`, and put `B = D' ∩ A`.
   - `B^G ⊆ D`.
   - If `b ∈ B` and `α_g(b) = χ(g) b` for all `g`, for some `χ ∈ Ĝ`, then `b`
     is normal and `b ∈ D`.
   - Hence `D' ∩ A = D`, and `D` is a masa. If `A` is unital, `1 ∈ D`.
2. **Existence and extension.** Every invariant abelian C\*-subalgebra of `A`
   is contained in an invariant masa. In particular:
   - every action of a finite abelian group has an invariant masa;
   - every masa `D_0` of the fixed-point algebra `A^G` equals `D ∩ A^G` for
     some invariant masa `D` of `A`.
3. **The abelian hypothesis cannot be dropped.** Let `X, Y, Z ∈ M_2` be the
   Pauli matrices and `U = (1 − iX − iY − iZ)/2`. Then `Ad X`, `Ad Z` and
   `Ad U` generate a subgroup of `Aut(M_2)` of order `12`, isomorphic to
   `A_4`. The only invariant abelian C\*-subalgebras are `{0}` and `C1`, so
   this action has no invariant masa. Its abelian subgroups do have invariant
   masas, as item 2 requires: `span{1, Z}` is invariant under
   `{id, Ad X, Ad Y, Ad Z} ≅ Z_2 × Z_2`, and `span{1, X + Y + Z}` is fixed
   pointwise by `⟨Ad U⟩ ≅ Z_3`.

Proof: `finite-abelian-actions-have-invariant-masas-proof`. Numerical sanity
check (item 3 matrices, and the greedy construction of item 1 for several
`Z_3`, `Z_3 × Z_3` and `Z_2 × Z_4` actions on matrix algebras):
`experiments/finite-abelian-invariant-masas-2026-09-16/invariant_masa_check.py`.

**Bearing on `o2-z3-actions-fix-a-cartan-subalgebra`.**
- **The masa part is free at `p = 3`.** Item 5 of
  `no-masa-of-o2-is-normalized-by-fixed-point-unitaries` was proved only at
  `p = 2`. By items 1 and 2 it holds at `p = 3` too. For every automorphism
  `α` of `O_2` with `α^3 = id`, whether or not it is outer or strongly
  approximately inner, `α`-invariant masas exist. Every `α`-invariant abelian
  C\*-subalgebra extends to one, and so does every masa of `O_2^α`.
- **What remains.** A Cartan subalgebra of a unital algebra is a masa that is
  regular and carries a faithful conditional expectation. So the target asks
  exactly for an `α`-invariant masa that is regular and admits a faithful
  conditional expectation, and maximality is never the obstruction. The
  extensions in item 2 give no control over normalizers, so they do not
  transfer regularity from `O_2^α` to `O_2`.
- **What an argument must use.** By item 3, no construction that works for
  arbitrary finite group actions on arbitrary C\*-algebras yields invariant
  masas, let alone invariant Cartan subalgebras. So an approach to the target
  must use that `Z_3` is abelian, for instance through its spectral
  subspaces, or else features specific to `O_2` and to the action. Item 3
  lives on `M_2`; whether every finite group action on `O_2` has an
  invariant masa is not addressed here.
