---
rg: 2
id: izumi-rokhlin-approximately-representable-duality
kind: claim
title: For finite abelian group actions, the Rokhlin property and approximate representability are dual, and outer strongly approximately inner Z_q-actions on O_2 are approximately representable
distinct_from:
  barlak-li-p-half-iff-zp-actions-fix-cartan: that characterizes the UCT half at a prime through Cartan subalgebras invariant under order-p automorphisms of O_2; this is the duality between Rokhlin and approximately representable actions that the ascent reformulation runs through.
artifacts:
  - research/artifacts/uct-o2-cyclic-actions-2026-09-12.md
---

**ESTABLISHED (literature).**  Barlak--Li, *Cartan subalgebras and the UCT
problem, II*, arXiv:1704.04939v2, read from the PDF on 2026-09-12.

1. **Definitions** (their Definitions 2.6, 2.7 and 4.13, after Izumi, *Finite
   group actions on C\*-algebras with the Rohlin property I*, Definitions 3.1
   and 3.6).  An action `α : Γ ↷ A` of a finite group on a separable
   C\*-algebra has the Rokhlin property if there is a unital equivariant
   \*-homomorphism `(C(Γ), σ) → (F_∞(A), α_∞)`, where `σ` is the translation
   action.  For `Γ` finite abelian, `α` is approximately representable if there
   is a unitary representation `u : Γ → F_∞(A^α) ⊆ F_∞(A^α, A)` with
   `α_γ(a) = u_γ a u_γ*` for all `a ∈ A`.  For unital `A`, `α` is strongly
   approximately inner if there are unitaries `u_n ∈ A^α` with
   `α = lim_n Ad(u_n)` pointwise in norm.
2. **Duality** (their Theorem 2.8, citing Izumi I, Duke Math. J. 122 (2004),
   Lemma 3.8, and Nawata, Trans. Amer. Math. Soc. 368 (2016), Proposition 4.4).  For `Γ` finite abelian, `A` separable and `α : Γ ↷ A`:
   `α` has the Rokhlin property iff the dual action `α̂` is approximately
   representable, and `α` is approximately representable iff `α̂` has the
   Rokhlin property.
3. **On `O_2`** (proof of their Corollary 4.15, citing Izumi I, Theorem 4.6).
   Every outer strongly approximately inner action `α : Z_q ↷ O_2` with `q` a
   prime power is approximately representable.

Proof: `izumi-rokhlin-approximately-representable-duality-citation`.

Barlak--Li Remark 4.14(2): it is not known whether all `Z_2`-actions on `O_2`
are strongly approximately inner.
