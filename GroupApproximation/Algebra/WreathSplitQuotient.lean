import GroupApproximation.Algebra.PermutationalWreath

/-!
# The split quotient of a permutational wreath product

**Section 53** of the dossier, in its structural form.  The wreath product
projects onto the acting group with kernel exactly the lamp subgroup, and the
projection is split by the canonical inclusion.  Composing that projection with
*any* injective representation of the acting group leaves the kernel unchanged.

For the dossier's concrete family this is what makes a single four-dimensional
rational representation realise the whole invisible kernel: the acting group
embeds in `GL₄(ℚ)`, so the composite has kernel exactly the lamp subgroup, which
for a perfect lamp group is the entire MF radical.
-/

namespace GroupApproximation

universe u v w

open SemidirectProduct

variable {K : Type u} [Group K] {G : Type w} [Group G] {X : Type v}
variable [MulAction G X]

/-- The wreath projection has kernel exactly the lamp subgroup. -/
theorem ker_rightHom_eq_lampRange :
    (rightHom : Wreath K G X →* G).ker
      = (inl : Lamp K X →* Wreath K G X).range :=
  (range_inl_eq_ker_rightHom).symm

/-- The projection is split by the canonical inclusion. -/
theorem rightHom_comp_inr :
    (rightHom : Wreath K G X →* G).comp (inr : G →* Wreath K G X)
      = MonoidHom.id G :=
  SemidirectProduct.rightHom_comp_inr

/-- Postcomposing with an injective homomorphism does not change a kernel. -/
theorem ker_comp_of_injective {A B C : Type*} [Group A] [Group B] [Group C]
    (q : A →* B) (ρ : B →* C) (hρ : Function.Injective ρ) :
    (ρ.comp q).ker = q.ker := by
  ext a
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro h
    exact hρ (by rw [h, map_one])
  · intro h
    rw [h, map_one]

/-- **Section 53, structural form.**  A faithful representation of the acting
group, precomposed with the wreath projection, has kernel exactly the lamp
subgroup — no matter how small the representation is. -/
theorem ker_comp_rightHom_eq_lampRange {C : Type*} [Group C] (ρ : G →* C)
    (hρ : Function.Injective ρ) :
    (ρ.comp (rightHom : Wreath K G X →* G)).ker
      = (inl : Lamp K X →* Wreath K G X).range := by
  rw [ker_comp_of_injective _ _ hρ, ker_rightHom_eq_lampRange]

end GroupApproximation
