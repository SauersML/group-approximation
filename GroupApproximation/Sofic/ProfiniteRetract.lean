import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.ProfiniteClosure

/-!
# Retracts are profinitely closed

If `i : H → G` admits a homomorphic retraction and `G` is residually
finite, then `i(H)` is closed in the profinite topology of `G`.  The
separating quotient is explicit: separate

`i (r x)⁻¹ x`

in a finite quotient `q` of `G`, and use the product map
`x ↦ (q x, q (i (r x)))`.  The retract maps to the diagonal, while the
chosen point does not.

This form is useful for the paired-return cutter, whose centralizing edge is
a graph retract inside a residually finite free-by-free base.
-/

namespace GroupApproximation

noncomputable section

variable {G H : Type*} [Group G] [Group H]

/-- Transport permutations to a universe-zero finite model. -/
private def permTransport {X : Type*} {Y : Type} (e : X ≃ Y) :
    Equiv.Perm X →* Equiv.Perm Y where
  toFun p := (e.symm.trans p).trans e
  map_one' := by ext y; simp
  map_mul' p q := by ext y; simp

@[simp] private theorem permTransport_apply {X : Type*} {Y : Type}
    (e : X ≃ Y) (p : Equiv.Perm X) (y : Y) :
    permTransport e p y = e (p (e.symm y)) := rfl

/-- The image of a retract in a residually finite group equals its profinite
closure. -/
theorem profiniteClosure_range_eq_range_of_retraction
    [Group.ResiduallyFinite G]
    (i : H →* G) (r : G →* H)
    (hri : r.comp i = MonoidHom.id H) :
    profiniteClosure i.range = i.range := by
  apply le_antisymm
  · intro x hx
    by_contra hnot
    have hmove : (i (r x))⁻¹ * x ≠ 1 := by
      intro hmove
      have hxeq : x = i (r x) := by
        exact (inv_mul_eq_one.mp hmove).symm
      apply hnot
      exact ⟨r x, hxeq.symm⟩
    obtain ⟨N, hN⟩ :=
      Group.exists_finiteIndexNormalSubgroup_notMem ((i (r x))⁻¹ * x) hmove
    letI := N.isNormal'
    letI := N.isFiniteIndex'
    letI : Fintype (G ⧸ N.toSubgroup) := Fintype.ofFinite _
    let n := Fintype.card (G ⧸ N.toSubgroup)
    let e : (G ⧸ N.toSubgroup) ≃ Fin n := Fintype.equivFin _
    let Q := Equiv.Perm (Fin n)
    let q : G →* Q :=
      (permTransport e).comp (MulAction.toPermHom G (G ⧸ N.toSubgroup))
    let diagonalTest : G →* Q × Q :=
      q.prod (q.comp (i.comp r))
    have hqmove : q ((i (r x))⁻¹ * x) ≠ 1 := by
      intro hq
      apply hN
      have happ := congrArg (fun p : Equiv.Perm (Fin n) ↦
        p (e (QuotientGroup.mk (1 : G) : G ⧸ N.toSubgroup))) hq
      simp only [q, MonoidHom.coe_comp, Function.comp_apply, permTransport_apply,
        Equiv.symm_apply_apply, MulAction.toPermHom_apply,
        MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at happ
      have hquot :
          (QuotientGroup.mk ((i (r x))⁻¹ * x) : G ⧸ N.toSubgroup) =
            QuotientGroup.mk 1 := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at happ
        exact e.injective happ
      have hinv : (((i (r x))⁻¹ * x)⁻¹) ∈ N.toSubgroup := by
        simpa using (QuotientGroup.eq (s := N.toSubgroup)).mp hquot
      have hy : (i (r x))⁻¹ * x ∈ N.toSubgroup := by
        simpa only [inv_inv] using N.toSubgroup.inv_mem hinv
      exact FiniteIndexNormalSubgroup.mem_toSubgroup_iff.1 hy
    have hximage : diagonalTest x ∈ i.range.map diagonalTest :=
      hx (Q × Q) diagonalTest
    obtain ⟨z, hz, hzx⟩ := hximage
    have hirz : i (r z) = z := by
      obtain ⟨h, rfl⟩ := hz
      have hh := congrArg (fun f : H →* H ↦ f h) hri
      change i (r (i h)) = i h
      simpa using congrArg i hh
    have hfirst : q z = q x := congrArg Prod.fst hzx
    have hsecond : q (i (r z)) = q (i (r x)) := congrArg Prod.snd hzx
    rw [hirz] at hsecond
    have heq : q (i (r x)) = q x := hsecond.symm.trans hfirst
    apply hqmove
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  · exact le_profiniteClosure i.range

/-! ## Functorial consequences -/

variable {Q : Type*} [Group Q]

/-- Profinite closure is functorial under preimages. -/
theorem profiniteClosure_comap_le (L : Subgroup Q) (f : G →* Q) :
    profiniteClosure (L.comap f) ≤ (profiniteClosure L).comap f := by
  intro x hx
  rw [Subgroup.mem_comap]
  intro F _ _ psi
  have hximage := hx F (psi.comp f)
  obtain ⟨y, hy, hyx⟩ := hximage
  refine ⟨f y, Subgroup.mem_comap.mp hy, ?_⟩
  exact hyx

/-- The preimage of a profinitely closed subgroup is profinitely closed. -/
theorem profiniteClosure_comap_eq_of_closed (L : Subgroup Q) (f : G →* Q)
    (hL : profiniteClosure L = L) :
    profiniteClosure (L.comap f) = L.comap f := by
  apply le_antisymm
  · rw [← hL]
    exact profiniteClosure_comap_le L f
  · exact le_profiniteClosure (L.comap f)

/-- The diagonal in the square of a residually finite group is profinitely
closed. -/
theorem profiniteClosure_diagonal_range [Group.ResiduallyFinite Q] :
    let diagonal : Q →* Q × Q :=
      (MonoidHom.id Q).prod (MonoidHom.id Q)
    profiniteClosure diagonal.range = diagonal.range := by
  let diagonal : Q →* Q × Q :=
    (MonoidHom.id Q).prod (MonoidHom.id Q)
  let first : Q × Q →* Q := MonoidHom.fst Q Q
  have hret : first.comp diagonal = MonoidHom.id Q := by
    ext q
    rfl
  exact profiniteClosure_range_eq_range_of_retraction diagonal first hret

end

end GroupApproximation
