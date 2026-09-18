import GroupApproximation.BooneHigman.Metabelian.SuslinHorrocksLower
import GroupApproximation.Meta.AxiomGuard

/-!
# Local Horrocks, part 3: a row with a monic entry is elementarily a basis row

Lane `bh-met-90a`.  **Local Horrocks theorem (row form), proved outright.**  Let `R` be a local
ring, `ι` a finite index type with at least three elements, `M ∈ GL_ι(R[X])`, and suppose the
entry `M r t` is monic.  Then there is `F ∈ E_ι(R[X])` with row `r` of `M F` equal to `e_r`
(`suslinHorrocks_row`).

Proof: induction on the degree of the monic entry.  In degree `0` the entry is `1`, and the rest
of the row is cleared (`suslinHorrocks_clear_of_eq_one`).  In degree `d + 1` the lowering step
`suslinHorrocks_lower` produces a monic entry of degree `d` in another column.  Finally the basis
row `e_s` is moved to `e_r` (`suslinHorrocks_move_single`).  Only Euclidean division by monic
polynomials and locality of `R` (through the residue field) are used.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- **Horrocks' lowering step.**  Over a local ring and with at least three columns, a monic
entry of degree `d + 1` in row `r` is traded, by an elementary right factor, for a monic entry
of degree `d` in the same row. -/
theorem suslinHorrocks_lower [IsLocalRing R] (hcard : 3 ≤ Fintype.card ι)
    (M : (Matrix ι ι (Polynomial R))ˣ) (r t : ι) (d : ℕ)
    (ht : ((M : Matrix ι ι (Polynomial R)) r t).Monic)
    (hd : ((M : Matrix ι ι (Polynomial R)) r t).natDegree = d + 1) :
    ∃ F ∈ elementaryGroup ι (Polynomial R), ∃ e : ι,
      (((M * F : (Matrix ι ι (Polynomial R))ˣ) : Matrix ι ι (Polynomial R)) r e).Monic ∧
        (((M * F : (Matrix ι ι (Polynomial R))ˣ) : Matrix ι ι (Polynomial R)) r e).natDegree =
          d := by
  obtain ⟨F1, hF1, hrow⟩ := suslinHorrocks_exists_row_modByMonic M r t
  obtain ⟨M1, hM1⟩ : ∃ M1 : (Matrix ι ι (Polynomial R))ˣ, M * F1 = M1 := ⟨_, rfl⟩
  rw [hM1] at hrow
  have hft : (M1 : Matrix ι ι (Polynomial R)) r t = (M : Matrix ι ι (Polynomial R)) r t := by
    rw [hrow t, if_pos rfl]
  have hmo : ((M1 : Matrix ι ι (Polynomial R)) r t).Monic := by
    rw [hft]
    exact ht
  have hmd : ((M1 : Matrix ι ι (Polynomial R)) r t).natDegree = d + 1 := by
    rw [hft, hd]
  obtain ⟨c, hct, hc⟩ := suslinHorrocks_exists_residue_ne_zero M1 r t hmo (by omega)
  have hgf : ((M1 : Matrix ι ι (Polynomial R)) r c).degree <
      ((M1 : Matrix ι ι (Polynomial R)) r t).degree := by
    rw [hrow c, if_neg hct, hft]
    exact Polynomial.degree_modByMonic_lt _ ht
  obtain ⟨a, b, hab, habd⟩ := suslinHorrocks_exists_monic_combo _ _ d hmo hmd hgf hc
  obtain ⟨e, het, hec⟩ : ∃ e : ι, e ≠ t ∧ e ≠ c := by
    have h3 : 0 < ((Finset.univ.erase t).erase c).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hct, Finset.mem_univ c⟩),
        Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ]
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.1 h3
    exact ⟨e, (Finset.mem_erase.1 (Finset.mem_erase.1 he).2).1, (Finset.mem_erase.1 he).1⟩
  obtain ⟨g, hg⟩ : ∃ g, (M1 : Matrix ι ι (Polynomial R)) r c = g := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, (M1 : Matrix ι ι (Polynomial R)) r t = f := ⟨_, rfl⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, (M1 : Matrix ι ι (Polynomial R)) r e = w₀ := ⟨_, rfl⟩
  rw [hg, hf] at hab habd
  obtain ⟨w, hw⟩ : ∃ w : Polynomial R, 1 - w₀ /ₘ (g * a + f * b) = w := ⟨_, rfl⟩
  refine ⟨F1 * (elementaryUnit c e (Ne.symm hec) (a * w) *
      elementaryUnit t e (Ne.symm het) (b * w)),
    Subgroup.mul_mem _ hF1 (Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _)
      (elementaryUnit_mem _ _ _ _)), e, ?_⟩
  have hentry : ((M * (F1 * (elementaryUnit c e (Ne.symm hec) (a * w) *
      elementaryUnit t e (Ne.symm het) (b * w))) : (Matrix ι ι (Polynomial R))ˣ) :
        Matrix ι ι (Polynomial R)) r e =
      w₀ + (g * a + f * b) * (1 - w₀ /ₘ (g * a + f * b)) := by
    rw [← mul_assoc, hM1, ← mul_assoc, Units.val_mul, Units.val_mul,
      suslinHorrocks_two_col_apply, hw₀, hg, hf, hw]
    ring
  rw [hentry]
  exact suslinHorrocks_monic_add_mod _ _ d hab habd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_lower

/-- **Local Horrocks, basis-row form.**  By induction on the degree of the monic entry, row `r`
is carried by an elementary right factor to some standard basis row `e_s`. -/
theorem suslinHorrocks_row_single_aux [IsLocalRing R] (hcard : 3 ≤ Fintype.card ι) (d : ℕ) :
    ∀ (M : (Matrix ι ι (Polynomial R))ˣ) (r t : ι),
      ((M : Matrix ι ι (Polynomial R)) r t).Monic →
        ((M : Matrix ι ι (Polynomial R)) r t).natDegree = d →
          ∃ F ∈ elementaryGroup ι (Polynomial R), ∃ s : ι,
            ∀ c : ι, ((M * F : (Matrix ι ι (Polynomial R))ˣ) : Matrix ι ι (Polynomial R)) r c =
              if c = s then 1 else 0 := by
  induction d with
  | zero =>
    intro M r t ht hd
    obtain ⟨F, hF, hrow⟩ := suslinHorrocks_clear_of_eq_one M r t
      (Polynomial.eq_one_of_monic_natDegree_zero ht hd)
    exact ⟨F, hF, t, hrow⟩
  | succ d ih =>
    intro M r t ht hd
    obtain ⟨F1, hF1, e, he, hed⟩ := suslinHorrocks_lower hcard M r t d ht hd
    obtain ⟨F2, hF2, s, hrow⟩ := ih (M * F1) r e he hed
    refine ⟨F1 * F2, Subgroup.mul_mem _ hF1 hF2, s, fun c ↦ ?_⟩
    rw [← mul_assoc]
    exact hrow c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_row_single_aux

/-- **Local Horrocks theorem (row form).**  Over a local ring `R` and with at least three
indices, if the entry `M r t` of `M ∈ GL_ι(R[X])` is monic, then an elementary right factor
turns row `r` of `M` into the standard basis row `e_r`. -/
theorem suslinHorrocks_row [IsLocalRing R] (hcard : 3 ≤ Fintype.card ι)
    (M : (Matrix ι ι (Polynomial R))ˣ) (r t : ι)
    (ht : ((M : Matrix ι ι (Polynomial R)) r t).Monic) :
    ∃ F ∈ elementaryGroup ι (Polynomial R),
      ∀ c : ι, ((M * F : (Matrix ι ι (Polynomial R))ˣ) : Matrix ι ι (Polynomial R)) r c =
        if c = r then 1 else 0 := by
  obtain ⟨F1, hF1, s, hrow⟩ := suslinHorrocks_row_single_aux hcard _ M r t ht rfl
  obtain ⟨F2, hF2, hrow2⟩ := suslinHorrocks_move_single (M * F1) r s hrow
  refine ⟨F1 * F2, Subgroup.mul_mem _ hF1 hF2, fun c ↦ ?_⟩
  rw [← mul_assoc]
  exact hrow2 c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_row

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
