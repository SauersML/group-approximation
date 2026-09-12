import GroupApproximation.GGT.HullSCFillingNonElementary
import GroupApproximation.GGT.HullSCFillingAlphabetReduction
import GroupApproximation.GGT.DGOProposition433Finite
import GroupApproximation.Meta.AxiomGuard

/-!
# Clause (d) of Hull's Theorem 7.1 over a quotient with torsion

Hull's clause (d): in the quotient `Q = G ⧸ ⟨⟨W⟩⟩`, the image of a suitable
subgroup is again suitable.  Its non-elementarity half is
`hullLemma58SuitableFamily_unconditional`.  Its other half, *"`φ(N)` normalizes
no nontrivial finite subgroup of `Q`"*, was so far obtained only when `Q` is
torsion-free (`suitableImagesInQuotient_of_torsionFree`).  This module proves it
for every quotient with Hull's peripheral preservation, with or without torsion.

## The argument

The auxiliary peripheral family of `N` carries two subgroups `H₀, H₁ ≤ N`,
containing loxodromics `h₀, h₁`, meeting trivially, and jointly hyperbolically
embedded.  Peripheral preservation makes their images `q H₀, q H₁` a
hyperbolically embedded family of `Q`, on whose union `q` is injective.

Let `F ≤ Q` be finite and normalized by `q N`, and let `x ∈ F`.

* `q hᵦ` normalizes `F`, so the conjugates `(q hᵦ)ⁱ x (q hᵦ)⁻ⁱ` range over the
  finite set `F`.  Two of them agree, so a positive power `(q hᵦ)ⁿ` commutes
  with `x` (`exists_pow_commute_of_normalizes_finite`).
* Then every `(q hᵦ)ⁿᵐ` lies in `q Hᵦ ∩ x (q Hᵦ) x⁻¹`.  These are infinitely many
  elements, because `q` keeps `hᵦ` of infinite order.  Almost malnormality of the
  hyperbolically embedded `q Hᵦ` (Dahmani–Guirardel–Osin, Proposition 4.33,
  `GGT.finite_conj_inter_of_notMem`) therefore forces `x ∈ q Hᵦ`
  (`mem_fam_of_normalizes_finite`).
* So `x ∈ q H₀ ∩ q H₁`, and injectivity of `q` on `H₀ ∪ H₁` with `H₀ ∩ H₁ = 1`
  gives `x = 1`.

The same holds for every prescribed subgroup `S j`, from its own pair core.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **An element normalizing a finite subgroup has a positive power commuting with
each of its elements.**  The conjugates `yⁱ x y⁻ⁱ` all lie in the finite subgroup,
so two of them agree. -/
theorem exists_pow_commute_of_normalizes_finite {Q : Type u} [Group Q]
    {F : Subgroup Q} [Finite F] {y : Q}
    (hy : ∀ z ∈ F, y * z * y⁻¹ ∈ F) {x : Q} (hx : x ∈ F) :
    ∃ n : ℕ, 0 < n ∧ y ^ n * x * (y ^ n)⁻¹ = x := by
  have hmem : ∀ i : ℕ, y ^ i * x * (y ^ i)⁻¹ ∈ F := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ i ih =>
        have heq : y * (y ^ i * x * (y ^ i)⁻¹) * y⁻¹ =
            y ^ (i + 1) * x * (y ^ (i + 1))⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          simp only [mul_assoc]
        rw [← heq]
        exact hy _ ih
  have key : ∀ i d : ℕ, y ^ i * x * (y ^ i)⁻¹ = y ^ (i + d) * x * (y ^ (i + d))⁻¹ →
      y ^ d * x * (y ^ d)⁻¹ = x := by
    intro i d h
    rw [pow_add] at h
    have h' : y ^ i * x * (y ^ i)⁻¹ =
        y ^ i * (y ^ d * x * (y ^ d)⁻¹) * (y ^ i)⁻¹ := by
      rw [h]
      simp only [mul_assoc, mul_inv_rev]
    exact (mul_left_cancel (mul_right_cancel h')).symm
  let f : ℕ → F := fun i => ⟨y ^ i * x * (y ^ i)⁻¹, hmem i⟩
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hval : y ^ i * x * (y ^ i)⁻¹ = y ^ j * x * (y ^ j)⁻¹ :=
    congrArg Subtype.val hfij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hji : j = i + (j - i) := by omega
    rw [hji] at hval
    exact ⟨j - i, by omega, key i (j - i) hval⟩
  · have hij' : i = j + (i - j) := by omega
    rw [hij'] at hval
    exact ⟨i - j, by omega, key j (i - j) hval.symm⟩

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
  {k : ℕ} {S : Fin k → Subgroup G} {Q : Type u} [Group Q] {q : G →* Q}
  {D : AuxiliaryPeripheralFamily A N S}

/-- **A finite subgroup normalized by the image of an infinite-order peripheral
element lies in the preserved peripheral**, by almost malnormality of a
hyperbolically embedded subgroup (Dahmani–Guirardel–Osin, Proposition 4.33). -/
theorem mem_fam_of_normalizes_finite (P : QuotientPeripheralPreservation q D)
    (i : AuxiliaryPeripheralIndex k) {g : G} (hg : g ∈ D.cores.peripheral i)
    (hginf : ¬ IsOfFinOrder g) {F : Subgroup Q} [Finite F]
    (hnorm : ∀ z ∈ F, q g * z * (q g)⁻¹ ∈ F) {x : Q} (hx : x ∈ F) :
    x ∈ P.rel.fam i := by
  by_contra hxH
  obtain ⟨n, hn, hcomm⟩ := exists_pow_commute_of_normalizes_finite hnorm hx
  have hfin := GGT.finite_conj_inter_of_notMem P.rel P.embedded hxH
  have hqg : q g ∈ P.rel.fam i := by
    rw [P.fam_map i]
    exact Subgroup.mem_map_of_mem q hg
  have hqginf : ¬ IsOfFinOrder (q g) := P.not_isOfFinOrder_map i hg hginf
  have hc : Commute x ((q g) ^ n) := (mul_inv_eq_iff_eq_mul.mp hcomm).symm
  have hsub : Set.range (fun m : ℤ => ((q g) ^ n) ^ m) ⊆
      {z : Q | z ∈ P.rel.fam i ∧ x⁻¹ * z * x ∈ P.rel.fam i} := by
    rintro _ ⟨m, rfl⟩
    have hmem : ((q g) ^ n) ^ m ∈ P.rel.fam i := zpow_mem (pow_mem hqg n) m
    simp only [Set.mem_setOf_eq]
    refine ⟨hmem, ?_⟩
    rw [mul_assoc, ← (hc.zpow_right m).eq, inv_mul_cancel_left]
    exact hmem
  have hpowinf : ¬ IsOfFinOrder ((q g) ^ n) := fun hfo => hqginf (hfo.of_pow hn.ne')
  have hinj : Function.Injective (fun m : ℤ => ((q g) ^ n) ^ m) :=
    injective_zpow_iff_not_isOfFinOrder.mpr hpowinf
  exact (Set.infinite_range_of_injective hinj) (hfin.subset hsub)

/-- **The image of a pair core normalizes no nontrivial finite subgroup.**  Every
finite subgroup it normalizes lies in both preserved peripherals `q H₀` and
`q H₁`, and these meet trivially. -/
theorem normalizesNoNontrivialFinite_map_of_core (P : QuotientPeripheralPreservation q D)
    {T : Subgroup G} (E : HypEmbeddedCore₂ A T) (idx : Bool → AuxiliaryPeripheralIndex k)
    (hidx : ∀ b, D.cores.peripheral (idx b) = E.H b) :
    HullSuitable.NormalizesNoNontrivialFinite (T.map q) := by
  intro F hF hnorm
  haveI := hF
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hnormb : ∀ b, ∀ z ∈ F, q (E.lox b) * z * (q (E.lox b))⁻¹ ∈ F := fun b =>
    hnorm (q (E.lox b)) (Subgroup.mem_map_of_mem q (E.le b (E.lox_mem b)))
  have hmap : ∀ b, x ∈ (E.H b).map q := by
    intro b
    have hperiph : E.lox b ∈ D.cores.peripheral (idx b) := by
      rw [hidx b]
      exact E.lox_mem b
    have h := mem_fam_of_normalizes_finite P (idx b) hperiph
      (not_isOfFinOrder_of_isLoxodromic (E.lox_isLoxodromic b)) (hnormb b) hx
    rw [P.fam_map (idx b), hidx b] at h
    exact h
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp (hmap false)
  obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp (hmap true)
  have huv : u = v := by
    apply P.injOn_peripheralUnion
    · exact Set.mem_iUnion.mpr ⟨idx false, by rw [hidx false]; exact hu⟩
    · exact Set.mem_iUnion.mpr ⟨idx true, by rw [hidx true]; exact hv⟩
    · rw [hux, hvx]
  have hu1 : u = 1 := E.disjoint u hu (by rw [huv]; exact hv)
  rw [← hux, hu1, map_one]

/-- **Clause (d), second half, for `N`**: the image of `N` normalizes no nontrivial
finite subgroup of the quotient. -/
theorem normalizesNoNontrivialFinite_map_N (P : QuotientPeripheralPreservation q D) :
    HullSuitable.NormalizesNoNontrivialFinite (N.map q) :=
  normalizesNoNontrivialFinite_map_of_core P D.cores.coreN (fun b => (none, b))
    (fun _ => rfl)

/-- **Clause (d), second half, for each prescribed subgroup.** -/
theorem normalizesNoNontrivialFinite_map_S (P : QuotientPeripheralPreservation q D)
    (j : Fin k) : HullSuitable.NormalizesNoNontrivialFinite ((S j).map q) :=
  normalizesNoNontrivialFinite_map_of_core P (D.cores.coreS j) (fun b => (some j, b))
    (fun _ => rfl)

/-- **The suitable images in the quotient, with no torsion hypothesis.** -/
theorem suitableImagesInQuotient_of_peripheralPreservation
    (B : QuotientHullAlphabet A q) (P : QuotientPeripheralPreservation q D)
    (hN : ActsNonElementarily (N.map q) (Cayley.base B.hullSet.alphabet))
    (hS : ∀ j : Fin k,
      ActsNonElementarily ((S j).map q) (Cayley.base B.hullSet.alphabet)) :
    SuitableImagesInQuotient N S q B :=
  ⟨⟨hN, normalizesNoNontrivialFinite_map_N P⟩,
    fun j => ⟨hS j, normalizesNoNontrivialFinite_map_S P j⟩⟩

/-- **Lemma 5.8's common alphabet and clause (d) reassemble the filling alphabet
over any quotient with peripheral preservation**, torsion or not:
`nonempty_fillingAlphabetData_of_peripheralPreservation` without `hQ`. -/
theorem nonempty_fillingAlphabetData_of_peripheralPreservation_general
    (D : AuxiliaryPeripheralFamily A N S) (P : QuotientPeripheralPreservation q D) :
    Nonempty (FillingAlphabetData A N S q) := by
  obtain ⟨B, -, hN, hS⟩ := hullLemma58SuitableFamily_unconditional q D P
  exact ⟨FillingAlphabetData.ofQuotientHullAlphabet B
    (suitableImagesInQuotient_of_peripheralPreservation B P hN hS)⟩

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.exists_pow_commute_of_normalizes_finite
#audit_axioms GroupApproximation.HullSC.mem_fam_of_normalizes_finite
#audit_axioms GroupApproximation.HullSC.normalizesNoNontrivialFinite_map_of_core
#audit_axioms GroupApproximation.HullSC.normalizesNoNontrivialFinite_map_N
#audit_axioms GroupApproximation.HullSC.normalizesNoNontrivialFinite_map_S
#audit_axioms GroupApproximation.HullSC.suitableImagesInQuotient_of_peripheralPreservation
#audit_axioms GroupApproximation.HullSC.nonempty_fillingAlphabetData_of_peripheralPreservation_general
