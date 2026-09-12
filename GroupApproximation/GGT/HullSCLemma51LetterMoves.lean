import GroupApproximation.GGT.HullSCLemma51FaceRelation
import GroupApproximation.GGT.HullSCLemma51LetterFacts
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's two moves on words over a relative alphabet

The letter pullback of Osin's Lemma 5.1 (`GGT/HullSCLemma51LetterPullback.lean`) applies
one move to a quotient-null word `w` over the letters of `D`:

* **a shortcut**: if some rotation of `w` is not geodesic, a strictly shorter geodesic
  word has the same value (`exists_shortcut_of_not_isRelGeodesic`);
* **a certificate cut**: if every rotation of `w` is geodesic, Osin's Lemma 4.4
  certificates give, after a rotation, an arc of `w` and a relator `ext ++ rem` with
  `ext` joined to the arc by geodesic sides `L`, `R` of length at most `ε`, and
  `|L| + |rem| + |R| < |arc|` (`exists_geodesicCut_of_leastAreaCertificates`).

Two coset facts control the new peripheral letters.  A geodesic word reads at most one
peripheral letter of index `λ` in each coset of `H_λ`
(`eq_of_isCompOf_coset_of_isRelGeodesic`), and in the face `L · arc · R` of a cut no
peripheral letter of `L` shares a coset with a vertex of `R`, since that would join the
ends of the geodesic arc by a path shorter than the arc (`false_of_crossCoset`).
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A geodesic word over the relative alphabet.** -/
def IsRelGeodesic (D : GGT.RelGenSet G Lambda) (u : List (GGT.RelLetter G Lambda)) : Prop :=
  u.length = wordNorm D.alphabet.carrier (GGT.RelLetter.listVal u)

/-- **A subword of a geodesic word is geodesic.** -/
theorem IsRelGeodesic.infix {D : GGT.RelGenSet G Lambda}
    {α s β : List (GGT.RelLetter G Lambda)} (hadm : RelWord.IsAdmissible D (α ++ s ++ β))
    (hgeo : IsRelGeodesic D (α ++ s ++ β)) : IsRelGeodesic D s := by
  have hS := D.alphabet.symmetricGenerating
  have hα : RelWord.IsAdmissible D α := fun a ha => hadm a (by simp [ha])
  have hs : RelWord.IsAdmissible D s := fun a ha => hadm a (by simp [ha])
  have hβ : RelWord.IsAdmissible D β := fun a ha => hadm a (by simp [ha])
  have e : GGT.RelLetter.listVal (α ++ s ++ β) =
      GGT.RelLetter.listVal α * GGT.RelLetter.listVal s * GGT.RelLetter.listVal β := by
    rw [RelWord.listVal_append, RelWord.listVal_append]
  have h₁ := wordNorm_mul_le hS (GGT.RelLetter.listVal α * GGT.RelLetter.listVal s)
    (GGT.RelLetter.listVal β)
  have h₂ := wordNorm_mul_le hS (GGT.RelLetter.listVal α) (GGT.RelLetter.listVal s)
  have hnα := RelativeBoundaryContiguity.wordNorm_listVal_le_length D α hα
  have hns := RelativeBoundaryContiguity.wordNorm_listVal_le_length D s hs
  have hnβ := RelativeBoundaryContiguity.wordNorm_listVal_le_length D β hβ
  unfold IsRelGeodesic at hgeo ⊢
  rw [e] at hgeo
  simp only [List.length_append] at hgeo
  omega

/-- **The shortcut.**  A word that is not geodesic has a strictly shorter geodesic word
with the same value. -/
theorem exists_shortcut_of_not_isRelGeodesic (D : GGT.RelGenSet G Lambda)
    {s : List (GGT.RelLetter G Lambda)} (hs : RelWord.IsAdmissible D s)
    (hng : ¬ IsRelGeodesic D s) :
    ∃ g : List (GGT.RelLetter G Lambda), RelWord.IsAdmissible D g ∧ IsRelGeodesic D g ∧
      GGT.RelLetter.listVal g = GGT.RelLetter.listVal s ∧ g.length < s.length := by
  obtain ⟨g, hgadm, hgval, hglen⟩ :=
    GGT.OsinComponents.existsGeodesicWord D 1 (GGT.RelLetter.listVal s)
  have hval : GGT.RelLetter.listVal g = GGT.RelLetter.listVal s := by
    simpa using hgval
  have hlen : g.length = wordNorm D.alphabet.carrier (GGT.RelLetter.listVal s) := by
    rw [hglen, wordDist_one_left]
  refine ⟨g, hgadm, by rw [IsRelGeodesic, hval]; exact hlen, hval, ?_⟩
  have hle := RelativeBoundaryContiguity.wordNorm_listVal_le_length D s hs
  unfold IsRelGeodesic at hng
  omega

/-- A geodesic word is `(1/4, 1)`-quasi-geodesic. -/
theorem isLambdaCQuasiGeodesicWord_of_isRelGeodesic (D : GGT.RelGenSet G Lambda)
    {w : List (GGT.RelLetter G Lambda)} (hw : RelWord.IsAdmissible D w)
    (hgeo : IsRelGeodesic D w) : GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / 4) 1 w := by
  refine ⟨hw, ?_⟩
  intro i j hij hj
  rw [wordDist_vertex_of_geodesic D hw hgeo hij hj]
  have h0 : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The certificate cut with geodesic sides.**  If every rotation of a quotient-null word
that is not null in `G` is geodesic, the least-area certificates give a rotation
`before ++ arc ++ after`, a relator `ext ++ rem ∈ W`, and geodesic sides `L`, `R` of length at
most `ε` with `ext = L · arc · R` and `|L| + |rem| + |R| < |arc|`; the arc is geodesic. -/
theorem exists_geodesicCut_of_leastAreaCertificates {Q : Type v} [Group Q]
    (D : GGT.RelGenSet G Lambda) {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho) (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeLeastAreaDiagram D W R),
      Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram))
    {w : List (GGT.RelLetter G Lambda)} (hw : RelWord.IsAdmissible D w)
    (hq : q (GGT.RelLetter.listVal w) = 1) (hne : GGT.RelLetter.listVal w ≠ 1)
    (hgeo : ∀ r : ℕ, IsRelGeodesic D (w.rotate r)) :
    ∃ (r : ℕ) (before arc after L R ext rem : List (GGT.RelLetter G Lambda)),
      w.rotate r = before ++ arc ++ after ∧ ext ++ rem ∈ W ∧
        RelWord.IsAdmissible D L ∧ IsRelGeodesic D L ∧ L.length ≤ eps ∧
        RelWord.IsAdmissible D R ∧ IsRelGeodesic D R ∧ R.length ≤ eps ∧
        IsRelGeodesic D arc ∧
        GGT.RelLetter.listVal ext =
          GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R ∧
        L.length + rem.length + R.length < arc.length := by
  have hword : IsWord D.alphabet.carrier (w.map GGT.RelLetter.val)
      (w.map GGT.RelLetter.val).prod := by
    refine ⟨?_, rfl⟩
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact RelativeBoundaryContiguity.val_mem_alphabet_of_isLetter D (hw a ha)
  have hqg : GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / 4) 1 w :=
    isLambdaCQuasiGeodesicWord_of_isRelGeodesic D hw (by simpa using hgeo 0)
  obtain ⟨C⟩ := exists_relativeDehnCut_of_quasiGeodesicKernelWord D hsc hmu hrho q hker hcert
    (w.map GGT.RelLetter.val) hword hne hq hw rfl hqg
  obtain ⟨C', hext, hrem, _hrot, _hbef, harc, _haft, hL, hR⟩ :=
    C.contiguity.exists_geodesicSides
  obtain ⟨before', arc', after', hdec, -, ham, -⟩ :=
    exists_relArc_of_rotate_decomposition (outer := w) rfl C.contiguity.boundary_decomposition
  have harcval : GGT.RelLetter.listVal arc' = C.contiguity.boundaryArc.prod := by
    unfold GGT.RelLetter.listVal
    rw [ham]
  have harclen : arc'.length = C.contiguity.boundaryArc.length := by
    rw [← ham, List.length_map]
  have hLgeo : IsRelGeodesic D C'.leftSide := by
    obtain ⟨-, hv, hl⟩ := hL
    rw [IsRelGeodesic, hl, wordDist_one_left]
    rw [one_mul] at hv
    rw [hv]
  have hRgeo : IsRelGeodesic D C'.rightSide := by
    obtain ⟨-, hv, hl⟩ := hR
    rw [IsRelGeodesic, hl, wordDist_one_left]
    rw [one_mul] at hv
    rw [hv]
  have hLle : C'.leftSide.length ≤ C.contiguity.leftSide.length := by
    obtain ⟨-, -, hl⟩ := hL
    rw [hl, wordDist_one_left]
    exact RelativeBoundaryContiguity.wordNorm_listVal_le_length D _
      C.contiguity.leftSide_admissible
  have hRle : C'.rightSide.length ≤ C.contiguity.rightSide.length := by
    obtain ⟨-, -, hl⟩ := hR
    rw [hl, wordDist_one_left]
    exact RelativeBoundaryContiguity.wordNorm_listVal_le_length D _
      C.contiguity.rightSide_admissible
  have hshort := C.replacement_length_lt
  rw [RelativeBoundaryContiguity.replacementWord_length] at hshort
  have hmem : C.contiguity.exterior ++ C.contiguity.remainder ∈ W := by
    rw [← C.contiguity.relator_decomposition]
    exact C.relator_mem
  refine ⟨C.contiguity.rotation, before', arc', after', C'.leftSide, C'.rightSide,
    C.contiguity.exterior, C.contiguity.remainder, hdec, hmem, C'.leftSide_admissible, hLgeo,
    C'.leftSide_short, C'.rightSide_admissible, hRgeo, C'.rightSide_short, ?_, ?_, ?_⟩
  · have hadm := isAdmissible_rotate hw C.contiguity.rotation
    rw [hdec] at hadm
    have hg := hgeo C.contiguity.rotation
    rw [hdec] at hg
    exact IsRelGeodesic.infix hadm hg
  · rw [harcval, ← harc, ← hext]
    exact C'.exterior_value
  · rw [harclen]
    omega

/-- **At most one peripheral letter of index `λ` in each coset**, for a geodesic word. -/
theorem eq_of_isCompOf_coset_of_isRelGeodesic (D : GGT.RelGenSet G Lambda)
    {u : List (GGT.RelLetter G Lambda)} (hu : RelWord.IsAdmissible D u)
    (hgeo : IsRelGeodesic D u) {lam : Lambda} {i k : ℕ} (hi : i < u.length)
    (hk : k < u.length) (hci : GGT.RelLetter.IsCompOf lam u[i])
    (hck : GGT.RelLetter.IsCompOf lam u[k])
    (hcoset : (GGT.RelLetter.listVal (u.take i))⁻¹ * GGT.RelLetter.listVal (u.take k) ∈
      D.fam lam) : i = k := by
  have hvert : ∀ m, GGT.OsinComponents.vertex 1 u m = GGT.RelLetter.listVal (u.take m) := by
    intro m
    rw [vertex_eq_mul_listVal_take, one_mul]
  rcases le_total i k with hik | hki
  · exact eq_of_isCompOf_of_mem_fam_of_geodesic D hu hgeo hik hk hck
      (by rw [hvert, hvert]; exact hcoset)
  · have h := eq_of_isCompOf_of_mem_fam_of_geodesic D hu hgeo hki hi hci
      (by rw [hvert, hvert]; simpa using (D.fam lam).inv_mem hcoset)
    exact h.symm

/-- **No cross coset in a cut face.**  In the face `L · arc · R` with a geodesic arc longer
than `|L| + |R|`, a peripheral letter of `L` and a vertex of `R` other than its end never lie
in one coset of `H_λ`. -/
theorem false_of_crossCoset (D : GGT.RelGenSet G Lambda) {lam : Lambda}
    {L arc R : List (GGT.RelLetter G Lambda)} (harc : IsRelGeodesic D arc)
    (hlen : L.length + R.length < arc.length) (hLadm : RelWord.IsAdmissible D L)
    (hRadm : RelWord.IsAdmissible D R) {i j : ℕ} (hi : i < L.length) (hj : j < R.length)
    (hcomp : GGT.RelLetter.IsCompOf lam L[i])
    (hcoset : (GGT.RelLetter.listVal (L.take i))⁻¹ *
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
        GGT.RelLetter.listVal (R.take j)) ∈ D.fam lam) : False := by
  have hS := D.alphabet.symmetricGenerating
  have hval : L[i].val ∈ D.fam lam :=
    val_mem_fam_of_isCompOf (hLadm _ (List.getElem_mem hi)) hcomp
  set v₁ := GGT.RelLetter.listVal (L.take (i + 1)) with hv₁
  have hv₁eq : v₁ = GGT.RelLetter.listVal (L.take i) * L[i].val := by
    rw [hv₁, List.take_succ_eq_append_getElem hi, RelWord.listVal_append,
      RelWord.listVal_singleton]
  set t := v₁⁻¹ * (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
    GGT.RelLetter.listVal (R.take j)) with ht
  have htmem : t ∈ D.fam lam := by
    have e : t = L[i].val⁻¹ * ((GGT.RelLetter.listVal (L.take i))⁻¹ *
        (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
          GGT.RelLetter.listVal (R.take j))) := by
      rw [ht, hv₁eq]; group
    rw [e]
    exact (D.fam lam).mul_mem ((D.fam lam).inv_mem hval) hcoset
  have hdrop : (GGT.RelLetter.listVal L)⁻¹ * v₁ =
      (GGT.RelLetter.listVal (L.drop (i + 1)))⁻¹ := by
    have e := congrArg GGT.RelLetter.listVal (List.take_append_drop (i + 1) L)
    rw [RelWord.listVal_append] at e
    rw [hv₁, ← e]
    group
  have harcval : GGT.RelLetter.listVal arc =
      ((GGT.RelLetter.listVal (L.drop (i + 1)))⁻¹ * t) *
        (GGT.RelLetter.listVal (R.take j))⁻¹ := by
    rw [← hdrop, ht]; group
  have hdropadm : RelWord.IsAdmissible D (L.drop (i + 1)) :=
    fun a ha => hLadm a (List.mem_of_mem_drop ha)
  have htakeadm : RelWord.IsAdmissible D (R.take j) :=
    fun a ha => hRadm a (List.mem_of_mem_take ha)
  have h₁ := wordNorm_mul_le hS ((GGT.RelLetter.listVal (L.drop (i + 1)))⁻¹ * t)
    (GGT.RelLetter.listVal (R.take j))⁻¹
  have h₂ := wordNorm_mul_le hS (GGT.RelLetter.listVal (L.drop (i + 1)))⁻¹ t
  have h₃ : wordNorm D.alphabet.carrier t ≤ 1 :=
    wordNorm_le_one_of_mem (GGT.RelGenSet.fam_subset_alphabet D lam htmem)
  have h₄ := RelativeBoundaryContiguity.wordNorm_listVal_le_length D _ hdropadm
  have h₅ := RelativeBoundaryContiguity.wordNorm_listVal_le_length D _ htakeadm
  rw [wordNorm_inv hS] at h₁ h₂
  have hlend : (L.drop (i + 1)).length = L.length - (i + 1) := List.length_drop
  have hlent : (R.take j).length = j := by rw [List.length_take]; omega
  unfold IsRelGeodesic at harc
  rw [harcval] at harc
  omega

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.IsRelGeodesic.infix
#audit_axioms GroupApproximation.HullSC.exists_shortcut_of_not_isRelGeodesic
#audit_axioms GroupApproximation.HullSC.isLambdaCQuasiGeodesicWord_of_isRelGeodesic
#audit_axioms GroupApproximation.HullSC.exists_geodesicCut_of_leastAreaCertificates
#audit_axioms GroupApproximation.HullSC.eq_of_isCompOf_coset_of_isRelGeodesic
#audit_axioms GroupApproximation.HullSC.false_of_crossCoset
