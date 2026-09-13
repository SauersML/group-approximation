import GroupApproximation.GGT.HullSCLemma51LetterPullbackShortcutArcs

/-!
# The faces of the certificate cut

The certificate cut of a quotient-null word all of whose rotations are relative geodesics gives
an arc of the word, a relator `ext ++ rem ∈ W` and geodesic side words `L`, `R`, with
`listVal ext = L · arc · R` and `|L| + |R| < |arc|` (`CutFace`).  The source word
`L ++ arc ++ R ++ respellInv ext` closes, and its peripheral letters give faces.

* `val_mem_boundedProducts_of_face`: in a closed word through a peripheral letter `a` of index
  `λ` whose other peripheral letters read at the coset of `a` have atom values, `a.val` is a
  bounded product of atoms.
* `exists_designated_of_face`: if one more letter `b` is read at that coset, `a.val⁻¹` is `b.val`
  between two bounded products.
* `cosetLettersAt_take_of_isRelGeodesic`, `cosetLettersAt_drop_of_isRelGeodesic`: a geodesic word
  has no second peripheral letter of index `λ` at the coset of one of its own.
* `cosetLettersAt_respellInv_of_subset`: the respelled inverse of a piece of a relator has atom
  values at every coset (`CutFace.ext_block`).
-/

namespace GroupApproximation
namespace HullSC

universe u w

variable {G : Type u} [Group G] {Lambda : Type w}

omit [Group G] in
theorem exists_eq_comp_of_isCompOf {lam : Lambda} {a : GGT.RelLetter G Lambda}
    (hc : GGT.RelLetter.IsCompOf lam a) : ∃ (mu : Lambda) (h : G), a = GGT.RelLetter.comp mu h := by
  cases a with
  | base x => exact False.elim hc
  | comp mu h => exact ⟨mu, h, rfl⟩

theorem listVal_take_mul_getElem_mul_drop (g : List (GGT.RelLetter G Lambda)) {j : ℕ}
    (hj : j < g.length) :
    GGT.RelLetter.listVal (g.take j) * g[j].val * GGT.RelLetter.listVal (g.drop (j + 1)) =
      GGT.RelLetter.listVal g := by
  rw [listVal_eq_take_mul_getElem_mul_drop g hj, mul_assoc]

/-- **The respelled inverse of a piece of a relator has atom values**, at every coset. -/
theorem cosetLettersAt_respellInv_of_subset (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (lam : Lambda) {r : ℕ} (hr : 1 ≤ r) (c x : G)
    {u word : List (GGT.RelLetter G Lambda)} (hu : ∀ a ∈ u, D.IsLetter a) (hword : word ∈ W)
    (hsub : ∀ a ∈ u, a ∈ word) :
    CosetLettersAt D lam (pullbackAtoms W D lam r) c (x * GGT.RelLetter.listVal u)
      (respellInv D u) := by
  refine cosetLettersAt_respellInv D lam _ c x u hu ?_
  intro k hk hk' _
  rw [val_invLetter]
  rcases hk' with hcomp | ⟨y, hy, hyH⟩
  · exact peripheralLetterValues_subset_pullbackAtoms W D lam r
      ⟨word, hword, u[k], hsub _ (List.getElem_mem hk), exists_eq_comp_of_isCompOf hcomp,
        Or.inr rfl⟩
  · have hyb : y ∈ D.base := by
      have hl := hu u[k] (List.getElem_mem hk)
      rw [hy] at hl
      exact hl
    rw [hy]
    exact inv_mem_pullbackAtoms_of_mem_base hyb hyH hr

/-- **A closed word through a peripheral letter bounds its value.**  The word `u ++ a :: v`,
read from `1`, closes, and every peripheral letter of index `λ` other than `a` read at the coset
of `a` has an atom value. -/
theorem val_mem_boundedProducts_of_face (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (lam : Lambda) {r N : ℕ}
    {u v : List (GGT.RelLetter G Lambda)} {a : GGT.RelLetter G Lambda}
    (hu : ∀ b ∈ u, D.IsLetter b) (hv : ∀ b ∈ v, D.IsLetter b)
    (hloop : GGT.RelLetter.listVal u * a.val * GGT.RelLetter.listVal v = 1)
    (ha : a.val ∈ D.fam lam)
    (hAu : CosetLettersAt D lam (pullbackAtoms W D lam r) (GGT.RelLetter.listVal u) 1 u)
    (hAv : CosetLettersAt D lam (pullbackAtoms W D lam r) (GGT.RelLetter.listVal u)
      (GGT.RelLetter.listVal u * a.val) v)
    (hlen : u.length + v.length ≤ r) (hN : r + 1 ≤ N) :
    a.val ∈ boundedProducts (pullbackAtoms W D lam r) N := by
  have hvval : GGT.RelLetter.listVal v = (GGT.RelLetter.listVal u * a.val)⁻¹ :=
    eq_inv_of_mul_eq_one_right hloop
  have hval : GGT.RelLetter.listVal (v ++ u) = a.val⁻¹ := by
    rw [GGT.OsinComponents.listVal_append, hvval]
    group
  have hrest : ∀ b ∈ v ++ u, D.IsLetter b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hv b hb
    · exact hu b hb
  have hrep : (GGT.RelLetter.listVal u * a.val)⁻¹ * GGT.RelLetter.listVal u ∈ D.fam lam := by
    have e : (GGT.RelLetter.listVal u * a.val)⁻¹ * GGT.RelLetter.listVal u = a.val⁻¹ := by
      group
    rw [e]
    exact inv_mem ha
  have hA : CosetLettersAt D lam (pullbackAtoms W D lam r) (GGT.RelLetter.listVal u * a.val)
      (GGT.RelLetter.listVal u * a.val) (v ++ u) := by
    refine (hAv.of_rep hrep).append ?_
    rw [hvval, mul_inv_cancel]
    exact hAu.of_rep hrep
  have hmem := mem_boundedProducts_pullbackAtoms_of_cosetLettersAt W D lam
    (GGT.RelLetter.listVal u * a.val) hrest (by rw [hval]; exact inv_mem ha) hA
    (by rw [List.length_append]; omega) hN
  rw [hval] at hmem
  have hinv := inv_mem_boundedProducts (fun _ hx => inv_mem_pullbackAtoms hx) hmem
  rwa [inv_inv] at hinv

/-- **A closed word through two peripheral letters at one coset.**  The word
`a :: (u₁ ++ b :: u₂)`, read from `c`, closes; `b` is read at the coset of `a`, and every other
peripheral letter of index `λ` read there has an atom value.  Then `a.val⁻¹` is `b.val` between
two bounded products. -/
theorem exists_designated_of_face (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (lam : Lambda) {r N : ℕ} (c : G)
    {u₁ u₂ : List (GGT.RelLetter G Lambda)} {a b : GGT.RelLetter G Lambda}
    (hu₁ : ∀ x ∈ u₁, D.IsLetter x) (hu₂ : ∀ x ∈ u₂, D.IsLetter x) (hb : D.IsLetter b)
    (hloop : a.val * GGT.RelLetter.listVal u₁ * b.val * GGT.RelLetter.listVal u₂ = 1)
    (ha : a.val ∈ D.fam lam) (hbcomp : GGT.RelLetter.IsCompOf lam b)
    (hbcos : GGT.RelLetter.listVal u₁ ∈ D.fam lam)
    (hA₁ : CosetLettersAt D lam (pullbackAtoms W D lam r) c (c * a.val) u₁)
    (hA₂ : CosetLettersAt D lam (pullbackAtoms W D lam r) c
      (c * (a.val * GGT.RelLetter.listVal u₁ * b.val)) u₂)
    (hlen : u₁.length + u₂.length + 1 ≤ r) (hN : r + 1 ≤ N) :
    ∃ X Y : G, X ∈ boundedProducts (pullbackAtoms W D lam r) N ∧
      Y ∈ boundedProducts (pullbackAtoms W D lam r) N ∧ a.val⁻¹ = X * b.val * Y := by
  have hrep : (1 : G)⁻¹ * a.val⁻¹ ∈ D.fam lam := by
    rw [inv_one, one_mul]
    exact inv_mem ha
  have e₁ : (c * a.val)⁻¹ * c = a.val⁻¹ := by group
  have h₁ : CosetLettersAt D lam (pullbackAtoms W D lam r) 1 1 u₁ := by
    have h := hA₁.translate (c * a.val)⁻¹
    rw [e₁, inv_mul_cancel] at h
    exact h.of_rep hrep
  have h₂ : CosetLettersAt D lam (pullbackAtoms W D lam r) 1
      (GGT.RelLetter.listVal u₁ * b.val) u₂ := by
    have h := hA₂.translate (c * a.val)⁻¹
    have e₂ : (c * a.val)⁻¹ * (c * (a.val * GGT.RelLetter.listVal u₁ * b.val)) =
        GGT.RelLetter.listVal u₁ * b.val := by group
    rw [e₁, e₂] at h
    exact h.of_rep hrep
  have hsplit : GGT.RelLetter.listVal (u₁ ++ b :: u₂) = a.val⁻¹ := by
    rw [GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_cons]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hloop]
    simp only [mul_assoc]
  have hletters : ∀ x ∈ u₁ ++ b :: u₂, D.IsLetter x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hu₁ x hx
    · rcases List.mem_cons.mp hx with hx | hx
      · rw [hx]
        exact hb
      · exact hu₂ x hx
  obtain ⟨X, Y, hX, hY, hXY⟩ := (face_relation_split D lam (pullbackAtoms W D lam r) hletters
    (by rw [hsplit]; exact inv_mem ha) h₁ h₂).2 ⟨hbcomp, hbcos⟩
  have hlen' : (u₁ ++ b :: u₂).length ≤ r := by
    simp only [List.length_append, List.length_cons]
    omega
  have hsub : pullbackAtoms W D lam r ∪ D.relBall lam (u₁ ++ b :: u₂).length ⊆
      pullbackAtoms W D lam r :=
    Set.union_subset (fun _ hx => hx) fun _ hx =>
      relBall_subset_pullbackAtoms W D lam r
        (GGT.OsinComponents.relBall_mono_radius D lam hlen' hx)
  refine ⟨X, Y, boundedProducts_mono hsub (by omega) hX,
    boundedProducts_mono hsub (by omega) hY, ?_⟩
  rw [← hsplit]
  exact hXY

/-- **A prefix of a geodesic word before one of its peripheral letters** has no peripheral letter
of index `λ` at the coset of that letter. -/
theorem cosetLettersAt_take_of_isRelGeodesic (D : GGT.RelGenSet G Lambda) (lam : Lambda)
    (A : Set G) {g : List (GGT.RelLetter G Lambda)} (hg : RelWord.IsAdmissible D g)
    (hgeo : IsRelGeodesic D g) {j : ℕ} (hj : j < g.length)
    (hcomp : GGT.RelLetter.IsCompOf lam g[j]) (y : G) {k : ℕ} (hkj : k ≤ j) :
    CosetLettersAt D lam A (y * GGT.RelLetter.listVal (g.take j)) y (g.take k) := by
  intro i hi hci hv
  have hik : i < k := lt_of_lt_of_le hi (List.length_take_le k g)
  have hig : i < g.length := lt_of_lt_of_le hi (List.length_take_le' k g)
  rw [List.getElem_take] at hci
  rw [List.take_take, Nat.min_eq_left hik.le] at hv
  have e : (GGT.RelLetter.listVal (g.take j))⁻¹ * GGT.RelLetter.listVal (g.take i) =
      (y * GGT.RelLetter.listVal (g.take j))⁻¹ * (y * GGT.RelLetter.listVal (g.take i)) := by
    group
  have hji := eq_of_isCompOf_coset_of_isRelGeodesic D hg hgeo hj hig hcomp hci
    (by rw [e]; exact hv)
  exact absurd hji (by omega)

/-- **A suffix of a geodesic word after one of its peripheral letters** has no peripheral letter
of index `λ` at the coset of that letter. -/
theorem cosetLettersAt_drop_of_isRelGeodesic (D : GGT.RelGenSet G Lambda) (lam : Lambda)
    (A : Set G) {g : List (GGT.RelLetter G Lambda)} (hg : RelWord.IsAdmissible D g)
    (hgeo : IsRelGeodesic D g) {j : ℕ} (hj : j < g.length)
    (hcomp : GGT.RelLetter.IsCompOf lam g[j]) (y : G) {k : ℕ} (hjk : j < k) :
    CosetLettersAt D lam A (y * GGT.RelLetter.listVal (g.take j))
      (y * GGT.RelLetter.listVal (g.take k)) (g.drop k) := by
  intro i hi hci hv
  have hlen : (g.drop k).length = g.length - k := List.length_drop
  have hig : k + i < g.length := by omega
  rw [List.getElem_drop] at hci
  have e : (GGT.RelLetter.listVal (g.take j))⁻¹ * GGT.RelLetter.listVal (g.take (k + i)) =
      (y * GGT.RelLetter.listVal (g.take j))⁻¹ *
        (y * GGT.RelLetter.listVal (g.take k) *
          GGT.RelLetter.listVal ((g.drop k).take i)) := by
    rw [List.take_add, GGT.OsinComponents.listVal_append]
    group
  have hji := eq_of_isCompOf_coset_of_isRelGeodesic D hg hgeo hj hig hcomp hci
    (by rw [e]; exact hv)
  exact absurd hji (by omega)

/-- **The certificate cut.**  Admissible relative geodesics `L`, `arc`, `R` with
`|L| + |R| < |arc|`, and an admissible piece `ext` of a relator spelling `L · arc · R`. -/
structure CutFace (W : Set (List (GGT.RelLetter G Lambda))) (D : GGT.RelGenSet G Lambda)
    (L arc R ext : List (GGT.RelLetter G Lambda)) : Prop where
  left_adm : RelWord.IsAdmissible D L
  left_geo : IsRelGeodesic D L
  arc_adm : RelWord.IsAdmissible D arc
  arc_geo : IsRelGeodesic D arc
  right_adm : RelWord.IsAdmissible D R
  right_geo : IsRelGeodesic D R
  ext_adm : RelWord.IsAdmissible D ext
  ext_sub : ∃ word ∈ W, ∀ a ∈ ext, a ∈ word
  value : GGT.RelLetter.listVal ext =
    GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R
  short : L.length + R.length < arc.length

/-- The respelled relator piece closing the cut face has atom values at every coset. -/
theorem CutFace.ext_block {W : Set (List (GGT.RelLetter G Lambda))} {D : GGT.RelGenSet G Lambda}
    {L arc R ext : List (GGT.RelLetter G Lambda)} (hcf : CutFace W D L arc R ext)
    (lam : Lambda) {r : ℕ} (hr1 : 1 ≤ r) (c : G) :
    CosetLettersAt D lam (pullbackAtoms W D lam r) c
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R)
      (respellInv D ext) := by
  obtain ⟨word, hword, hsub⟩ := hcf.ext_sub
  have h := cosetLettersAt_respellInv_of_subset W D lam hr1 c 1 hcf.ext_adm hword hsub
  rwa [one_mul, hcf.value] at h

/-- The letters of the closed word of a cut face. -/
theorem CutFace.ext_letters {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {L arc R ext : List (GGT.RelLetter G Lambda)}
    (hcf : CutFace W D L arc R ext) : ∀ a ∈ respellInv D ext, D.IsLetter a :=
  isLetter_respellInv D (word := ext) hcf.ext_adm

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.exists_eq_comp_of_isCompOf
#audit_axioms GroupApproximation.HullSC.listVal_take_mul_getElem_mul_drop
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_respellInv_of_subset
#audit_axioms GroupApproximation.HullSC.val_mem_boundedProducts_of_face
#audit_axioms GroupApproximation.HullSC.exists_designated_of_face
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_take_of_isRelGeodesic
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_drop_of_isRelGeodesic
#audit_axioms GroupApproximation.HullSC.CutFace.ext_block
#audit_axioms GroupApproximation.HullSC.CutFace.ext_letters
