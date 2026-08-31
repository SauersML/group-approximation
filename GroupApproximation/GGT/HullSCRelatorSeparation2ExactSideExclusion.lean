import GroupApproximation.GGT.HullSCRelatorSeparation2ExactCyclicAvoidance

/-!
# Exact-design closure of the same-side exclusions

The direct and mirrored cyclic-prefix dispatchers retain the component letters
at both endpoints.  This file transports those reads through a symmetrized
relator prefix and proves the two same-side exclusions.  On the oppositely
traversed second long side the certified components are incoming; shifting the
span back by one letter aligns them with the cyclic-prefix endpoints.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u

section ExactSide

variable {G : Type u} [Group G]
  {A : HullGeneratingSet G} {N : Subgroup G}

/-- Every component letter in a symmetrized exact relator has value in its
declared peripheral subgroup. -/
theorem comp_value_mem_fam_of_sym_relator₂
    (E : HypEmbeddedCore₂ A N) {p : List G} {ms : List ℕ}
    {v : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ p (E.lox false) (E.lox true) ms) v)
    {i : ℕ} {s : Bool} {x : G}
    (hread : v[i]? = some (GGT.RelLetter.comp s x)) :
    x ∈ E.rel.fam s := by
  rcases hv.exists_rotate with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [hc] at hread
    have hi : i < (relatorWord₂ p (E.lox false) (E.lox true) ms).length := by
      have := (List.getElem?_eq_some_iff.mp hread).choose
      simpa only [List.length_rotate] using this
    have hraw := getElem?_of_rotate hi hread
    obtain ⟨q, -, -, hqread⟩ := blockIndex_of_relatorWord₂ hraw
    obtain ⟨m, -, hx⟩ := blockWord_getElem?_exponent
      (E.lox false) (E.lox true) false ms q s x hqread
    rw [hx]
    have hloxfam : E.lox s ∈ E.rel.fam s := by
      rw [E.fam_eq]
      exact E.lox_mem s
    cases s <;> simpa using pow_mem hloxfam m
  · rw [hc] at hread
    let M := RelWord.revInv
      (relatorWord₂ p (E.lox false) (E.lox true) ms)
    have hi : i < M.length := by
      have := (List.getElem?_eq_some_iff.mp hread).choose
      simpa only [M, List.length_rotate] using this
    have hraw := getElem?_of_rotate hi hread
    let t := (c + i) % M.length
    change M[t]? = some (GGT.RelLetter.comp s x) at hraw
    obtain ⟨ht, hbi⟩ := blockIndex_of_revInv_relatorWord₂ hraw
    have htq : t + (ms.length - 1 - t) + 1 = ms.length := by omega
    obtain ⟨m, -, hx⟩ := revInv_blockWord_getElem?_exponent
      (E.lox false) (E.lox true) false ms htq hbi
    rw [hx]
    have hloxfam : E.lox s ∈ E.rel.fam s := by
      rw [E.fam_eq]
      exact E.lox_mem s
    apply (E.rel.fam s).inv_mem
    simpa only [ite_apply_eq] using pow_mem hloxfam m

/-- A bounded positive span between two actual component letters of the same
index in a prefix of a symmetrized relator is excluded by the exact cyclic
dispatchers. -/
theorem ExactRelatorDesign₂.forwardSpan_not_mem
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (h : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    (heven : Even ms.length)
    {v u tl : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hu : v = u ++ tl) {a b : ℕ} (hab : a < b) (hb : b < u.length)
    {s : Bool} {x y : G}
    (haRead : u[a]? = some (GGT.RelLetter.comp s x))
    (hbRead : u[b]? = some (GGT.RelLetter.comp s y))
    (hgap : b - a ≤ W) :
    (GGT.OsinComponents.vertex (1 : G) u a)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u b ∉ E.rel.fam s := by
  have ha : a < u.length := by omega
  have hvaRead : v[a]? = some (GGT.RelLetter.comp s x) := by
    rw [hu, List.getElem?_append_left ha]
    exact haRead
  have hvbRead : v[b]? = some (GGT.RelLetter.comp s y) := by
    rw [hu, List.getElem?_append_left hb]
    exact hbRead
  have hva : GGT.OsinComponents.vertex (1 : G) v a =
      GGT.OsinComponents.vertex (1 : G) u a := by
    rw [hu]
    exact GGT.OsinComponents.vertex_append_of_le u tl 1 a (by omega)
  have hvb : GGT.OsinComponents.vertex (1 : G) v b =
      GGT.OsinComponents.vertex (1 : G) u b := by
    rw [hu]
    exact GGT.OsinComponents.vertex_append_of_le u tl 1 b (by omega)
  have hbV : b < v.length := by rw [hu, List.length_append]; omega
  intro hmem
  rcases hv.exists_rotate with ⟨c, hc⟩ | ⟨c, hc⟩
  · let R := relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms
    have hbR : b < R.length := by rw [← hv.length_eq]; exact hbV
    have haR : a < R.length := by omega
    have hhead : (R.rotate (c + a))[0]? =
        some (GGT.RelLetter.comp s x) := by
      rw [← getElem?_rotate_at haR, ← hc]
      exact hvaRead
    have hend : (R.rotate (c + a))[b - a]? =
        some (GGT.RelLetter.comp s y) := by
      calc
        (R.rotate (c + a))[b - a]? =
            (R.rotate (c + a + (b - a)))[0]? :=
          getElem?_rotate_at (by omega)
        _ = (R.rotate (c + b))[0]? := by rw [show c + a + (b - a) = c + b by omega]
        _ = (R.rotate c)[b]? := (getElem?_rotate_at hbR).symm
        _ = v[b]? := by rw [hc]
        _ = _ := hvbRead
    have hspan :
        (GGT.OsinComponents.vertex (1 : G) u a)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) u b =
          GGT.RelLetter.listVal ((R.rotate (c + a)).take (b - a)) := by
      rw [← hva, ← hvb, hc]
      exact span_rotate_eq_listVal_take_rotate R (le_of_lt hab) (by omega)
    rw [hspan] at hmem
    exact h.directCyclicPrefix_not_mem E heven (by omega) hgap hhead hend hmem
  · let R := relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms
    let M := RelWord.revInv R
    have hbR : b < R.length := by rw [← hv.length_eq]; exact hbV
    have hbM : b < M.length := by
      simpa only [M, RelWord.length_revInv] using hbR
    have haM : a < M.length := by omega
    have hhead : (M.rotate (c + a))[0]? =
        some (GGT.RelLetter.comp s x) := by
      rw [← getElem?_rotate_at haM, ← hc]
      exact hvaRead
    have hend : (M.rotate (c + a))[b - a]? =
        some (GGT.RelLetter.comp s y) := by
      calc
        (M.rotate (c + a))[b - a]? =
            (M.rotate (c + a + (b - a)))[0]? :=
          getElem?_rotate_at (by omega)
        _ = (M.rotate (c + b))[0]? := by rw [show c + a + (b - a) = c + b by omega]
        _ = (M.rotate c)[b]? := (getElem?_rotate_at hbM).symm
        _ = v[b]? := by rw [hc]
        _ = _ := hvbRead
    have hspan :
        (GGT.OsinComponents.vertex (1 : G) u a)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) u b =
          GGT.RelLetter.listVal ((M.rotate (c + a)).take (b - a)) := by
      rw [← hva, ← hvb, hc]
      exact span_rotate_eq_listVal_take_rotate M (le_of_lt hab) (by
        exact le_of_lt hbM)
    rw [hspan] at hmem
    exact h.revInvCyclicPrefix_not_mem E heven (by omega) hgap hhead hend hmem

/-- The exact finite-avoidance design supplies both same-side exclusions; no
additional side-exclusion hypothesis is needed. -/
theorem sideExclusionOfExactDesign₂ (E : HypEmbeddedCore₂ A N) (cnt : ℕ) :
    SideExclusionOfExactDesign₂ E cnt := by
  intro hcount baseLetter hbase eps rho epsD Cm target ms heven hdesign hlong
    py pz u u' huSym hu'Sym hpy hpz hpy0 hpz0
  let W := 1 + blockConst [baseLetter] (max cnt (eps + 2))
  have hmsEven : Even ms.length := by
    rw [hdesign.1]
    exact heven
  have hW : 1 + blockConst [baseLetter] cnt ≤ W := by
    simp only [W, blockConst, List.length_singleton]
    omega
  constructor
  · intro s d i hdcomp hi hine hstart hmem
    obtain ⟨v, tl, hv, hu⟩ := huSym
    have hdlt : d < u.length := by exact lt_of_lt_of_le hdcomp.1 hdcomp.2.1
    have hdOf := hdcomp.2.2.1 d (le_refl d) (by omega) hdlt
    obtain ⟨xd, hdRead⟩ := getElem?_comp_of_isCompOf hdlt hdOf
    obtain ⟨hilt, xi, hiRead⟩ :=
      exists_comp_letter_of_firstLongSide_start hpz hpz0 hi hstart
    have hwindow := index_window_of_blockCount E cnt hcount
      (by simp) hv hu (d := d) (i := i) (by omega) (by omega) hmem
    rcases hwindow with ⟨hdi, hgap⟩ | ⟨hid, hgap⟩
    · have hdilt : d < i := lt_of_le_of_ne hdi (Ne.symm hine)
      exact hdesign.forwardSpan_not_mem E hmsEven hv hu hdilt hilt hdRead hiRead
        (le_trans hgap hW) hmem
    · have hidlt : i < d := lt_of_le_of_ne hid hine
      have hspanMem :
          (GGT.OsinComponents.vertex (1 : G) u i)⁻¹ *
              GGT.OsinComponents.vertex (1 : G) u d ∈ E.rel.fam s := by
        have := (E.rel.fam s).inv_mem hmem
        simpa [mul_inv_rev] using this
      exact hdesign.forwardSpan_not_mem E hmsEven hv hu hidlt hdlt hiRead hdRead
        (le_trans hgap hW) hspanMem
  · intro s k m hkcomp hm hmne hstart hmem
    obtain ⟨v, tl, hv, hu⟩ := hu'Sym
    obtain ⟨j, hjk, hjcomp⟩ := hkcomp
    have hjlt : j < u'.length :=
      lt_of_lt_of_le hjcomp.1 hjcomp.2.1
    have hklen : k ≤ u'.length := by simpa only [hjk] using hjcomp.2.1
    have hjOf := hjcomp.2.2.1 j (le_refl j) (by omega) hjlt
    obtain ⟨xj, hjRead⟩ := getElem?_comp_of_isCompOf hjlt hjOf
    obtain ⟨hm0, xm, hmRead⟩ :=
      exists_comp_letter_of_secondLongSide_start hm hstart
    let r := m - 1
    have hrlt : r < u'.length := by simp only [r]; omega
    have hkmem : xj ∈ E.rel.fam s :=
      comp_value_mem_fam_of_sym_relator₂ E hv (by
        rw [hu, List.getElem?_append_left hjlt]
        exact hjRead)
    have hrmem : xm ∈ E.rel.fam s :=
      comp_value_mem_fam_of_sym_relator₂ E hv (by
        rw [hu, List.getElem?_append_left hrlt]
        exact hmRead)
    have hjk' : j + 1 = k := hjk
    have hrm : r + 1 = m := by simp only [r]; omega
    have hjstep := vertex_succ_of_getElem? u' j (1 : G)
      (GGT.RelLetter.comp s xj) hjRead
    have hrstep := vertex_succ_of_getElem? u' r (1 : G)
      (GGT.RelLetter.comp s xm) hmRead
    simp only [GGT.RelLetter.val] at hjstep hrstep
    have hwindow := index_window_of_blockCount E cnt hcount
      (by simp) hv hu (d := k) (i := m) hklen hm hmem
    rcases hwindow with ⟨hkm, hgap⟩ | ⟨hmk, hgap⟩
    · have hjr : j < r := by omega
      have hshiftMem :
          (GGT.OsinComponents.vertex (1 : G) u' j)⁻¹ *
              GGT.OsinComponents.vertex (1 : G) u' r ∈ E.rel.fam s := by
        have heq :
            (GGT.OsinComponents.vertex (1 : G) u' j)⁻¹ *
                GGT.OsinComponents.vertex (1 : G) u' r =
              xj * ((GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
                GGT.OsinComponents.vertex (1 : G) u' m) * xm⁻¹ := by
          rw [← hjk', ← hrm, hjstep, hrstep]
          group
        rw [heq]
        exact (E.rel.fam s).mul_mem
          ((E.rel.fam s).mul_mem hkmem hmem) ((E.rel.fam s).inv_mem hrmem)
      exact hdesign.forwardSpan_not_mem E hmsEven hv hu hjr hrlt hjRead hmRead
        (by omega) hshiftMem
    · have hrj : r < j := by omega
      have hshiftMem :
          (GGT.OsinComponents.vertex (1 : G) u' r)⁻¹ *
              GGT.OsinComponents.vertex (1 : G) u' j ∈ E.rel.fam s := by
        have heq :
            (GGT.OsinComponents.vertex (1 : G) u' r)⁻¹ *
                GGT.OsinComponents.vertex (1 : G) u' j =
              xm * (((GGT.OsinComponents.vertex (1 : G) u' k)⁻¹ *
                GGT.OsinComponents.vertex (1 : G) u' m)⁻¹) * xj⁻¹ := by
          rw [← hjk', ← hrm, hjstep, hrstep]
          group
        rw [heq]
        exact (E.rel.fam s).mul_mem
          ((E.rel.fam s).mul_mem hrmem ((E.rel.fam s).inv_mem hmem))
          ((E.rel.fam s).inv_mem hkmem)
      exact hdesign.forwardSpan_not_mem E hmsEven hv hu hrj hjlt hmRead hjRead
        (by omega) hshiftMem

/-- The exact separation clause now needs only the block-count estimate; its
formerly external same-side input is supplied by the exact design itself. -/
theorem separationNe₂_clause_of_exactDesign
    (E : HypEmbeddedCore₂ A N) (hN : Suitable A.alphabet N) (cnt : ℕ) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ)
    (hcount : RelatorBlockCountInputOne₂ E cnt)
    (t : G) (ht : t⁻¹ ∈ E.rel.base) (eps rho : ℕ) :
    ∃ B : ℕ, ∀ L : ℕ, ∃ (p : List G) (ms : List ℕ),
      (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
        (∀ m ∈ ms, ∀ b : Bool, E.lox b ^ m ∉ E.rel.relBall b rho ∧
          (E.lox b ^ m)⁻¹ ∉ E.rel.relBall b rho) ∧
        ∀ w w' u₀ u₀' : List (GGT.RelLetter G Bool),
          RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w →
            RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) w' →
              w' ≠ w → (∃ s, w = u₀ ++ s) → (∃ s', w' = u₀' ++ s') →
                B < u₀.length → ∀ y z : G,
                  wordNorm E.rel.base y ≤ eps → wordNorm E.rel.base z ≤ eps →
                    GGT.RelLetter.listVal u₀' =
                        y * GGT.RelLetter.listVal u₀ * z →
                      GGT.RelLetter.listVal w' =
                        y * GGT.RelLetter.listVal w * y⁻¹ :=
  separationNe₂_clause_of_exactDesign_of_sideExclusion E hN cnt hδ hcount
    (sideExclusionOfExactDesign₂ E cnt) t ht eps rho

section QuantifiedCount

variable
  (hcountClosure : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G)
    (N : Subgroup G) (E : HypEmbeddedCore₂ A N),
      ∃ cnt : ℕ, RelatorBlockCountInputOne₂ E cnt)

include hcountClosure in
/-- Quantified exact separation with the obsolete side-closure conjunct
removed from its sole remaining geometric input. -/
theorem separationNe₂OfBaseLetter_of_exactDesign :
    ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
      (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
        ∀ (t : G), t⁻¹ ∈ E.rel.base → ∀ (eps rho : ℕ),
          ∃ B : ℕ, ∀ L : ℕ,
            ∃ (p : List G) (ms : List ℕ),
              (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
                (∀ m ∈ ms, ∀ b : Bool,
                  E.lox b ^ m ∉ E.rel.relBall b rho ∧
                    (E.lox b ^ m)⁻¹ ∉ E.rel.relBall b rho) ∧
                ∀ w w' u₀ u₀' : List (GGT.RelLetter G Bool),
                  RelWord.Sym
                      (relatorWord₂ p (E.lox false) (E.lox true) ms) w →
                    RelWord.Sym
                        (relatorWord₂ p (E.lox false) (E.lox true) ms) w' →
                      w' ≠ w → (∃ s, w = u₀ ++ s) →
                        (∃ s', w' = u₀' ++ s') → B < u₀.length →
                          ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                            wordNorm E.rel.base z ≤ eps →
                              GGT.RelLetter.listVal u₀' =
                                  y * GGT.RelLetter.listVal u₀ * z →
                                GGT.RelLetter.listVal w' =
                                  y * GGT.RelLetter.listVal w * y⁻¹ := by
  intro G _ A N E hN t ht eps rho
  obtain ⟨cnt, hcount⟩ := hcountClosure A N E
  obtain ⟨δ, hδ⟩ :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded E.rel E.embedded
  exact separationNe₂_clause_of_exactDesign E hN cnt hδ hcount
    t ht eps rho

include hcountClosure in
/-- The corrected one-letter relator endpoint, conditional only on Hull's
block-count item and not on any finite-avoidance or side-exclusion input. -/
theorem hullRelatorStatement₂OfBaseLetter_of_exactDesign :
    HullRelatorStatement₂OfBaseLetter.{u} :=
  hullRelatorStatement₂OfBaseLetter_of_separationNe₂
    (separationNe₂OfBaseLetter_of_exactDesign hcountClosure)

end QuantifiedCount

end ExactSide

end HullSC
end GroupApproximation
