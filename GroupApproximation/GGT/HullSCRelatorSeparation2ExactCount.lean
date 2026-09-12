import GroupApproximation.GGT.HullSCRelatorSeparation2CountGeometry
import GroupApproximation.GGT.HullSCRelatorSeparation2ExactSideExclusion
import GroupApproximation.GGT.HullSCRelatorSeparation2BaseCount
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyComp
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.GGT.OsinTheorem54SepSegmentVertex
import GroupApproximation.GGT.DGOQuasiGeodesicChainAt

/-!
# The exact relator block count

This module applies the every-edge geodesic-bigon estimate to the one exact
relator selected by `ExactRelatorDesign₂`.  The producer fixes a target length,
uses the corresponding every-edge isolation radius as its depth threshold, and
uses the whole target as its cyclic-avoidance window.  The resulting block
count has constant `1`, independent of the selected exponent list.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section Positions

variable {G : Type u} [Group G] {Lambda : Type v}

/-- Positions carrying a peripheral letter, indexed recursively so no equality
test on the group element is needed. -/
def componentPositions : List (GGT.RelLetter G Lambda) → Finset ℕ
  | [] => ∅
  | GGT.RelLetter.base _ :: t =>
      (componentPositions t).map ⟨Nat.succ, Nat.succ_injective⟩
  | GGT.RelLetter.comp _ _ :: t =>
      insert 0 ((componentPositions t).map ⟨Nat.succ, Nat.succ_injective⟩)

omit [Group G] in
theorem card_componentPositions (w : List (GGT.RelLetter G Lambda)) :
    (componentPositions w).card = compCount w := by
  induction w with
  | nil => rfl
  | cons a t ih =>
      cases a with
      | base g => simpa [componentPositions, compCount] using ih
      | comp lam g =>
          have hzero : 0 ∉ (componentPositions t).map
              ⟨Nat.succ, Nat.succ_injective⟩ := by simp
          rw [componentPositions, Finset.card_insert_of_notMem hzero,
            Finset.card_map, ih]
          rfl

omit [Group G] in
theorem mem_componentPositions_iff {w : List (GGT.RelLetter G Lambda)} {i : ℕ} :
    i ∈ componentPositions w ↔
      ∃ lam : Lambda, ∃ g : G, w[i]? = some (GGT.RelLetter.comp lam g) := by
  induction w generalizing i with
  | nil => simp [componentPositions]
  | cons a t ih =>
      cases a with
      | base g =>
          cases i with
          | zero => simp [componentPositions]
          | succ i => simp [componentPositions, ih]
      | comp lam g =>
          cases i with
          | zero => simp [componentPositions]
          | succ i => simp [componentPositions, ih]

omit [Group G] in
/-- Erasing one possible boundary component loses at most one count. -/
theorem card_componentPositions_le_card_erase_add_one
    (w : List (GGT.RelLetter G Lambda)) (i : ℕ) :
    compCount w ≤ ((componentPositions w).erase i).card + 1 := by
  rw [← card_componentPositions]
  by_cases hi : i ∈ componentPositions w
  · rw [Finset.card_erase_add_one hi]
  · rw [Finset.erase_eq_of_notMem hi]
    omega

end Positions

section SegmentComponent

variable {G : Type u} [Group G] {Lambda : Type v}

omit [Group G] in
/-- A singleton component of a word restricts to a singleton component of a
segment when its successor remains inside that segment. -/
theorem isComp_segment_of_singleton
    (lam : Lambda) (w : List (GGT.RelLetter G Lambda))
    {i m x : ℕ} (hcomp : GGT.OsinComponents.IsComp lam w (i + x) (i + x + 1))
    (him : i + m ≤ w.length) (hx : x + 1 < m) :
    GGT.OsinComponents.IsComp lam ((w.drop i).take m) x (x + 1) := by
  have hlen : ((w.drop i).take m).length = m :=
    GGT.OsinComponents.length_segment w i m him
  obtain ⟨-, -, hrange, hpre, hpost⟩ := hcomp
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro a hxa hax ha
    have haeq : a = x := by omega
    subst a
    have hwx : i + x < w.length := by omega
    rw [← GGT.OsinComponents.getElem_segment' w i m x (i + x) ha hwx rfl]
    exact hrange (i + x) (le_refl _) (by omega) hwx
  · intro a hxa ha hc
    have hix : i + x = (i + a) + 1 := by omega
    have hwa : i + a < w.length := by omega
    rw [← GGT.OsinComponents.getElem_segment' w i m a (i + a) ha hwa rfl] at hc
    exact hpre (i + a) hix hwa hc
  · intro hk hc
    have hwk : i + (x + 1) < w.length := by omega
    rw [← GGT.OsinComponents.getElem_segment' w i m (x + 1) (i + x + 1)
      hk hwk (by omega)] at hc
    exact hpost hwk hc

omit [Group G] in
/-- A component ending strictly inside a prefix remains maximal after a suffix
is appended. -/
theorem isComp_append_of_lt_exactCount {lam : Lambda}
    {q r : List (GGT.RelLetter G Lambda)} {i k : ℕ}
    (h : GGT.OsinComponents.IsComp lam q i k) (hk : k < q.length) :
    GGT.OsinComponents.IsComp lam (q ++ r) i k := by
  rcases h with ⟨hik, hkq, hrange, hpre, hpost⟩
  refine ⟨hik, by simp; omega, ?_, ?_, ?_⟩
  · intro j hij hjk hjqr
    have hjq : j < q.length := by omega
    rw [List.getElem_append_left hjq]
    exact hrange j hij hjk hjq
  · intro j hij hjqr
    have hjq : j < q.length := by omega
    rw [List.getElem_append_left hjq]
    exact hpre j hij hjq
  · intro hkqr
    rw [List.getElem_append_left hk]
    exact hpost hk

end SegmentComponent

section ExactLetters

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- Every member of the symmetrized one-base-letter relator is admissible. -/
theorem admissible_of_sym_exactRelator
    (E : HypEmbeddedCore₂ A N) {baseLetter : G} (hbase : baseLetter ∈ E.rel.base)
    {ms : List ℕ} {v : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v) :
    ∀ a ∈ v, E.rel.IsLetter a := by
  have hrel : ∀ a ∈ relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms,
      E.rel.IsLetter a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · simp only [List.mem_map, List.mem_singleton] at ha
      obtain ⟨g, rfl, rfl⟩ := ha
      exact hbase
    · obtain ⟨s, m, -, haeq⟩ :=
        mem_blockWord (E.lox false) (E.lox true) false ms a ha
      rw [haeq]
      have hloxfam : E.lox s ∈ E.rel.fam s := by
        rw [E.fam_eq]
        exact E.lox_mem s
      cases s <;> exact pow_mem hloxfam m
  intro a ha
  rcases hv.letters a ha with ha | ha
  · exact hrel a ha
  · have hinv := RelWord.isLetter_inv
      (D := E.rel) (isSymmetricGeneratingSet_base₂ E).inv_mem (hrel _ ha)
    rwa [RelWord.inv_inv_letter] at hinv

/-- A peripheral letter of a symmetrized exact relator is one of the selected
deep powers, possibly formally inverted. -/
theorem comp_value_not_mem_relBall_of_sym_exactRelator
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    {v : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    {i : ℕ} {s : Bool} {x : G}
    (hread : v[i]? = some (GGT.RelLetter.comp s x)) :
    x ∉ E.rel.relBall s rho := by
  rcases hv.exists_rotate with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [hc] at hread
    have hi : i < (relatorWord₂ [baseLetter]
        (E.lox false) (E.lox true) ms).length := by
      simpa only [List.length_rotate] using (List.getElem?_eq_some_iff.mp hread).1
    have hraw := getElem?_of_rotate hi hread
    obtain ⟨q, -, -, hqread⟩ := blockIndex_of_relatorWord₂ hraw
    obtain ⟨m, hm, hx⟩ := blockWord_getElem?_exponent
      (E.lox false) (E.lox true) false ms q s x hqread
    rw [hx]
    have hdeep := (hdesign.2.2.1 m (List.mem_of_getElem? hm) s s).1
    cases s <;> simpa using hdeep
  · rw [hc] at hread
    let M := RelWord.revInv
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms)
    have hi : i < M.length := by
      simpa only [M, List.length_rotate] using
        (List.getElem?_eq_some_iff.mp hread).1
    have hraw := getElem?_of_rotate hi hread
    let t := (c + i) % M.length
    change M[t]? = some (GGT.RelLetter.comp s x) at hraw
    obtain ⟨ht, hbi⟩ := blockIndex_of_revInv_relatorWord₂ hraw
    have htq : t + (ms.length - 1 - t) + 1 = ms.length := by omega
    obtain ⟨m, hm, hx⟩ := revInv_blockWord_getElem?_exponent
      (E.lox false) (E.lox true) false ms htq hbi
    rw [hx]
    have hdeep := (hdesign.2.2.1 m (List.mem_of_getElem? hm) s s).2
    cases s <;> simpa using hdeep

/-- Every peripheral letter of a symmetrized one-base-letter relator is its own
component. -/
theorem isComp_of_sym_exactRelator
    (E : HypEmbeddedCore₂ A N) {baseLetter : G} {ms : List ℕ}
    {v : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    {i : ℕ} {s : Bool} {x : G}
    (hread : v[i]? = some (GGT.RelLetter.comp s x)) :
    GGT.OsinComponents.IsComp s v i (i + 1) := by
  rcases hv.exists_rotate with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [hc] at hread ⊢
    exact isComp_rotate_relatorWord₂ (p := [baseLetter]) (by simp) hread
  · rw [hc] at hread ⊢
    exact isComp_rotate_revInv_relatorWord₂ (p := [baseLetter]) (by simp) hread

end ExactLetters

section ExactCount

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The useful fixed-list count from an exact design.**

One possible last component of the near segment is discarded because it can
merge with the first component of the reversed geodesic chord.  Together with
the unique base letter this costs two letters, i.e. `blockConst [baseLetter] 1`.
The constant `1` is absolute; the depth radius and avoidance window depend only
on the producer's target. -/
theorem ExactRelatorDesign₂.blockCountAt_one
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    (hbase : baseLetter ∈ E.rel.base)
    {delta : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier delta)
    (heven : Even ms.length)
    (hW : target + 1 ≤ W)
    (hrho : GGT.OsinComponents.everyEdgeIsolationRadius delta
      (2 * (target + 1)) ≤ rho) :
    RelatorBlockCountAt₂ E [baseLetter] ms 1 := by
  classical
  intro v hv i j hij hj
  let m := j - i
  let u := (v.drop i).take m
  let f := GGT.OsinComponents.vertex (1 : G) v i
  have hvlen : v.length = target + 1 := by
    rw [hv.length_eq, length_relatorWord₂, hdesign.1]
    simp [Nat.add_comm]
  have him : i + m ≤ v.length := by
    dsimp only [m]
    omega
  have hulen : u.length = m := by
    exact GGT.OsinComponents.length_segment v i m him
  have huTarget : u.length ≤ target + 1 := by omega
  have hvletters := admissible_of_sym_exactRelator E hbase hv
  have huletters : ∀ a ∈ u, E.rel.IsLetter a := by
    intro a ha
    exact hvletters a (List.drop_subset i v (List.take_subset m _ ha))
  obtain ⟨q, hq⟩ := GGT.OsinComponents.existsGeodesicWord E.rel f
    (GGT.OsinComponents.vertex (1 : G) v j)
  have hqend : GGT.OsinComponents.vertex (1 : G) v j =
      GGT.OsinComponents.vertex f u u.length := by
    rw [hulen, show j = i + m by dsimp only [m]; omega]
    exact (GGT.OsinComponents.vertex_segment v 1 i m m (le_refl _)).symm
  have hq' : GGT.OsinComponents.IsGeodesicWord E.rel f
      (GGT.OsinComponents.vertex f u u.length) q := by
    rwa [← hqend]
  let figure := u ++ GGT.OsinComponents.revWord q
  let S := (componentPositions u).erase (u.length - 1)
  let Ss (s : Bool) := S.filter fun x =>
    ∃ g : G, u[x]? = some (GGT.RelLetter.comp s g)
  let Qs (s : Bool) := (Finset.range q.length).filter fun y =>
    GGT.OsinComponents.IsCompStart s figure (u.length + y)
  have hSread (s : Bool) {x : ℕ} (hx : x ∈ Ss s) :
      ∃ g : G, u[x]? = some (GGT.RelLetter.comp s g) := by
    exact (Finset.mem_filter.mp hx).2
  have hSbase {s : Bool} {x : ℕ} (hx : x ∈ Ss s) : x ∈ S :=
    (Finset.mem_filter.mp hx).1
  have hSpos {s : Bool} {x : ℕ} (hx : x ∈ Ss s) : x < u.length := by
    obtain ⟨g, hg⟩ := hSread s hx
    exact (List.getElem?_eq_some_iff.mp hg).1
  have hSinside {s : Bool} {x : ℕ} (hx : x ∈ Ss s) : x + 1 < u.length := by
    have hxne : x ≠ u.length - 1 := (Finset.mem_erase.mp (hSbase hx)).1
    have hxlt := hSpos hx
    omega
  have hreadV {s : Bool} {x : ℕ} (hx : x ∈ Ss s) :
      ∃ g : G, v[i + x]? = some (GGT.RelLetter.comp s g) := by
    obtain ⟨g, hg⟩ := hSread s hx
    refine ⟨g, ?_⟩
    have hxm : x < m := by rw [← hulen]; exact hSpos hx
    simpa only [u, List.getElem?_take, List.getElem?_drop, if_pos hxm] using hg
  have hcomponentDeep (s : Bool) {x : ℕ} (hx : x ∈ Ss s) :
      ∃ k : ℕ, GGT.OsinComponents.IsComp s figure x k ∧
        (GGT.OsinComponents.vertex f figure x)⁻¹ *
          GGT.OsinComponents.vertex f figure k ∉ E.rel.relBall s rho := by
    obtain ⟨g, hgU⟩ := hSread s hx
    obtain ⟨g', hgV⟩ := hreadV hx
    have hgg : g' = g := by
      have hgU' : u[x]? = v[i + x]? := by
        have hxm : x < m := by rw [← hulen]; exact hSpos hx
        simp only [u, List.getElem?_take, List.getElem?_drop, if_pos hxm]
      rw [hgU', hgV] at hgU
      exact (GGT.RelLetter.comp.inj (Option.some.inj hgU)).2
    subst g'
    have hcompV := isComp_of_sym_exactRelator E hv hgV
    have hcompU := isComp_segment_of_singleton s v hcompV him (by
      rw [← hulen]
      exact hSinside hx)
    have hcompFigure : GGT.OsinComponents.IsComp s figure x (x + 1) := by
      exact isComp_append_of_lt_exactCount hcompU (hSinside hx)
    refine ⟨x + 1, hcompFigure, ?_⟩
    have hgFig : figure[x]? = some (GGT.RelLetter.comp s g) := by
      rw [show figure = u ++ GGT.OsinComponents.revWord q by rfl,
        List.getElem?_append_left (hSpos hx)]
      exact hgU
    have hstep := vertex_succ_of_getElem?
      figure x f (GGT.RelLetter.comp s g) hgFig
    simp only [GGT.RelLetter.val] at hstep
    have hspan : (GGT.OsinComponents.vertex f figure x)⁻¹ *
        GGT.OsinComponents.vertex f figure (x + 1) = g := by
      rw [hstep]
      group
    rw [hspan]
    exact comp_value_not_mem_relBall_of_sym_exactRelator E hdesign hv hgV
  have hsideSep (s : Bool) :
      ∀ x : ℕ, x < u.length → ∀ y : ℕ, y < u.length → x ≠ y →
        GGT.OsinComponents.IsCompStart s figure x →
        GGT.OsinComponents.IsCompStart s figure y →
        ¬ GGT.OsinComponents.Connected E.rel.fam s f figure x y := by
    intro x hx y hy hxy hxStart hyStart hcon
    have hfigx : GGT.OsinComponents.vertex f figure x =
        GGT.OsinComponents.vertex (1 : G) v (i + x) := by
      rw [show figure = u ++ GGT.OsinComponents.revWord q by rfl,
        GGT.OsinComponents.vertex_append_of_le u _ f x (by omega),
        GGT.OsinComponents.vertex_segment v 1 i m x (by omega)]
    have hfigy : GGT.OsinComponents.vertex f figure y =
        GGT.OsinComponents.vertex (1 : G) v (i + y) := by
      rw [show figure = u ++ GGT.OsinComponents.revWord q by rfl,
        GGT.OsinComponents.vertex_append_of_le u _ f y (by omega),
        GGT.OsinComponents.vertex_segment v 1 i m y (by omega)]
    rw [GGT.OsinComponents.Connected, hfigx, hfigy] at hcon
    obtain ⟨kx, hkx⟩ := hxStart
    obtain ⟨gx, hxFig⟩ := getElem?_comp_of_isCompOf
      (lt_of_lt_of_le hkx.1 hkx.2.1)
      (hkx.2.2.1 x (le_refl _) hkx.1 (lt_of_lt_of_le hkx.1 hkx.2.1))
    have hxU : u[x]? = some (GGT.RelLetter.comp s gx) := by
      rw [show figure = u ++ GGT.OsinComponents.revWord q by rfl,
        List.getElem?_append_left hx] at hxFig
      exact hxFig
    have hxV : v[i + x]? = some (GGT.RelLetter.comp s gx) := by
      have hxm : x < m := by rw [← hulen]; exact hx
      simpa only [u, List.getElem?_take, List.getElem?_drop, if_pos hxm] using hxU
    obtain ⟨ky, hky⟩ := hyStart
    obtain ⟨gy, hyFig⟩ := getElem?_comp_of_isCompOf
      (lt_of_lt_of_le hky.1 hky.2.1)
      (hky.2.2.1 y (le_refl _) hky.1 (lt_of_lt_of_le hky.1 hky.2.1))
    have hyU : u[y]? = some (GGT.RelLetter.comp s gy) := by
      rw [show figure = u ++ GGT.OsinComponents.revWord q by rfl,
        List.getElem?_append_left hy] at hyFig
      exact hyFig
    have hyV : v[i + y]? = some (GGT.RelLetter.comp s gy) := by
      have hym : y < m := by rw [← hulen]; exact hy
      simpa only [u, List.getElem?_take, List.getElem?_drop, if_pos hym] using hyU
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact hdesign.forwardSpan_not_mem E heven hv (u := v) (tl := []) (by simp)
        (by omega) (by omega)
        hxV hyV (le_trans (by omega) hW) hcon
    · have hcon' :
          (GGT.OsinComponents.vertex (1 : G) v (i + y))⁻¹ *
              GGT.OsinComponents.vertex (1 : G) v (i + x) ∈ E.rel.fam s := by
        have := (E.rel.fam s).inv_mem hcon
        simpa [mul_inv_rev] using this
      exact hdesign.forwardSpan_not_mem E heven hv (u := v) (tl := []) (by simp)
        (by omega) (by omega)
        hyV hxV (le_trans (by omega) hW) hcon'
  have hcard (s : Bool) : (Ss s).card ≤ (Qs s).card := by
    apply GGT.OsinComponents.card_le_card_of_boundedGeodesicBigon
      E.rel (isSymmetricGeneratingSet_base₂ E).inv_mem hdelta s f u q
      (Ss s) (Qs s) huletters hq' huTarget hrho
    · intro x hx
      exact hSpos hx
    · intro x hx
      simpa only [figure] using hcomponentDeep s hx
    · simpa only [figure] using hsideSep s
    · intro y hy hstart
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hy, by simpa only [figure] using hstart⟩
  have hSdisjoint : Disjoint (Ss false) (Ss true) := by
    rw [Finset.disjoint_left]
    intro x hxf hxt
    obtain ⟨gf, hf⟩ := hSread false hxf
    obtain ⟨gt, ht⟩ := hSread true hxt
    rw [hf] at ht
    cases ht
  have hSunion : Ss false ∪ Ss true = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hSbase hx
      · exact hSbase hx
    · intro hx
      have hxcomp : x ∈ componentPositions u := (Finset.mem_erase.mp hx).2
      obtain ⟨s, g, hread⟩ := mem_componentPositions_iff.mp hxcomp
      cases s with
      | false =>
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, ⟨g, hread⟩⟩)
      | true =>
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, ⟨g, hread⟩⟩)
  have hScard : S.card = (Ss false).card + (Ss true).card := by
    rw [← hSunion]
    exact Finset.card_union_of_disjoint hSdisjoint
  have hQsubset (s : Bool) : Qs s ⊆ Finset.range q.length := by
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  have hQdisjoint : Disjoint (Qs false) (Qs true) := by
    rw [Finset.disjoint_left]
    intro y hyf hyt
    have hf := (Finset.mem_filter.mp hyf).2
    have ht := (Finset.mem_filter.mp hyt).2
    exact (GGT.OsinComponents.not_isCompStart_of_ne (by decide) hf) ht
  have hQcard : (Qs false).card + (Qs true).card ≤ q.length :=
    GGT.OsinComponents.card_add_card_le_of_subset_range
      (hQsubset false) (hQsubset true) hQdisjoint
  have hSle : S.card ≤ q.length := by
    rw [hScard]
    exact le_trans (Nat.add_le_add (hcard false) (hcard true)) hQcard
  have hcompErase := card_componentPositions_le_card_erase_add_one
    u (u.length - 1)
  have hrange := compCount_range_ge hv hij hj
  simp only [List.length_singleton, Nat.add_comm] at hrange
  have hrange' : m ≤ compCount u + 1 := by
    dsimp only [m, u]
    omega
  have hqlen : q.length = wordDist E.rel.alphabet.carrier
      (GGT.OsinComponents.vertex (1 : G) v i)
      (GGT.OsinComponents.vertex (1 : G) v j) := by
    simpa only [f, hqend] using hq'.2.2
  simp only [blockConst]
  rw [← hqlen]
  change j - i ≤ q.length + (1 + 1)
  dsimp only [S] at hSle hcompErase
  dsimp only [m] at hrange'
  omega

/-- **The uniform fixed-list count gives Hull's published `(4,1)`
quasi-geodesicity for every member of the symmetrized relator family.**

The count with the one-letter base and count constant `1` says that every
subpath has length at most its endpoint distance plus `2`.  This is stronger
than the required real lower bound `length / 4 - 1 ≤ distance`; the upper
bound is the standard admissible-word estimate. -/
theorem quasiGeodesic_sym_of_blockCountAt₂
    (E : HypEmbeddedCore₂ A N) {baseLetter : G} {ms : List ℕ}
    (hbase : baseLetter ∈ E.rel.base)
    (hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1) :
    ∀ v, RelWord.Sym
        (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v →
      GGT.IsQuasiGeodesicChainAt E.rel.alphabet.carrier 4 1
        (fun i => GGT.RelLetter.listVal (v.take i)) v.length := by
  intro v hv i j hij hj
  have hcountij := hcount v hv i j hij hj
  have hletters := admissible_of_sym_exactRelator E hbase hv
  have hupper := GGT.OsinComponents.wordDist_vertex_le E.rel hletters hij hj
  have hvi : GGT.OsinComponents.vertex (1 : G) v i =
      GGT.RelLetter.listVal (v.take i) := by
    rw [GGT.OsinComponents.vertex_eq_mul_listVal_take, one_mul]
  have hvj : GGT.OsinComponents.vertex (1 : G) v j =
      GGT.RelLetter.listVal (v.take j) := by
    rw [GGT.OsinComponents.vertex_eq_mul_listVal_take, one_mul]
  rw [hvi, hvj] at hcountij hupper
  refine ⟨?_, hupper⟩
  simp only [blockConst, List.length_singleton] at hcountij
  have hcountReal : ((j - i : ℕ) : ℝ) ≤
      (wordDist E.rel.alphabet.carrier
        (GGT.RelLetter.listVal (v.take i))
        (GGT.RelLetter.listVal (v.take j)) : ℕ) + 2 := by
    exact_mod_cast hcountij
  have hdist : (0 : ℝ) ≤
      ((wordDist E.rel.alphabet.carrier
        (GGT.RelLetter.listVal (v.take i))
        (GGT.RelLetter.listVal (v.take j)) : ℕ) : ℝ) := by positivity
  norm_num
  linarith

/-- **Producer-facing exact design with a uniform count and side exclusion.**

The depth threshold is enlarged by the explicit every-edge isolation radius
and the cyclic window is the whole fixed target plus its base letter.  Both are
chosen before `exists_exactRelatorDesign₂` selects `ms`.  The resulting count
parameter is the absolute constant `1`, and therefore fits the same window as
soon as the target has at least two block letters. -/
theorem exists_exactRelatorDesign₂_with_count_one
    (E : HypEmbeddedCore₂ A N) (baseLetter : G)
    (hbase : baseLetter ∈ E.rel.base) {delta : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier delta)
    (requestedRho eps diffRadius target : ℕ)
    (htarget : 2 ≤ target) (hevenTarget : Even target) :
    ∃ ms : List ℕ,
      ExactRelatorDesign₂ E baseLetter
        (max requestedRho (GGT.OsinComponents.everyEdgeIsolationRadius delta
          (2 * (target + 1)))) eps diffRadius (target + 1) target ms ∧
      RelatorBlockCountAt₂ E [baseLetter] ms 1 ∧
      RelatorSideExclusionAt₂ E [baseLetter] ms := by
  let deepRadius := max requestedRho
    (GGT.OsinComponents.everyEdgeIsolationRadius delta (2 * (target + 1)))
  obtain ⟨ms, hdesign⟩ := exists_exactRelatorDesign₂ E deepRadius eps diffRadius
    baseLetter (target + 1) target
  have heven : Even ms.length := by rw [hdesign.1]; exact hevenTarget
  have hcount : RelatorBlockCountAt₂ E [baseLetter] ms 1 :=
    hdesign.blockCountAt_one E hbase hdelta heven (le_refl _)
      (Nat.le_max_right _ _)
  have hwindow : 1 + blockConst [baseLetter] 1 ≤ target + 1 := by
    simp only [blockConst, List.length_singleton]
    omega
  exact ⟨ms, hdesign, hcount,
    hdesign.sideExclusionAt E heven hcount hwindow⟩

end ExactCount

end HullSC
end GroupApproximation
