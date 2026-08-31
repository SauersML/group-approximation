import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyExact
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyGap
import GroupApproximation.GGT.HullSCRelatorSeparation2CyclicSegment
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex

/-!
# The bounded-window parser for exact-design side spans

After repairing the side-exclusion API so both anchors denote actual
components, the first geometric step is unconditional.  If a prefix of a
symmetrized relator has two vertices whose quotient lies in one peripheral
subgroup, their relative distance is at most one.  The relator block-count
estimate therefore puts their indices at distance at most
`1 + blockConst p cnt`, exactly the window used by `ExactRelatorDesign₂`.

This module proves the estimate in both orientations and packages the result as
a disjunction.  The remaining parser is purely cyclic-word bookkeeping: turn
the bounded span into either a pure-run window or a window crossing the unique
base letter, then apply the corresponding exact-design avoidance clause.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Parser

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- A component start whose declared coordinate lies on the first long side
really is a component letter of that side.  Positivity of the following
base-spelled side excludes the endpoint coordinate; this is why the active
side-exclusion API carries the two nonempty short-side certificates. -/
theorem exists_comp_letter_of_firstLongSide_start
    {py pz u u' : List (GGT.RelLetter G Bool)} {s : Bool} {i : ℕ}
    (hpz : ∀ x ∈ pz, ∃ g : G, x = GGT.RelLetter.base g)
    (hpz0 : 0 < pz.length) (hi : i ≤ u.length)
    (hstart : GGT.OsinComponents.IsCompStart s
      (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') (py.length + i)) :
    ∃ (_hil : i < u.length) (x : G),
      u[i]? = some (GGT.RelLetter.comp s x) := by
  have hil : i < u.length := by
    by_contra hnot
    have hieq : i = u.length := by omega
    apply GGT.OsinComponents.not_isCompStart_fourGon_r py u pz u' s hpz
      (o := py.length + i) (by omega) (by omega)
    exact hstart
  obtain ⟨hglobal, hcomp⟩ :=
    GGT.OsinComponents.isCompOf_getElem_of_isCompStart hstart
  have hread := GGT.OsinComponents.getElem_fourGon_q py u pz u' hil rfl hglobal
  rw [hread] at hcomp
  obtain ⟨x, hx⟩ := getElem?_comp_of_isCompOf hil hcomp
  exact ⟨hil, x, hx⟩

/-- A component start in the oppositely traversed fourth side has a positive
endpoint coordinate in `u'`, and the preceding letter of `u'` is a component
letter of the same index. -/
theorem exists_comp_letter_of_secondLongSide_start
    {py pz u u' : List (GGT.RelLetter G Bool)} {s : Bool} {m : ℕ}
    (hm : m ≤ u'.length)
    (hstart : GGT.OsinComponents.IsCompStart s
      (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
      (py.length + u.length + pz.length + (u'.length - m))) :
    ∃ (_hm0 : 0 < m) (x : G),
      u'[m - 1]? = some (GGT.RelLetter.comp s x) := by
  have hm0 : 0 < m := by
    by_contra hnot
    have hmz : m = 0 := by omega
    subst hmz
    obtain ⟨k, hk⟩ := hstart
    have hstartlt : py.length + u.length + pz.length + (u'.length - 0) <
        (py ++ u ++ pz ++ GGT.OsinComponents.revWord u').length :=
      lt_of_lt_of_le hk.1 hk.2.1
    have hlen : (py ++ u ++ pz ++ GGT.OsinComponents.revWord u').length =
        py.length + u.length + pz.length + u'.length := by
      rw [GGT.OsinComponents.length_fourGon]
    rw [hlen] at hstartlt
    omega
  obtain ⟨x, hx⟩ := GGT.OsinComponents.exists_comp_of_isCompStart_rev
    py u pz u' s hm0 hm hstart
  exact ⟨hm0, x, hx⟩

/-- A forward peripheral span in a prefix of a symmetrized relator has bounded
index length. -/
theorem forward_index_gap_le_of_blockCount
    (E : HypEmbeddedCore₂ A N) (cnt : ℕ)
    (hcount : RelatorBlockCountInputOne₂ E cnt)
    {p : List G} (hp : p.length = 1) {ms : List ℕ}
    {v u tl : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v)
    (hu : v = u ++ tl) {d i : ℕ} (hdi : d ≤ i) (hi : i ≤ u.length)
    {s : Bool}
    (hmem : (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u i ∈ E.rel.fam s) :
    i - d ≤ 1 + blockConst p cnt := by
  have hiv : i ≤ v.length := by rw [hu, List.length_append]; omega
  have hdv : d ≤ v.length := le_trans hdi hiv
  have hq := hcount p hp ms v hv d i hdi hiv
  have hdu : d ≤ u.length := le_trans hdi hi
  have hvd : GGT.OsinComponents.vertex (1 : G) v d =
      GGT.OsinComponents.vertex (1 : G) u d := by
    rw [hu]
    exact GGT.OsinComponents.vertex_append_of_le u tl 1 d hdu
  have hvi : GGT.OsinComponents.vertex (1 : G) v i =
      GGT.OsinComponents.vertex (1 : G) u i := by
    rw [hu]
    exact GGT.OsinComponents.vertex_append_of_le u tl 1 i hi
  have hdist : WordMetric.wordDist E.rel.alphabet.carrier
      (GGT.OsinComponents.vertex (1 : G) v d)
      (GGT.OsinComponents.vertex (1 : G) v i) ≤ 1 := by
    rw [hvd, hvi]
    exact GGT.OsinComponents.wordDist_le_one_of_mem_fam E.rel hmem
  omega

/-- The same estimate when the anchor order is reversed. -/
theorem reverse_index_gap_le_of_blockCount
    (E : HypEmbeddedCore₂ A N) (cnt : ℕ)
    (hcount : RelatorBlockCountInputOne₂ E cnt)
    {p : List G} (hp : p.length = 1) {ms : List ℕ}
    {v u tl : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v)
    (hu : v = u ++ tl) {d i : ℕ} (hid : i ≤ d) (hd : d ≤ u.length)
    {s : Bool}
    (hmem : (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u i ∈ E.rel.fam s) :
    d - i ≤ 1 + blockConst p cnt := by
  have hdv : d ≤ v.length := by rw [hu, List.length_append]; omega
  have hiv : i ≤ v.length := le_trans hid hdv
  have hq := hcount p hp ms v hv i d hid hdv
  have hi : i ≤ u.length := le_trans hid hd
  have hvi : GGT.OsinComponents.vertex (1 : G) v i =
      GGT.OsinComponents.vertex (1 : G) u i := by
    rw [hu]
    exact GGT.OsinComponents.vertex_append_of_le u tl 1 i hi
  have hvd : GGT.OsinComponents.vertex (1 : G) v d =
      GGT.OsinComponents.vertex (1 : G) u d := by
    rw [hu]
    exact GGT.OsinComponents.vertex_append_of_le u tl 1 d hd
  have hdist : WordMetric.wordDist E.rel.alphabet.carrier
      (GGT.OsinComponents.vertex (1 : G) v i)
      (GGT.OsinComponents.vertex (1 : G) v d) ≤ 1 := by
    rw [WordMetric.wordDist_comm E.rel.alphabet.symmetricGenerating, hvd, hvi]
    exact GGT.OsinComponents.wordDist_le_one_of_mem_fam E.rel hmem
  omega

/-- Every peripheral span between two indices of such a prefix lies in one of
the two oriented windows of radius `1 + blockConst p cnt`. -/
theorem index_window_of_blockCount
    (E : HypEmbeddedCore₂ A N) (cnt : ℕ)
    (hcount : RelatorBlockCountInputOne₂ E cnt)
    {p : List G} (hp : p.length = 1) {ms : List ℕ}
    {v u tl : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym (relatorWord₂ p (E.lox false) (E.lox true) ms) v)
    (hu : v = u ++ tl) {d i : ℕ} (hd : d ≤ u.length) (hi : i ≤ u.length)
    {s : Bool}
    (hmem : (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) u i ∈ E.rel.fam s) :
    (d ≤ i ∧ i - d ≤ 1 + blockConst p cnt) ∨
      (i ≤ d ∧ d - i ≤ 1 + blockConst p cnt) := by
  rcases le_total d i with hdi | hid
  · exact Or.inl ⟨hdi,
      forward_index_gap_le_of_blockCount E cnt hcount hp hv hu hdi hi hmem⟩
  · exact Or.inr ⟨hid,
      reverse_index_gap_le_of_blockCount E cnt hcount hp hv hu hid hd hmem⟩

/-- A forward span in a prefix of a symmetrized relator is a prefix of a
rotation based at the first endpoint, either in the relator or in its formal
inverse.  This is the cyclic normalization consumed by the exact-design seam
parser. -/
theorem forward_span_prefix_sym_cases
    (E : HypEmbeddedCore₂ A N) {p : List G} {ms : List ℕ}
    {v u tl : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ p (E.lox false) (E.lox true) ms) v)
    (hu : v = u ++ tl) {d i : ℕ} (hdi : d ≤ i) (hi : i ≤ u.length) :
    (∃ c : ℕ,
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) u i =
        GGT.RelLetter.listVal
          ((relatorWord₂ p (E.lox false) (E.lox true) ms).rotate c |>.take
            (i - d))) ∨
      (∃ c : ℕ,
        (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) u i =
          GGT.RelLetter.listVal
            ((RelWord.revInv
              (relatorWord₂ p (E.lox false) (E.lox true) ms)).rotate c |>.take
                (i - d))) := by
  have hd : d ≤ u.length := le_trans hdi hi
  have hvd : GGT.OsinComponents.vertex (1 : G) v d =
      GGT.OsinComponents.vertex (1 : G) u d := by
    rw [hu]
    exact GGT.OsinComponents.vertex_append_of_le u tl 1 d hd
  have hvi : GGT.OsinComponents.vertex (1 : G) v i =
      GGT.OsinComponents.vertex (1 : G) u i := by
    rw [hu]
    exact GGT.OsinComponents.vertex_append_of_le u tl 1 i hi
  have hiv : i ≤ v.length := by rw [hu, List.length_append]; omega
  have hiR : i ≤
      (relatorWord₂ p (E.lox false) (E.lox true) ms).length := by
    rw [← hv.length_eq]
    exact hiv
  rcases hv.exists_rotate with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨c + d, ?_⟩
    rw [← hvd, ← hvi, hc]
    exact span_rotate_eq_listVal_take_rotate _ hdi hiR
  · refine Or.inr ⟨c + d, ?_⟩
    rw [← hvd, ← hvi, hc]
    apply span_rotate_eq_listVal_take_rotate _ hdi
    simpa only [RelWord.length_revInv] using hiR

/-- In the reverse endpoint order, the side span is the inverse of the same
normalized cyclic prefix based at the smaller endpoint. -/
theorem reverse_span_prefix_sym_cases
    (E : HypEmbeddedCore₂ A N) {p : List G} {ms : List ℕ}
    {v u tl : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ p (E.lox false) (E.lox true) ms) v)
    (hu : v = u ++ tl) {d i : ℕ} (hid : i ≤ d) (hd : d ≤ u.length) :
    (∃ c : ℕ,
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) u i =
        (GGT.RelLetter.listVal
          ((relatorWord₂ p (E.lox false) (E.lox true) ms).rotate c |>.take
            (d - i)))⁻¹) ∨
      (∃ c : ℕ,
        (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) u i =
          (GGT.RelLetter.listVal
            ((RelWord.revInv
              (relatorWord₂ p (E.lox false) (E.lox true) ms)).rotate c |>.take
                (d - i)))⁻¹) := by
  rcases forward_span_prefix_sym_cases E hv hu hid hd with
    ⟨c, hc⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨c, ?_⟩
    calc
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) u i =
          ((GGT.OsinComponents.vertex (1 : G) u i)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) u d)⁻¹ := by group
      _ = _ := congrArg Inv.inv hc
  · refine Or.inr ⟨c, ?_⟩
    calc
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) u i =
          ((GGT.OsinComponents.vertex (1 : G) u i)⁻¹ *
            GGT.OsinComponents.vertex (1 : G) u d)⁻¹ := by group
      _ = _ := congrArg Inv.inv hc

end Parser

end HullSC
end GroupApproximation
