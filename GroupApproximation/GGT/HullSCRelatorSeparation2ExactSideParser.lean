import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyExact
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyGap
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

end Parser

end HullSC
end GroupApproximation
