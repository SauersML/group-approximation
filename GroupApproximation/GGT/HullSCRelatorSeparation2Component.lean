import GroupApproximation.GGT.HullSCRelatorSeparation2Word

/-!
# Every block letter of the alternating relator is its own component

Osin, Definition 4.1: a component is a maximal run of letters of one index.
`HullSC.blockWord_index_alternates` says consecutive block letters of
`HullSC.relatorWord₂` carry opposite indices, and the base part carries none, so
each block letter is a maximal run by itself:

  `IsComp b (relatorWord₂ p h₀ h₁ ms) (|p| + i) (|p| + i + 1)`.

That is the granularity `GGT/HullSCRelatorSeparationComponent.lean` shows the
`Λ = Unit` model destroys, and restoring it is the whole point of the
alternation.  With it the per-letter matching of
`HullSC.exponent_eq_of_blockMatch` is reachable again, and the run no longer
spans a single edge, so the obstruction of
`HullSC.not_quasiGeodesic_relatorWord` is gone.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- Reading a list at an index, from the `Option` form. -/
theorem getElem_eq_of_getElem? {α : Type v} {w : List α} {j : ℕ}
    (hj : j < w.length) {y : α} (h : w[j]? = some y) : w[j]'hj = y := by
  have h1 := List.getElem?_eq_getElem hj
  rw [h] at h1
  exact (Option.some.inj h1).symm

section Comp

variable {G : Type u} [Group G]

omit [Group G] in
/-- A letter read as `comp b x` carries the index `b`. -/
theorem isCompOf_of_getElem? {w : List (GGT.RelLetter G Bool)} {j : ℕ}
    (hj : j < w.length) {b : Bool} {x : G}
    (h : w[j]? = some (GGT.RelLetter.comp b x)) :
    (w[j]'hj).IsCompOf b :=
  Eq.subst (motive := fun y => GGT.RelLetter.IsCompOf b y)
    (getElem_eq_of_getElem? hj h).symm (isCompOf_comp b x)

omit [Group G] in
/-- A letter read as `comp b' x` with `b' ≠ b` does not carry the index `b`. -/
theorem not_isCompOf_of_getElem? {w : List (GGT.RelLetter G Bool)} {j : ℕ}
    (hj : j < w.length) {b b' : Bool} {x : G}
    (h : w[j]? = some (GGT.RelLetter.comp b' x)) (hne : b' ≠ b) :
    ¬ (w[j]'hj).IsCompOf b :=
  Eq.subst (motive := fun y => ¬ GGT.RelLetter.IsCompOf b y)
    (getElem_eq_of_getElem? hj h).symm hne

/-- Every position of the run carries a component letter. -/
theorem blockWord_getElem?_comp (h₀ h₁ : G) (s : Bool) (ms : List ℕ) {i : ℕ}
    (hi : i < ms.length) :
    ∃ (b : Bool) (x : G),
      (blockWord h₀ h₁ s ms)[i]? = some (GGT.RelLetter.comp b x) := by
  have hlen : i < (blockWord h₀ h₁ s ms).length := by
    rw [length_blockWord]
    exact hi
  have h1 := List.getElem?_eq_getElem hlen
  obtain ⟨b, m, -, hx⟩ := mem_blockWord h₀ h₁ s ms _ (List.mem_of_getElem? h1)
  refine ⟨b, (if b then h₁ else h₀) ^ m, ?_⟩
  rw [h1, hx]

/-- The relator reads its run after its base part. -/
theorem relatorWord₂_getElem?_block (p : List G) (h₀ h₁ : G) (ms : List ℕ)
    (i : ℕ) :
    (relatorWord₂ p h₀ h₁ ms)[p.length + i]?
      = (blockWord h₀ h₁ false ms)[i]? := by
  have hsub : p.length + i - p.length = i := by omega
  show (p.map GGT.RelLetter.base ++ blockWord h₀ h₁ false ms)[p.length + i]?
    = (blockWord h₀ h₁ false ms)[i]?
  rw [List.getElem?_append_right (by rw [List.length_map]; omega),
    List.length_map, hsub]

/-- A letter of the relator below `|p|` carries no index. -/
theorem not_isCompOf_getElem_relatorWord₂ {p : List G} {h₀ h₁ : G}
    {ms : List ℕ} {j : ℕ} (hj : j < p.length)
    (hjv : j < (relatorWord₂ p h₀ h₁ ms).length) (lam : Bool) :
    ¬ ((relatorWord₂ p h₀ h₁ ms)[j]'hjv).IsCompOf lam := by
  have h1 : (relatorWord₂ p h₀ h₁ ms)[j]? = (p.map GGT.RelLetter.base)[j]? := by
    show (p.map GGT.RelLetter.base ++ blockWord h₀ h₁ false ms)[j]? = _
    exact List.getElem?_append_left (by rwa [List.length_map])
  have h2 : (relatorWord₂ p h₀ h₁ ms)[j]'hjv ∈ p.map GGT.RelLetter.base := by
    refine List.mem_of_getElem? (i := j) ?_
    rw [← h1]
    exact List.getElem?_eq_getElem hjv
  obtain ⟨g, -, hg⟩ := List.mem_map.mp h2
  exact hg ▸ not_isCompOf_base lam g

/-- **Each block letter of the alternating relator is a component by itself.**

The letter at `|p| + i` carries an index its two neighbours do not: the one
before is either a base letter or the block letter at `|p| + i - 1`, whose index
is the opposite one, and the one after is the block letter at `|p| + i + 1`,
likewise.  So the maximal run containing it is `[|p| + i, |p| + i + 1)`. -/
theorem isComp_relatorWord₂ (p : List G) (h₀ h₁ : G) (ms : List ℕ) {i₀ : ℕ}
    (hi₀ : i₀ < ms.length) {b : Bool} {x : G}
    (hb : (blockWord h₀ h₁ false ms)[i₀]? = some (GGT.RelLetter.comp b x)) :
    GGT.OsinComponents.IsComp b (relatorWord₂ p h₀ h₁ ms)
      (p.length + i₀) (p.length + i₀ + 1) := by
  have hlen : (relatorWord₂ p h₀ h₁ ms).length = p.length + ms.length :=
    length_relatorWord₂ p h₀ h₁ ms
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j _ _ hjv
    have hje : j = p.length + i₀ := by omega
    subst hje
    have hget : (relatorWord₂ p h₀ h₁ ms)[p.length + i₀]?
        = some (GGT.RelLetter.comp b x) := by
      rw [relatorWord₂_getElem?_block]
      exact hb
    exact isCompOf_of_getElem? hjv hget
  · intro j hje hjv
    rcases Nat.eq_zero_or_pos i₀ with hz | hpos
    · exact not_isCompOf_getElem_relatorWord₂ (by omega) hjv b
    · obtain ⟨i₁, hi₁⟩ : ∃ i₁, i₀ = i₁ + 1 := ⟨i₀ - 1, by omega⟩
      subst hi₁
      have hjeq : j = p.length + i₁ := by omega
      subst hjeq
      obtain ⟨b', x', hb'⟩ :=
        blockWord_getElem?_comp h₀ h₁ false ms (show i₁ < ms.length by omega)
      have halt :=
        blockWord_index_alternates h₀ h₁ false ms i₁ b' b x' x hb' hb
      have hget : (relatorWord₂ p h₀ h₁ ms)[p.length + i₁]?
          = some (GGT.RelLetter.comp b' x') := by
        rw [relatorWord₂_getElem?_block]
        exact hb'
      have hne : b' ≠ b := by
        rw [halt]
        cases b' <;> simp
      exact not_isCompOf_of_getElem? hjv hget hne
  · intro hk
    obtain ⟨b'', x'', hb''⟩ :=
      blockWord_getElem?_comp h₀ h₁ false ms (show i₀ + 1 < ms.length by omega)
    have halt := blockWord_index_alternates h₀ h₁ false ms i₀ b b'' x x'' hb hb''
    have hget : (relatorWord₂ p h₀ h₁ ms)[p.length + i₀ + 1]?
        = some (GGT.RelLetter.comp b'' x'') := by
      rw [show p.length + i₀ + 1 = p.length + (i₀ + 1) by omega,
        relatorWord₂_getElem?_block]
      exact hb''
    have hne : b'' ≠ b := by
      rw [halt]
      cases b <;> simp
    exact not_isCompOf_of_getElem? hk hget hne

end Comp

end HullSC
end GroupApproximation
