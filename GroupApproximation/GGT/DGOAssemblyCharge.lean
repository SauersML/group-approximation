import GroupApproximation.GGT.DGOAssemblyIsolation
import GroupApproximation.GGT.DGOGeodesicChainComponents
import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic

/-!
# Charging a broken component to the three that replace it

The accounting step of the assembly.  A distinguished component the break
consumes --- one connected to a component of the chord --- is not an isolated
component of any piece, so nothing bounds its `ℓ̂` directly.  What bounds it is
the quadrilateral it sits in: writing `p` for the consumed component, `y` for the
chord component it is connected to, and `f`, `e` for the two edges joining their
endpoints,

    p₋ → p₊     is     p₋ → y₋ → y₊ → p₊
                        f      y      e⁻¹

so `ℓ̂(p) ≤ ℓ̂(f) + ℓ̂(y) + ℓ̂(e)`, which is Dahmani--Guirardel--Osin's implicit
step in the displayed inequality of Proposition 4.14's proof.  Their `y_j`, `e_j`
and `f_j` are all isolated components of the cycle `c_j`, so the right-hand side
is bounded by that cycle's own sum bound and the charge closes.

## Why this is stated at group elements and not at words

Nothing here is about components, indices or words: the quadrilateral is an
identity in `G`, and the three hypotheses are ball memberships.  Stating it that
way means the assembly can supply the three from wherever it likes --- in
practice from `SumBound` applied to `c_j`, whose conclusion is exactly ball
membership at a radius --- without this lemma knowing anything about how the
cycles were built.

It is also why the `∃ r` form of `SumBound` pays off here rather than merely
avoiding a trap: the charge is an *addition of radii*, and a witness function
adds where an infimum would have to be re-minimised.
-/

namespace GroupApproximation
namespace GGT
namespace DGOPolygonCut

open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The auxiliary cycles -/

/-- **The word of one DGO auxiliary cycle `c_j`.**

For an interior cycle, `left` is `e_{j-1}`, `arc` is the polygon segment from
`p_{i_{j-1}}` to `p_{i_j}`, `right` is `f_j`, and `chord` is the intervening
segment of the cutting chord, read back toward `y_{j-1}`.  The first and last
cycles use an empty `left` or `right`.  Lists, rather than mandatory singleton
letters, record those endpoint degeneracies without inserting identity edges.
-/
def auxiliaryCycleWord (left arc right chord : List (RelLetter G Λ)) :
    List (RelLetter G Λ) :=
  ((revWord left ++ arc) ++ right) ++ chord

/-- The canonical side cut of `auxiliaryCycleWord`: every connector and chord
letter is a side, while the polygon arc retains its inherited side cut. -/
def auxiliaryCycleCut (left : List (RelLetter G Λ)) (nArc : ℕ)
    (arcCut : ℕ → ℕ) (right : List (RelLetter G Λ)) : ℕ → ℕ :=
  appendCut
    (appendCut
      (appendCut (fun s => s) left.length arcCut)
      (left.length + nArc) (fun s => s))
    (left.length + nArc + right.length) (fun s => s)

/-- **The endpoint equation closes `c_j`.**  This is the word-level form of
the four paths having consecutive endpoints in DGO's construction. -/
theorem listVal_auxiliaryCycleWord_eq_one
    (left arc right chord : List (RelLetter G Λ))
    (hclose : RelLetter.listVal left = RelLetter.listVal arc *
      RelLetter.listVal right * RelLetter.listVal chord) :
    RelLetter.listVal (auxiliaryCycleWord left arc right chord) = 1 := by
  simp only [auxiliaryCycleWord, listVal_append, listVal_revWord, hclose]
  group

/-- **The interior auxiliary cycle between two successive ordered partners
closes.**

Here `p₀,p₁` are the terminal/start vertices of the two omitted broken polygon
components and `y₀,y₁` are the matching terminal/start vertices on the chord.
The connector `e` runs from `p₀` to `y₀`, while `f` runs from `p₁` to `y₁`.
Thus the concrete DGO cycle is

`e⁻¹ · half[p₀,p₁] · f · half[y₀,y₁]⁻¹`.

This fixes the endpoint convention needed by the ordered separation argument;
in particular the partner components at the two ends are omitted rather than
accidentally placed next to their own connectors. -/
theorem listVal_auxiliaryCycle_segments_eq_one (v : G)
    (half e f : List (RelLetter G Λ)) {p₀ p₁ y₀ y₁ : ℕ}
    (hp : p₀ ≤ p₁) (hy : y₀ ≤ y₁)
    (he : RelLetter.listVal e = (vertex v half p₀)⁻¹ * vertex v half y₀)
    (hf : RelLetter.listVal f = (vertex v half p₁)⁻¹ * vertex v half y₁) :
    RelLetter.listVal (auxiliaryCycleWord e
      ((half.drop p₀).take (p₁ - p₀)) f
      (revWord ((half.drop y₀).take (y₁ - y₀)))) = 1 := by
  have hpseg := listVal_segment half v hp
  have hyseg := listVal_segment half v hy
  have hpval : RelLetter.listVal ((half.drop p₀).take (p₁ - p₀)) =
      (vertex v half p₀)⁻¹ * vertex v half p₁ := by
    calc
      RelLetter.listVal ((half.drop p₀).take (p₁ - p₀))
          = (vertex v half p₀)⁻¹ *
              (vertex v half p₀ *
                RelLetter.listVal ((half.drop p₀).take (p₁ - p₀))) := by
              rw [inv_mul_cancel_left]
      _ = (vertex v half p₀)⁻¹ * vertex v half p₁ := by rw [hpseg]
  have hyval : RelLetter.listVal ((half.drop y₀).take (y₁ - y₀)) =
      (vertex v half y₀)⁻¹ * vertex v half y₁ := by
    calc
      RelLetter.listVal ((half.drop y₀).take (y₁ - y₀))
          = (vertex v half y₀)⁻¹ *
              (vertex v half y₀ *
                RelLetter.listVal ((half.drop y₀).take (y₁ - y₀))) := by
              rw [inv_mul_cancel_left]
      _ = (vertex v half y₀)⁻¹ * vertex v half y₁ := by rw [hyseg]
  apply listVal_auxiliaryCycleWord_eq_one
  rw [he, hpval, hf, listVal_revWord, hyval]
  group

/-- **The auxiliary cycle has exactly the printed four families of sides.** -/
theorem isPolygonCut_auxiliaryCycleWord (left arc right chord :
    List (RelLetter G Λ)) {nArc : ℕ} {arcCut : ℕ → ℕ}
    (harc : IsPolygonCut nArc arc arcCut) :
    IsPolygonCut (left.length + nArc + right.length + chord.length)
      (auxiliaryCycleWord left arc right chord)
      (auxiliaryCycleCut left nArc arcCut right) := by
  have hleft : IsPolygonCut left.length (revWord left) (fun s => s) := by
    have h := isPolygonCut_id (revWord left)
    rwa [length_revWord] at h
  have hright : IsPolygonCut right.length right (fun s => s) :=
    isPolygonCut_id right
  have hchord : IsPolygonCut chord.length chord (fun s => s) :=
    isPolygonCut_id chord
  have hla := isPolygonCut_append hleft harc
  have hlar := isPolygonCut_append hla hright
  have hall := isPolygonCut_append hlar hchord
  simpa [auxiliaryCycleWord, auxiliaryCycleCut, Nat.add_assoc] using hall

/-! ## The connector/arc cut dictionary -/

omit [Group G] in
/-- `appendCut` agrees with its first cut up to the joining side. -/
theorem appendCut_apply_of_le (c₁ c₂ : ℕ → ℕ) (n s : ℕ) (hs : s ≤ n) :
    appendCut c₁ n c₂ s = c₁ s := by
  simp [appendCut, hs]

omit [Group G] in
/-- `appendCut` agrees with the shifted second cut, including at offset zero
when that cut starts at zero. -/
theorem appendCut_apply_add (c₁ c₂ : ℕ → ℕ) (n r : ℕ)
    (hc₂0 : c₂ 0 = 0) :
    appendCut c₁ n c₂ (n + r) = c₁ n + c₂ r := by
  by_cases hr : r = 0
  · subst r
    simp [appendCut, hc₂0]
  · have hnot : ¬ n + r ≤ n := by omega
    simp [appendCut, hnot]

omit [Group G] in
/-- On the reversed left connector, the auxiliary cut is the identity cut. -/
theorem auxiliaryCycleCut_left (left right : List (RelLetter G Λ))
    (nArc : ℕ) (arcCut : ℕ → ℕ) {r : ℕ} (hr : r ≤ left.length) :
    auxiliaryCycleCut left nArc arcCut right r = r := by
  have hmiddle : r ≤ left.length + nArc := by omega
  have houter : r ≤ left.length + nArc + right.length := by omega
  rw [auxiliaryCycleCut,
    appendCut_apply_of_le _ _ _ _ houter,
    appendCut_apply_of_le _ _ _ _ hmiddle,
    appendCut_apply_of_le _ _ _ _ hr]

omit [Group G] in
/-- On the inherited arc, the auxiliary cut is the arc cut shifted past the
left connector. -/
theorem auxiliaryCycleCut_arc (left right : List (RelLetter G Λ))
    {arc : List (RelLetter G Λ)} {nArc r : ℕ} {arcCut : ℕ → ℕ}
    (harc : IsPolygonCut nArc arc arcCut) (hr : r ≤ nArc) :
    auxiliaryCycleCut left nArc arcCut right (left.length + r) =
      left.length + arcCut r := by
  have hmiddle : left.length + r ≤ left.length + nArc := by omega
  have houter : left.length + r ≤
      left.length + nArc + right.length := by omega
  rw [auxiliaryCycleCut,
    appendCut_apply_of_le _ _ _ _ houter,
    appendCut_apply_of_le _ _ _ _ hmiddle,
    appendCut_apply_add _ _ _ _ harc.start]

omit [Group G] in
/-- On the right connector, the auxiliary cut has passed the whole arc. -/
theorem auxiliaryCycleCut_right (left right : List (RelLetter G Λ))
    {arc : List (RelLetter G Λ)} {nArc r : ℕ} {arcCut : ℕ → ℕ}
    (harc : IsPolygonCut nArc arc arcCut) (hr : r ≤ right.length) :
    auxiliaryCycleCut left nArc arcCut right (left.length + nArc + r) =
      left.length + arc.length + r := by
  have houter : left.length + nArc + r ≤
      left.length + nArc + right.length := by omega
  rw [auxiliaryCycleCut,
    appendCut_apply_of_le _ _ _ _ houter,
    appendCut_apply_add _ _ _ _ rfl,
    appendCut_apply_add _ _ _ _ harc.start,
    harc.finish]

omit [Group G] in
/-- On the final chord, the auxiliary cut has passed both connectors and the
inherited arc. -/
theorem auxiliaryCycleCut_chord (left right : List (RelLetter G Λ))
    {arc : List (RelLetter G Λ)} {nArc r : ℕ} {arcCut : ℕ → ℕ}
    (harc : IsPolygonCut nArc arc arcCut) :
    auxiliaryCycleCut left nArc arcCut right
        (left.length + nArc + right.length + r) =
      left.length + arc.length + right.length + r := by
  rw [auxiliaryCycleCut,
    appendCut_apply_add _ _ _ _ rfl,
    appendCut_apply_add _ _ _ _ rfl,
    appendCut_apply_add _ _ _ _ harc.start,
    harc.finish]

/-! ## The canonical connector target -/

/-- The distinguished-side indices forced solely by the two connectors.

Every connector letter must be distinguished because no quasi-geodesic
estimate is available for an arbitrary peripheral connector.  Endpoint
degeneracies are represented by empty lists and therefore contribute no
indices.  This is the canonical target used by every connector-indexed child
certificate below; keeping it canonical also makes the child-family assembly
independent of any later choice of labels. -/
def auxiliaryCycleConnectorTarget (left right : List (RelLetter G Λ))
    (nArc : ℕ) : Finset ℕ :=
  Finset.range left.length ∪
    (Finset.range right.length).image (fun r => left.length + nArc + r)

omit [Group G] in
theorem mem_auxiliaryCycleConnectorTarget_left
    (left right : List (RelLetter G Λ)) (nArc r : ℕ)
    (hr : r < left.length) :
    r ∈ auxiliaryCycleConnectorTarget left right nArc := by
  simp [auxiliaryCycleConnectorTarget, hr]

omit [Group G] in
theorem mem_auxiliaryCycleConnectorTarget_right
    (left right : List (RelLetter G Λ)) (nArc r : ℕ)
    (hr : r < right.length) :
    left.length + nArc + r ∈
      auxiliaryCycleConnectorTarget left right nArc := by
  simp [auxiliaryCycleConnectorTarget, hr]

omit [Group G] in
/-- Every canonical connector target is a side of the auxiliary cycle. -/
theorem auxiliaryCycleConnectorTarget_lt
    (left right chord : List (RelLetter G Λ)) (nArc : ℕ) :
    ∀ s ∈ auxiliaryCycleConnectorTarget left right nArc,
      s < left.length + nArc + right.length + chord.length := by
  intro s hs
  rw [auxiliaryCycleConnectorTarget, Finset.mem_union] at hs
  rcases hs with hs | hs
  · have := Finset.mem_range.mp hs
    omega
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    have := Finset.mem_range.mp hr
    omega

omit [Group G] in
/-- The auxiliary cut advances by one on every canonical connector target. -/
theorem auxiliaryCycleConnectorTarget_edge
    (left arc right : List (RelLetter G Λ)) {nArc : ℕ}
    {arcCut : ℕ → ℕ} (harc : IsPolygonCut nArc arc arcCut) :
    ∀ s ∈ auxiliaryCycleConnectorTarget left right nArc,
      auxiliaryCycleCut left nArc arcCut right (s + 1) =
        auxiliaryCycleCut left nArc arcCut right s + 1 := by
  intro s hs
  rw [auxiliaryCycleConnectorTarget, Finset.mem_union] at hs
  rcases hs with hs | hs
  · have hslt := Finset.mem_range.mp hs
    rw [auxiliaryCycleCut_left left right nArc arcCut (by omega),
      auxiliaryCycleCut_left left right nArc arcCut (by omega)]
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    have hrlt := Finset.mem_range.mp hr
    have hs1 : left.length + nArc + r + 1 =
        left.length + nArc + (r + 1) := by omega
    rw [hs1,
      auxiliaryCycleCut_right left right harc (by omega),
      auxiliaryCycleCut_right left right harc (by omega)]
    omega

/-- Vertices on the inherited arc are vertices of `arc`, read after the
reversed left connector. -/
theorem vertex_auxiliaryCycle_arc (v : G) (left arc right chord :
    List (RelLetter G Λ)) {r : ℕ} (hr : r ≤ arc.length) :
    vertex v (auxiliaryCycleWord left arc right chord) (left.length + r) =
      vertex (v * RelLetter.listVal (revWord left)) arc r := by
  have hrev : (revWord left).length = left.length := length_revWord left
  have h₁ : left.length + r ≤ (revWord left ++ arc).length := by
    simp [hrev]
    omega
  have h₂ : left.length + r ≤ ((revWord left ++ arc) ++ right).length := by
    simp only [List.length_append]
    omega
  rw [auxiliaryCycleWord,
    vertex_append_of_le (((revWord left ++ arc) ++ right)) chord v _ h₂,
    vertex_append_of_le (revWord left ++ arc) right v _ h₁]
  rw [← hrev, vertex_append_add]

/-- Vertices on the final chord are vertices of `chord`, read after the three
preceding paths. -/
theorem vertex_auxiliaryCycle_chord (v : G) (left arc right chord :
    List (RelLetter G Λ)) (r : ℕ) :
    vertex v (auxiliaryCycleWord left arc right chord)
        (left.length + arc.length + right.length + r) =
      vertex (v * RelLetter.listVal ((revWord left ++ arc) ++ right)) chord r := by
  have hpref : ((revWord left ++ arc) ++ right).length =
      left.length + arc.length + right.length := by
    simp [length_revWord, Nat.add_assoc]
  rw [auxiliaryCycleWord, ← hpref, vertex_append_add]

/-- **Off-target quasigeodesicity of one auxiliary cycle.**

The inherited arc uses its own named cut after the vertex-offset dictionary
above.  The final chord is a subpath of a geodesic word.  Every left and right
connector side is explicitly required to be distinguished, so no unjustified
quasigeodesic assertion is made about a possibly trivial connector letter. -/
theorem quasi_auxiliaryCycleWord (D : RelGenSet G Λ) {b : ℝ} (hb : 0 ≤ b)
    (v : G) (left arc right chord : List (RelLetter G Λ)) {nArc : ℕ}
    {arcCut : ℕ → ℕ}
    (harc : IsCutPolygon D b nArc
      (v * RelLetter.listVal (revWord left)) arc arcCut)
    {g : G} (hchord : IsGeodesicWord D
      (v * RelLetter.listVal ((revWord left ++ arc) ++ right)) g chord)
    (Target : Finset ℕ)
    (hleft : ∀ r : ℕ, r < left.length → r ∈ Target)
    (hright : ∀ r : ℕ, r < right.length →
      left.length + nArc + r ∈ Target) :
    ∀ s : ℕ, s < left.length + nArc + right.length + chord.length →
      s ∉ Target → ∀ p q : ℕ,
      auxiliaryCycleCut left nArc arcCut right s ≤ p →
      p ≤ q →
      q ≤ auxiliaryCycleCut left nArc arcCut right (s + 1) →
      ((q - p : ℕ) : ℝ) - b ≤
        ((wordDist D.alphabet.carrier
          (vertex v (auxiliaryCycleWord left arc right chord) p)
          (vertex v (auxiliaryCycleWord left arc right chord) q) : ℕ) : ℝ) := by
  intro s hs hsTarget p q hp hpq hq
  by_cases hsLeft : s < left.length
  · exact False.elim (hsTarget (hleft s hsLeft))
  by_cases hsArc : s < left.length + nArc
  · let r := s - left.length
    have hr : r < nArc := by dsimp [r]; omega
    have hsEq : s = left.length + r := by dsimp [r]; omega
    have hs1Eq : s + 1 = left.length + (r + 1) := by omega
    have hcut0 := auxiliaryCycleCut_arc left right harc.cut (le_of_lt hr)
    have hcut1 := auxiliaryCycleCut_arc left right harc.cut (by omega : r + 1 ≤ nArc)
    rw [hsEq, hcut0] at hp
    rw [hs1Eq, hcut1] at hq
    have hpArc : arcCut r ≤ p - left.length := by omega
    have hpqArc : p - left.length ≤ q - left.length := by omega
    have hqArc : q - left.length ≤ arcCut (r + 1) := by omega
    have hpLen : p - left.length ≤ arc.length := by
      have := harc.cut.le_length (by omega : r + 1 ≤ nArc)
      omega
    have hqLen : q - left.length ≤ arc.length := by
      have := harc.cut.le_length (by omega : r + 1 ≤ nArc)
      omega
    have hpEq : left.length + (p - left.length) = p := by omega
    have hqEq : left.length + (q - left.length) = q := by omega
    have hdiff : q - left.length - (p - left.length) = q - p := by omega
    have hqa := harc.quasi r hr (p - left.length) (q - left.length)
      hpArc hpqArc hqArc
    rw [hdiff] at hqa
    have hvp :
        vertex v (auxiliaryCycleWord left arc right chord) p =
          vertex (v * RelLetter.listVal (revWord left)) arc
            (p - left.length) := by
      conv_lhs => rw [← hpEq]
      rw [vertex_auxiliaryCycle_arc v left arc right chord hpLen]
    have hvq :
        vertex v (auxiliaryCycleWord left arc right chord) q =
          vertex (v * RelLetter.listVal (revWord left)) arc
            (q - left.length) := by
      conv_lhs => rw [← hqEq]
      rw [vertex_auxiliaryCycle_arc v left arc right chord hqLen]
    rw [hvp, hvq]
    exact hqa
  by_cases hsRight : s < left.length + nArc + right.length
  · let r := s - (left.length + nArc)
    have hr : r < right.length := by dsimp [r]; omega
    have hsEq : left.length + nArc + r = s := by dsimp [r]; omega
    have ht := hright r hr
    rw [hsEq] at ht
    exact False.elim (hsTarget ht)
  · let r := s - (left.length + nArc + right.length)
    have hr : r < chord.length := by dsimp [r]; omega
    have hsEq : s = left.length + nArc + right.length + r := by dsimp [r]; omega
    have hs1Eq : s + 1 = left.length + nArc + right.length + (r + 1) := by omega
    have hcut0 := auxiliaryCycleCut_chord left right harc.cut (r := r)
    have hcut1 := auxiliaryCycleCut_chord left right harc.cut (r := r + 1)
    rw [hsEq, hcut0] at hp
    rw [hs1Eq, hcut1] at hq
    let off := left.length + arc.length + right.length
    have hpqChord : p - off ≤ q - off := by omega
    have hqLen : q - off ≤ chord.length := by omega
    have hpEq : off + (p - off) = p := by dsimp [off]; omega
    have hqEq : off + (q - off) = q := by dsimp [off]; omega
    have hdiff : q - off - (p - off) = q - p := by omega
    have hgeo := sub_le_wordDist_vertex D hchord (p - off) (q - off)
      hpqChord hqLen
    have hgeoR : (((q - p : ℕ) : ℝ)) ≤
        ((wordDist D.alphabet.carrier
          (vertex (v * RelLetter.listVal ((revWord left ++ arc) ++ right))
            chord (p - off))
          (vertex (v * RelLetter.listVal ((revWord left ++ arc) ++ right))
            chord (q - off)) : ℕ) : ℝ) := by
      rw [← hdiff]
      exact_mod_cast hgeo
    have hvp :
        vertex v (auxiliaryCycleWord left arc right chord) p =
          vertex (v * RelLetter.listVal ((revWord left ++ arc) ++ right))
            chord (p - off) := by
      conv_lhs => rw [← hpEq]
      simp only [off]
      rw [vertex_auxiliaryCycle_chord]
    have hvq :
        vertex v (auxiliaryCycleWord left arc right chord) q =
          vertex (v * RelLetter.listVal ((revWord left ++ arc) ++ right))
            chord (q - off) := by
      conv_lhs => rw [← hqEq]
      simp only [off]
      rw [vertex_auxiliaryCycle_chord]
    rw [hvp, hvq]
    linarith

/-- Admissibility is inherited by the four paths of an auxiliary cycle. -/
theorem isLetter_auxiliaryCycleWord (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {left arc right chord : List (RelLetter G Λ)}
    (hleft : ∀ x ∈ left, D.IsLetter x) (harc : ∀ x ∈ arc, D.IsLetter x)
    (hright : ∀ x ∈ right, D.IsLetter x)
    (hchord : ∀ x ∈ chord, D.IsLetter x) :
    ∀ x ∈ auxiliaryCycleWord left arc right chord, D.IsLetter x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact isLetter_of_mem_revWord D hsymm hleft x hx
      · exact harc x hx
    · exact hright x hx
  · exact hchord x hx

/-- **An interior component of the inherited arc starts a component of `c_j`.**

The broken endpoint components are omitted from `arc`, so every retained
type-(1) component is interior and its two maximality letters are unchanged by
the three appended paths. -/
theorem isComp_auxiliaryCycle_arc (lam : Λ)
    (left arc right chord : List (RelLetter G Λ)) {i k : ℕ}
    (hcomp : IsComp lam arc i k) (hi : 1 ≤ i) (hk : k < arc.length) :
    IsComp lam (auxiliaryCycleWord left arc right chord)
      (left.length + i) (left.length + k) := by
  have hseg : ((auxiliaryCycleWord left arc right chord).drop left.length).take
      arc.length = arc := by
    simp [auxiliaryCycleWord, revWord]
  have hcomp' : IsComp lam
      (((auxiliaryCycleWord left arc right chord).drop left.length).take arc.length)
      i k := by
    rwa [hseg]
  have hk' : k <
      (((auxiliaryCycleWord left arc right chord).drop left.length).take arc.length).length := by
    rw [hseg]
    exact hk
  exact isComp_of_isComp_segment lam (auxiliaryCycleWord left arc right chord)
    hcomp' hi hk' (by simp [auxiliaryCycleWord, revWord])

/-- **An interior chord component starts a component of `c_j`.**

This is the type-(4) counterpart of `isComp_auxiliaryCycle_arc`.  Ordering the
partners lets the construction trim the two endpoint partners, leaving each
recorded `y_j` interior to the selected chord segment. -/
theorem isComp_auxiliaryCycle_chord (lam : Λ)
    (left arc right chord : List (RelLetter G Λ)) {i k : ℕ}
    (hcomp : IsComp lam chord i k) (hi : 1 ≤ i) (hk : k < chord.length) :
    IsComp lam (auxiliaryCycleWord left arc right chord)
      (left.length + arc.length + right.length + i)
      (left.length + arc.length + right.length + k) := by
  let off := left.length + arc.length + right.length
  have hseg : ((auxiliaryCycleWord left arc right chord).drop off).take
      chord.length = chord := by
    have hoff : off = ((revWord left ++ arc) ++ right).length := by
      simp [off, length_revWord, Nat.add_assoc]
    change ((((revWord left ++ arc) ++ right) ++ chord).drop off).take
      chord.length = chord
    rw [hoff, List.drop_left, List.take_length]
  have hcomp' : IsComp lam
      (((auxiliaryCycleWord left arc right chord).drop off).take chord.length)
      i k := by
    rwa [hseg]
  have hk' : k <
      (((auxiliaryCycleWord left arc right chord).drop off).take chord.length).length := by
    rw [hseg]
    exact hk
  have hauxLen : (auxiliaryCycleWord left arc right chord).length =
      off + chord.length := by
    simp [off, auxiliaryCycleWord, length_revWord, Nat.add_assoc]
  have hoffEnd : off + chord.length ≤
      (auxiliaryCycleWord left arc right chord).length := by
    rw [hauxLen]
  have htrans := isComp_of_isComp_segment lam
    (auxiliaryCycleWord left arc right chord) hcomp' hi
      hk' hoffEnd
  simpa [off, Nat.add_assoc] using htrans

omit [Group G] in
/-- **A recorded connector is a one-letter component once its two boundary
letters are excluded.**

The construction obtains the middle letter from
`exists_component_connector_pair`; the ordered endpoint argument supplies the
two maximality clauses.  Empty connectors create no component and therefore
need no case here. -/
theorem isComp_singleton_of_boundary (lam : Λ)
    (cycle : List (RelLetter G Λ)) {p : ℕ} (hp : p < cycle.length)
    (hletter : (cycle[p]'hp).IsCompOf lam)
    (hprev : ∀ q : ℕ, p = q + 1 → ∀ hq : q < cycle.length,
      ¬ (cycle[q]'hq).IsCompOf lam)
    (hnext : ∀ hn : p + 1 < cycle.length,
      ¬ (cycle[p + 1]'hn).IsCompOf lam) :
    IsComp lam cycle p (p + 1) := by
  refine ⟨by omega, by omega, ?_, hprev, hnext⟩
  intro q hpq hqp hq
  have hqp' : q = p := by omega
  subst q
  exact hletter

/-- **Every position of `c_j` lies in exactly one of its four paths.**

This is the case split used by both letter coverage and cross-path separation;
it keeps the append arithmetic out of the geometric argument. -/
theorem auxiliaryCycle_position_cases (left arc right chord :
    List (RelLetter G Λ)) {q : ℕ}
    (hq : q < (auxiliaryCycleWord left arc right chord).length) :
    q < left.length ∨
      (left.length ≤ q ∧ q < left.length + arc.length) ∨
      (left.length + arc.length ≤ q ∧
        q < left.length + arc.length + right.length) ∨
      (left.length + arc.length + right.length ≤ q ∧
        q < left.length + arc.length + right.length + chord.length) := by
  simp [auxiliaryCycleWord, revWord] at hq
  omega

/-- **Covering peripheral letters by recorded runs supplies `hexhaust`.**

This is the concrete exhaustion step for the four-path word.  It is enough to
classify each `targetLam s`-letter into one of the complete family `All` of
arc, connector, or chord runs.  If a purported component start lay strictly
inside the recorded run, its predecessor would simultaneously be, and not be,
a `targetLam s`-letter. -/
theorem auxiliaryCycle_componentStarts_exhausted
    (left arc right chord : List (RelLetter G Λ))
    (Target All : Finset ℕ) (targetLam allLam : ℕ → Λ)
    (allPos allFinish : ℕ → ℕ)
    (hrecord : ∀ t ∈ All,
      IsComp (allLam t) (auxiliaryCycleWord left arc right chord)
        (allPos t) (allFinish t))
    (hcover : ∀ s ∈ Target, ∀ q : ℕ,
      ∀ hq : q < (auxiliaryCycleWord left arc right chord).length,
      ((auxiliaryCycleWord left arc right chord)[q]'hq).IsCompOf (targetLam s) →
      ∃ t ∈ All, allLam t = targetLam s ∧
        allPos t ≤ q ∧ q < allFinish t) :
    ∀ s ∈ Target, ∀ q : ℕ,
      IsCompStart (targetLam s) (auxiliaryCycleWord left arc right chord) q →
      ∃ t ∈ All, allLam t = targetLam s ∧ allPos t = q := by
  intro s hs q hqstart
  obtain ⟨qend, hqcomp⟩ := hqstart
  have hqltEnd : q < qend := hqcomp.1
  have hqendLen : qend ≤ (auxiliaryCycleWord left arc right chord).length :=
    hqcomp.2.1
  have hqlen : q < (auxiliaryCycleWord left arc right chord).length := by
    exact hqltEnd.trans_le hqendLen
  have hqletter : ((auxiliaryCycleWord left arc right chord)[q]'hqlen).IsCompOf
      (targetLam s) := hqcomp.2.2.1 q le_rfl hqcomp.1 hqlen
  obtain ⟨t, ht, hlam, htq, hqfinish⟩ := hcover s hs q hqlen hqletter
  refine ⟨t, ht, hlam, ?_⟩
  by_contra hne
  have hlt : allPos t < q := by omega
  have hpredlen : q - 1 < (auxiliaryCycleWord left arc right chord).length := by
    omega
  have hpredT :
      ((auxiliaryCycleWord left arc right chord)[q - 1]'hpredlen).IsCompOf
        (allLam t) :=
    (hrecord t ht).2.2.1 (q - 1) (by omega) (by omega) hpredlen
  have hpredS :
      ((auxiliaryCycleWord left arc right chord)[q - 1]'hpredlen).IsCompOf
        (targetLam s) := by
    simpa only [hlam] using hpredT
  exact hqcomp.2.2.2.1 (q - 1) (by omega) hpredlen hpredS

/-- **The type-(1)/(3)/(4) side-isolation assertion for an auxiliary cycle.**

`Target` indexes exactly the peripheral components under consideration: inherited
polygon components (type (1)), nonempty connectors (type (3)), and selected
chord components `y_j` (type (4)).  `All` separately indexes every component
start whose label can oppose a target, including components lying inside a
type-(2) quasi-geodesic subpath.  The geometric construction supplies three
facts: each target position starts its component, every opposing component is
recorded in `All`, and no target is connected to a distinct recorded opponent.
These facts are precisely, and sufficient for, DGO's isolation assertion.

Keeping `hexhaust` label-relative is important: an auxiliary cycle may contain
components for many peripheral subgroups, and isolatedness of the component
indexed by `s` only quantifies over starts with label `targetLam s`. -/
theorem isIsolated_auxiliaryCycle_sides (D : RelGenSet G Λ) (v : G)
    (left arc right chord : List (RelLetter G Λ))
    (Target All : Finset ℕ) (targetLam allLam : ℕ → Λ)
    (targetPos allPos : ℕ → ℕ)
    (hstart : ∀ s ∈ Target,
      IsCompStart (targetLam s) (auxiliaryCycleWord left arc right chord)
        (targetPos s))
    (hexhaust : ∀ s ∈ Target, ∀ q : ℕ,
      IsCompStart (targetLam s) (auxiliaryCycleWord left arc right chord) q →
      ∃ t ∈ All, allLam t = targetLam s ∧ allPos t = q)
    (hsep : ∀ s ∈ Target, ∀ t ∈ All,
      allLam t = targetLam s → allPos t ≠ targetPos s →
      ¬ Connected D.fam (targetLam s) v
        (auxiliaryCycleWord left arc right chord) (targetPos s) (allPos t)) :
    ∀ s ∈ Target,
      IsIsolated D.fam (targetLam s) v (auxiliaryCycleWord left arc right chord)
        (targetPos s) := by
  intro s hs
  refine ⟨hstart s hs, ?_⟩
  intro q hqs hqstart hconn
  obtain ⟨t, ht, hlam, hpos⟩ := hexhaust s hs q hqstart
  subst q
  exact hsep s hs t ht hlam (by omega) hconn

/-- **Same-path entries of `hsep` come directly from geodesicity.**

This is the reusable instance for two type-(1) components on the inherited arc,
or two type-(4) components on the chord.  The chain is stated directly in the
auxiliary cycle's coordinates, so it applies after the corresponding append
offset has been calculated. -/
theorem not_connected_auxiliaryCycle_same_path (D : RelGenSet G Λ) (v : G)
    (left arc right chord : List (RelLetter G Λ)) {lam : Λ} {c₀ n i j : ℕ}
    (hchain : IsGeodesicChain D.alphabet.carrier
      (fun m => vertex v (auxiliaryCycleWord left arc right chord) (c₀ + m)) n)
    (hi : IsCompStart lam (auxiliaryCycleWord left arc right chord) i)
    (hj : IsCompStart lam (auxiliaryCycleWord left arc right chord) j)
    (hne : i ≠ j) (hci : c₀ ≤ i) (hin : i ≤ c₀ + n)
    (hcj : c₀ ≤ j) (hjn : j ≤ c₀ + n) :
    ¬ Connected D.fam lam v (auxiliaryCycleWord left arc right chord) i j :=
  not_connected_of_isCompStart_of_geodesicChain D hchain hi hj hne hci hin hcj hjn

/-- **A broken component has at most one partner on a geodesic chord.**

The earlier injectivity theorem says two broken components cannot share a
partner.  This is the converse uniqueness needed for Target-vs-All separation:
if one broken component met two chord components, those two components would be
connected through it, impossible along a geodesic chain. -/
theorem chord_partner_unique_of_geodesicChain (D : RelGenSet G Λ) {lam : Λ}
    {v : G} {half : List (RelLetter G Λ)} {c₀ n p q r : ℕ}
    (hchain : IsGeodesicChain D.alphabet.carrier
      (fun m => vertex v half (c₀ + m)) n)
    (hq : IsCompStart lam half q) (hr : IsCompStart lam half r)
    (hqc : c₀ ≤ q) (hqn : q ≤ c₀ + n)
    (hrc : c₀ ≤ r) (hrn : r ≤ c₀ + n)
    (hpq : Connected D.fam lam v half p q)
    (hpr : Connected D.fam lam v half p r) : q = r := by
  by_contra hne
  exact not_connected_of_isCompStart_of_geodesicChain D hchain hq hr hne
    hqc hqn hrc hrn (connected_trans (connected_symm hpq) hpr)

/-- **Every charged side inherits separation from its broken anchor.**

The partner `y_j` and the nonempty connectors `e_j,f_j` lie in the same
`H_lam`-coset as the broken polygon component.  Thus a connection from any of
them to an arbitrary type-(2) opponent would connect the broken anchor to that
opponent, contradicting the original arc-isolation lemma. -/
theorem not_connected_of_connected_anchor {H : Λ → Subgroup G} {lam : Λ}
    {v : G} {cycle : List (RelLetter G Λ)} {anchor target opponent : ℕ}
    (hanchor : Connected H lam v cycle anchor target)
    (hnot : ¬ Connected H lam v cycle anchor opponent) :
    ¬ Connected H lam v cycle target opponent := by
  intro hconn
  exact hnot (connected_trans hanchor hconn)

/-- **Two charged sides inherit separation from two distinct broken anchors.**

Partner injectivity/order supplies distinct anchors; original isolation supplies
their nonconnection.  This single coset calculation handles every combination
of `y_j`, `e_j`, and `f_j` belonging to different charges. -/
theorem not_connected_of_connected_anchors {H : Λ → Subgroup G} {lam : Λ}
    {v : G} {cycle : List (RelLetter G Λ)}
    {anchor₁ target₁ anchor₂ target₂ : ℕ}
    (h₁ : Connected H lam v cycle anchor₁ target₁)
    (h₂ : Connected H lam v cycle anchor₂ target₂)
    (hnot : ¬ Connected H lam v cycle anchor₁ anchor₂) :
    ¬ Connected H lam v cycle target₁ target₂ := by
  intro hconn
  exact hnot (connected_trans h₁
    (connected_trans hconn (connected_symm h₂)))

/-- **A forbidden connection transports through the cycle dictionaries.**

For cross-path pairs, the ordered construction identifies both auxiliary-cycle
vertices with vertices of the relevant half-polygon.  Once the corresponding
half-polygon components are known not to be connected (by survivor isolation or
the ordered partner argument), no new group-theoretic proof is needed. -/
theorem not_connected_auxiliaryCycle_of_vertex_transport (D : RelGenSet G Λ)
    (lam : Λ) (vHalf vCycle : G) (half : List (RelLetter G Λ))
    (left arc right chord : List (RelLetter G Λ)) {i j p q : ℕ}
    (hpi : vertex vCycle (auxiliaryCycleWord left arc right chord) p =
      vertex vHalf half i)
    (hqj : vertex vCycle (auxiliaryCycleWord left arc right chord) q =
      vertex vHalf half j)
    (hnot : ¬ Connected D.fam lam vHalf half i j) :
    ¬ Connected D.fam lam vCycle (auxiliaryCycleWord left arc right chord) p q := by
  intro hconn
  apply hnot
  show (vertex vHalf half i)⁻¹ * vertex vHalf half j ∈ D.fam lam
  rw [← hpi, ← hqj]
  exact hconn

/-- **A first-half type-(1) target is separated from an arbitrary type-(2)
opponent in its auxiliary cycle.**

Only the opponent's first same-label letter is transported.  This is what
allows `All` to contain components created at the endpoints of a restricted
type-(2) subpath. -/
theorem not_connected_auxiliaryCycle_firstHalf_typeTwo
    (D : RelGenSet G Λ) (lam : Λ) (v vCycle : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i j p q : ℕ}
    (left arc right chord : List (RelLetter G Λ))
    (hlet : ∀ x ∈ w, D.IsLetter x) (hb : c b ≤ w.length)
    (hi : i < c b - c a) (hj : j < c b - c a) (hne : j ≠ i)
    (hcomp : IsComp lam w (c a + i) (c a + i + 1))
    (hiso : IsIsolated D.fam lam v w (c a + i))
    (t : List (RelLetter G Λ))
    (hjlen : j < (firstHalf w c a b t).length)
    (hco : ((firstHalf w c a b t)[j]'hjlen).IsCompOf lam)
    (hpi : vertex vCycle (auxiliaryCycleWord left arc right chord) p =
      vertex (vertex v w (c a)) (firstHalf w c a b t) i)
    (hqj : vertex vCycle (auxiliaryCycleWord left arc right chord) q =
      vertex (vertex v w (c a)) (firstHalf w c a b t) j) :
    ¬ Connected D.fam lam vCycle (auxiliaryCycleWord left arc right chord) p q :=
  not_connected_auxiliaryCycle_of_vertex_transport D lam
    (vertex v w (c a)) vCycle (firstHalf w c a b t) left arc right chord hpi hqj
    (not_connected_firstHalf_arc_of_isCompOf D lam v w c hlet hb hi hj hne
      hcomp hiso t hjlen hco)

/-- **A chord partner or connector charged to a first-half broken component is
also separated from every type-(2) opponent.**

The new input over `not_connected_auxiliaryCycle_firstHalf_typeTwo` is exactly
the incidence selected by the greedy enumeration: `anchor` is the broken
position and `target` is any component in its coset (the selected `y_j`, or a
nonempty `e_j`/`f_j`).  Transporting through that incidence reduces the claim
to the already proved broken-target case. -/
theorem not_connected_auxiliaryCycle_firstHalf_charged_typeTwo
    (D : RelGenSet G Λ) (lam : Λ) (v vCycle : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b anchor target j p q : ℕ}
    (left arc right chord : List (RelLetter G Λ))
    (hlet : ∀ x ∈ w, D.IsLetter x) (hb : c b ≤ w.length)
    (hanchor : anchor < c b - c a) (hj : j < c b - c a)
    (hne : j ≠ anchor)
    (hcomp : IsComp lam w (c a + anchor) (c a + anchor + 1))
    (hiso : IsIsolated D.fam lam v w (c a + anchor))
    (t : List (RelLetter G Λ))
    (hjlen : j < (firstHalf w c a b t).length)
    (hco : ((firstHalf w c a b t)[j]'hjlen).IsCompOf lam)
    (hcharge : Connected D.fam lam (vertex v w (c a))
      (firstHalf w c a b t) anchor target)
    (hpi : vertex vCycle (auxiliaryCycleWord left arc right chord) p =
      vertex (vertex v w (c a)) (firstHalf w c a b t) target)
    (hqj : vertex vCycle (auxiliaryCycleWord left arc right chord) q =
      vertex (vertex v w (c a)) (firstHalf w c a b t) j) :
    ¬ Connected D.fam lam vCycle (auxiliaryCycleWord left arc right chord) p q :=
  not_connected_auxiliaryCycle_of_vertex_transport D lam
    (vertex v w (c a)) vCycle (firstHalf w c a b t) left arc right chord hpi hqj
    (not_connected_of_connected_anchor hcharge
      (not_connected_firstHalf_arc_of_isCompOf D lam v w c hlet hb hanchor hj
        hne hcomp hiso t hjlen hco))

/-- **The wrapped-half counterpart for an arbitrary type-(2) opponent.** -/
theorem not_connected_auxiliaryCycle_secondHalf_typeTwo
    (D : RelGenSet G Λ) (lam : Λ) (v vCycle : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) {a b i j p q : ℕ}
    (left arc right chord : List (RelLetter G Λ))
    (hlet : ∀ x ∈ w, D.IsLetter x) (ha : c a ≤ c b)
    (hb : c b ≤ w.length) (hi : i < (w.length - c b) + c a)
    (hj : j < (w.length - c b) + c a) (hne : j ≠ i)
    (hcomp : IsComp lam (rotWord w (c b)) i (i + 1))
    (hiso : IsIsolated D.fam lam (vertex v w (c b)) (rotWord w (c b)) i)
    (t : List (RelLetter G Λ))
    (hjlen : j < (secondHalf w c a b t).length)
    (hco : ((secondHalf w c a b t)[j]'hjlen).IsCompOf lam)
    (hpi : vertex vCycle (auxiliaryCycleWord left arc right chord) p =
      vertex (vertex v w (c b)) (secondHalf w c a b t) i)
    (hqj : vertex vCycle (auxiliaryCycleWord left arc right chord) q =
      vertex (vertex v w (c b)) (secondHalf w c a b t) j) :
    ¬ Connected D.fam lam vCycle (auxiliaryCycleWord left arc right chord) p q :=
  not_connected_auxiliaryCycle_of_vertex_transport D lam
    (vertex v w (c b)) vCycle (secondHalf w c a b t) left arc right chord hpi hqj
    (not_connected_secondHalf_arc_of_isCompOf D lam v w c hlet ha hb hi hj hne
      hcomp hiso t hjlen hco)

/-- **Wrapped-half charged targets are separated from arbitrary type-(2)
opponents.**  This is the mirror-copy instance needed for the second family of
auxiliary cycles in DGO's construction. -/
theorem not_connected_auxiliaryCycle_secondHalf_charged_typeTwo
    (D : RelGenSet G Λ) (lam : Λ) (v vCycle : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    {a b anchor target j p q : ℕ}
    (left arc right chord : List (RelLetter G Λ))
    (hlet : ∀ x ∈ w, D.IsLetter x) (ha : c a ≤ c b)
    (hb : c b ≤ w.length) (hanchor : anchor < (w.length - c b) + c a)
    (hj : j < (w.length - c b) + c a) (hne : j ≠ anchor)
    (hcomp : IsComp lam (rotWord w (c b)) anchor (anchor + 1))
    (hiso : IsIsolated D.fam lam (vertex v w (c b))
      (rotWord w (c b)) anchor)
    (t : List (RelLetter G Λ))
    (hjlen : j < (secondHalf w c a b t).length)
    (hco : ((secondHalf w c a b t)[j]'hjlen).IsCompOf lam)
    (hcharge : Connected D.fam lam (vertex v w (c b))
      (secondHalf w c a b t) anchor target)
    (hpi : vertex vCycle (auxiliaryCycleWord left arc right chord) p =
      vertex (vertex v w (c b)) (secondHalf w c a b t) target)
    (hqj : vertex vCycle (auxiliaryCycleWord left arc right chord) q =
      vertex (vertex v w (c b)) (secondHalf w c a b t) j) :
    ¬ Connected D.fam lam vCycle (auxiliaryCycleWord left arc right chord) p q :=
  not_connected_auxiliaryCycle_of_vertex_transport D lam
    (vertex v w (c b)) vCycle (secondHalf w c a b t) left arc right chord hpi hqj
    (not_connected_of_connected_anchor hcharge
      (not_connected_secondHalf_arc_of_isCompOf D lam v w c hlet ha hb hanchor
        hj hne hcomp hiso t hjlen hco))

/-- **Connected components supply DGO's two connector edges `f_j,e_j`.**

The start connector is the connectedness witness itself.  The end connector is
obtained by transporting it across the two component spans inside `H_lam`.
A nontrivial connector is represented by one peripheral letter; a trivial one
is the empty path, so no spurious identity-loop side is introduced. -/
theorem exists_component_connector_pair (D : RelGenSet G Λ) (lam : Λ)
    {pm pp ym yp : G} (hp : pm⁻¹ * pp ∈ D.fam lam)
    (hy : ym⁻¹ * yp ∈ D.fam lam) (hconn : pm⁻¹ * ym ∈ D.fam lam) :
    ∃ f e : List (RelLetter G Λ),
      f.length ≤ 1 ∧ e.length ≤ 1 ∧
      (∀ x ∈ f, D.IsLetter x) ∧ (∀ x ∈ e, D.IsLetter x) ∧
      RelLetter.listVal f = pm⁻¹ * ym ∧
      RelLetter.listVal e = pp⁻¹ * yp := by
  classical
  have he : pp⁻¹ * yp ∈ D.fam lam := by
    have heq : pp⁻¹ * yp = (pm⁻¹ * pp)⁻¹ *
        ((pm⁻¹ * ym) * (ym⁻¹ * yp)) := by
      group
    rw [heq]
    exact mul_mem (inv_mem hp) (mul_mem hconn hy)
  let f : List (RelLetter G Λ) :=
    if pm⁻¹ * ym = 1 then [] else [RelLetter.comp lam (pm⁻¹ * ym)]
  let e : List (RelLetter G Λ) :=
    if pp⁻¹ * yp = 1 then [] else [RelLetter.comp lam (pp⁻¹ * yp)]
  refine ⟨f, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hf : pm⁻¹ * ym = 1 <;> simp [f, hf]
  · by_cases heq : pp⁻¹ * yp = 1 <;> simp [e, heq]
  · intro x hx
    by_cases hf : pm⁻¹ * ym = 1
    · simp [f, hf] at hx
    · have hx' : x = RelLetter.comp lam (pm⁻¹ * ym) := by
        simpa [f, hf] using hx
      subst x
      exact hconn
  · intro x hx
    by_cases heq : pp⁻¹ * yp = 1
    · simp [e, heq] at hx
    · have hx' : x = RelLetter.comp lam (pp⁻¹ * yp) := by
        simpa [e, heq] using hx
      subst x
      exact he
  · by_cases hf : pm⁻¹ * ym = 1
    · simp [f, hf, RelLetter.listVal_nil]
    · simp [f, hf, listVal_singleton, RelLetter.val]
  · by_cases heq : pp⁻¹ * yp = 1
    · simp [e, heq, RelLetter.listVal_nil]
    · simp [e, heq, listVal_singleton, RelLetter.val]

/-- **The charge.**  A component connected to another across two edges is no
deeper than the three of them together. -/
theorem span_mem_relBall_of_quadrilateral (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (lam : Λ) {pm pp ym yp : G}
    {rf ry re : ℕ} (hf : pm⁻¹ * ym ∈ D.relBall lam rf)
    (hy : ym⁻¹ * yp ∈ D.relBall lam ry)
    (he : pp⁻¹ * yp ∈ D.relBall lam re) :
    pm⁻¹ * pp ∈ D.relBall lam (rf + ry + re) := by
  have hkey : pm⁻¹ * pp = (pm⁻¹ * ym) * ((ym⁻¹ * yp) * (pp⁻¹ * yp)⁻¹) := by
    group
  have hinv : (pp⁻¹ * yp)⁻¹ ∈ D.relBall lam re := relBall_inv D lam hsymm he
  have h1 : (ym⁻¹ * yp) * (pp⁻¹ * yp)⁻¹ ∈ D.relBall lam (ry + re) :=
    relBall_mul D lam hy hinv
  have hsum : rf + (ry + re) = rf + ry + re := by omega
  rw [hkey, ← hsum]
  exact relBall_mul D lam hf h1

/-- **Witness functions on two disjoint component families combine by
addition.**

This is the witness-summing step of Proposition 4.14 with all geometry removed.
Once the distinguished indices have been partitioned between two collections
of smaller cycles, choose the radius supplied on the appropriate side.  The
two finite sums add exactly, so bounds `K₁` and `K₂` combine to `K₁+K₂`.

Repeated application combines any finite family of cycles.  The remaining
geometric task is therefore only to construct a disjoint assignment of every
original distinguished component to either a surviving isolated component or
one charged cycle; no further radius algebra is hidden. -/
theorem combine_relBall_witnesses (D : RelGenSet G Λ)
    (I I₁ I₂ : Finset ℕ) (hdisj : Disjoint I₁ I₂) (hcover : I = I₁ ∪ I₂)
    (lam : ℕ → Λ) (span : ℕ → G) (r₁ r₂ : ℕ → ℕ) (K₁ K₂ : ℕ)
    (hmem₁ : ∀ s ∈ I₁, span s ∈ D.relBall (lam s) (r₁ s))
    (hmem₂ : ∀ s ∈ I₂, span s ∈ D.relBall (lam s) (r₂ s))
    (hsum₁ : ∑ s ∈ I₁, r₁ s ≤ K₁) (hsum₂ : ∑ s ∈ I₂, r₂ s ≤ K₂) :
    ∃ r : ℕ → ℕ,
      (∀ s ∈ I, span s ∈ D.relBall (lam s) (r s)) ∧
      ∑ s ∈ I, r s ≤ K₁ + K₂ := by
  classical
  let r : ℕ → ℕ := fun s => if s ∈ I₁ then r₁ s else r₂ s
  refine ⟨r, ?_, ?_⟩
  · intro s hs
    have hsunion : s ∈ I₁ ∪ I₂ := by rwa [← hcover]
    rcases Finset.mem_union.mp hsunion with hs₁ | hs₂
    · simpa [r, hs₁] using hmem₁ s hs₁
    · have hsnot : s ∉ I₁ := by
        intro hs₁
        exact Finset.disjoint_left.mp hdisj hs₁ hs₂
      simpa [r, hsnot] using hmem₂ s hs₂
  · rw [hcover, Finset.sum_union hdisj]
    have heq₁ : ∑ s ∈ I₁, r s = ∑ s ∈ I₁, r₁ s := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [r, hs]
    have heq₂ : ∑ s ∈ I₂, r s = ∑ s ∈ I₂, r₂ s := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsnot : s ∉ I₁ := by
        intro hs₁
        exact Finset.disjoint_left.mp hdisj hs₁ hs
      simp [r, hsnot]
    rw [heq₁, heq₂]
    omega

/-- **Witness functions from an arbitrary finite family combine fiberwise.**

`owner s` is the auxiliary cycle charged with the original distinguished
component `s`.  Each local witness function is only summed over its ownership
fiber.  Summing those fiber estimates gives one witness on the original
family, with total radius bounded by the sum of the child bounds.

This is the family-level version of `combine_relBall_witnesses`.  It does not
assume that the auxiliary cycles are ordered along the chord; the owner map is
the only bookkeeping needed here. -/
theorem combine_relBall_witnesses_finite (D : RelGenSet G Λ)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : Finset ℕ) (owner : ℕ → κ) (lam : ℕ → Λ) (span : ℕ → G)
    (radius : κ → ℕ → ℕ) (bound : κ → ℕ)
    (hmem : ∀ s ∈ I,
      span s ∈ D.relBall (lam s) (radius (owner s) s))
    (hsum : ∀ j : κ,
      ∑ s ∈ I, (if owner s = j then radius j s else 0) ≤ bound j) :
    ∃ r : ℕ → ℕ,
      (∀ s ∈ I, span s ∈ D.relBall (lam s) (r s)) ∧
      ∑ s ∈ I, r s ≤ ∑ j : κ, bound j := by
  classical
  let r : ℕ → ℕ := fun s => radius (owner s) s
  refine ⟨r, ?_, ?_⟩
  · intro s hs
    exact hmem s hs
  · calc
      ∑ s ∈ I, r s =
          ∑ s ∈ I, ∑ j : κ, (if owner s = j then radius j s else 0) := by
            apply Finset.sum_congr rfl
            intro s hs
            simp [r]
      _ = ∑ j : κ, ∑ s ∈ I,
          (if owner s = j then radius j s else 0) := by
            rw [Finset.sum_comm]
      _ ≤ ∑ j : κ, bound j :=
        Finset.sum_le_sum fun j _ => hsum j

end DGOPolygonCut
end GGT
end GroupApproximation
