import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyNamed
import GroupApproximation.GGT.HullSCRelatorSeparation2OtherArc

/-!
# The polygon, applied: the four cases of step (c)

The chain's geometric input arrives as a quadrilateral and leaves as two
elements of a relative ball.  This module is the join between the two: one
lemma that runs the polygon on the configuration the relator builds, and four
that spend its output, one per case of Olshanskii's step (c).

## The configuration

The quadrilateral is the one the ledger names: `px ++ [a_b^e] ++ rx ++ revWord
[a_b^f]`, with the two long sides SINGLE block letters and the two short sides
base-spelled connectors.  In that configuration the polygon's own gaps are the
connectors themselves --- `(vertex 1 s 0)⁻¹ * (listVal px * vertex 1 q 0)` is
`listVal px`, and `(listVal px * vertex 1 q 1)⁻¹ * vertex 1 s 1` is `listVal rx`
once the closing relation is used --- so what the polygon delivers is exactly
this: **the two connectors of a matched pair lie in a relative ball whose radius
does not depend on the pair.**  That is the rigidity in the currency the design's
separation and diagonal clauses are stated in, and `exists_eps_blockQuad` is it.

Four of the packaged theorem's clauses are discharged here rather than assumed,
and all four are vacuous in this configuration:

* the two `IsComp` clauses, because a one-letter side is a component by itself;
* the innermost clause of the first reading, whose range is exactly the third
  side, which is base-spelled (`not_isCompStart_fourGon_r`);
* the other-arc clause, whose first range is empty --- there is no index
  strictly between `|px| + 1 + |rx|` and the length --- and whose second range
  is the first side, base-spelled (`not_isCompStart_fourGon_p`).

What survives as a hypothesis is the isolated-component bound in the six-sided
form, the quadrilateral's quasi-geodesicity, that the two components are
connected, and that both connectors are nonempty.  The last is the piece side
condition and the degenerate `rx = []` branch it excludes; the third is what the
dichotomy of the caller discharges, a component connected to nothing being
isolated and so bounded outright, against a deep power.

## The four cases

Each takes the two ball memberships, the closing relation of the block
quadrilateral, and the two block letters, and returns what
`RelWord.IsPiece` excludes.

* aligned --- both members rotations of the relator;
* mirrored --- both rotations of the formal inverse;
* the two mixed orders, which return `False`.

The aligned and mirrored cases also take the VERTEX relation, `y * vertex 1 w i
= vertex 1 w' j * listVal px`, which says no more than that `listVal px` is the
quadrilateral's first side: it is the definition of the left connector at the
matched block, and it is what makes the join's `y` the piece's own connector
rather than an arbitrary short element.  Once the design forces `listVal px = 1`
it collapses to the relation `HullSC.listVal_conj_of_alignedTrivial` consumes.
The mixed cases do not need it, which is why they run on the polygon's output
alone.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Quad

variable {G : Type u} [Group G]

/-- **The two connectors of a matched pair lie in a relative ball.**

The polygon, run on the block quadrilateral.  The radius is fixed before the
pair, before the relator, and before the design, which is what lets a caller run
the design at it. -/
theorem exists_eps_blockQuad {D : GGT.RelGenSet G Bool}
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hbound : ∀ mu bb : ℝ, 1 ≤ mu → 0 ≤ bb → ∃ C : ℕ, 0 < C ∧
      ∀ n : ℕ, n ≤ 6 → ∀ (v : G) (u : List (GGT.RelLetter G Bool)),
        GGT.OsinComponents.IsQuasiGeodesicPolygon D mu bb n v u →
        ∀ (nu : Bool) (i k : ℕ), GGT.OsinComponents.IsComp nu u i k →
          GGT.OsinComponents.IsIsolated D.fam nu v u i →
            (GGT.OsinComponents.vertex v u i)⁻¹ *
                GGT.OsinComponents.vertex v u k ∈ D.relBall nu (C * n))
    (mu bb : ℝ) (hmu : 1 ≤ mu) (hbb : 0 ≤ bb) :
    ∃ eps : ℕ, 0 < eps ∧
      ∀ (nu : Bool) (px rx : List (GGT.RelLetter G Bool)) (vq vs : G),
        (∀ c ∈ px, ∃ g : G, c = GGT.RelLetter.base g) →
        (∀ c ∈ rx, ∃ g : G, c = GGT.RelLetter.base g) →
        (∀ c ∈ px, D.IsLetter c) → (∀ c ∈ rx, D.IsLetter c) →
        vq ∈ D.fam nu → vs ∈ D.fam nu →
        0 < px.length → 0 < rx.length →
        vs = GGT.RelLetter.listVal px * vq * GGT.RelLetter.listVal rx →
        (∀ n : ℕ, n < 4 → ∀ c d : ℕ,
          GGT.OsinComponents.fourGonCut px [GGT.RelLetter.comp nu vq] rx
              [GGT.RelLetter.comp nu vs] n ≤ c → c ≤ d →
          d ≤ GGT.OsinComponents.fourGonCut px [GGT.RelLetter.comp nu vq] rx
              [GGT.RelLetter.comp nu vs] (n + 1) →
          ((d - c : ℕ) : ℝ) / mu - bb
            ≤ ((wordDist D.alphabet.carrier
                (GGT.OsinComponents.vertex (1 : G)
                  (px ++ [GGT.RelLetter.comp nu vq] ++ rx ++
                    GGT.OsinComponents.revWord
                      [GGT.RelLetter.comp nu vs]) c)
                (GGT.OsinComponents.vertex (1 : G)
                  (px ++ [GGT.RelLetter.comp nu vq] ++ rx ++
                    GGT.OsinComponents.revWord
                      [GGT.RelLetter.comp nu vs]) d) : ℕ) : ℝ)) →
        GGT.OsinComponents.Connected D.fam nu 1
            (px ++ [GGT.RelLetter.comp nu vq] ++ rx ++
              GGT.OsinComponents.revWord [GGT.RelLetter.comp nu vs])
            px.length (px.length + 1 + rx.length) →
        GGT.RelLetter.listVal px ∈ D.relBall nu eps ∧
          GGT.RelLetter.listVal rx ∈ D.relBall nu eps := by
  obtain ⟨C, hC0, hC⟩ :=
    GGT.OsinComponents.two_block_conj_mem_relBall D hbound hsymm mu bb hmu hbb
  refine ⟨C * 4, by omega, ?_⟩
  intro nu px rx vq vs hpx hrx hpxlet hrxlet hvq hvs hp0 hr0 hclose hqg hconn
  have hone : ([GGT.RelLetter.comp nu vq] : List (GGT.RelLetter G Bool)).length
      = 1 := by simp
  have htwo : ([GGT.RelLetter.comp nu vs] : List (GGT.RelLetter G Bool)).length
      = 1 := by simp
  -- the closing relation, read at the two one-letter sides
  have hclose' : GGT.RelLetter.listVal [GGT.RelLetter.comp nu vs]
      = GGT.RelLetter.listVal px *
          GGT.RelLetter.listVal [GGT.RelLetter.comp nu vq] *
          GGT.RelLetter.listVal rx := by
    rw [GGT.OsinComponents.listVal_singleton (GGT.RelLetter.comp nu vs),
      GGT.OsinComponents.listVal_singleton (GGT.RelLetter.comp nu vq)]
    exact hclose
  -- admissibility of the quadrilateral
  have hletq : ∀ c ∈ [GGT.RelLetter.comp nu vq], D.IsLetter c := by
    intro c hc
    rw [List.mem_cons] at hc
    rcases hc with rfl | hnil
    · exact hvq
    · simp at hnil
  have hlets : ∀ c ∈ [GGT.RelLetter.comp nu vs], D.IsLetter c := by
    intro c hc
    rw [List.mem_cons] at hc
    rcases hc with rfl | hnil
    · exact hvs
    · simp at hnil
  have hlet : ∀ c ∈ px ++ [GGT.RelLetter.comp nu vq] ++ rx ++
      GGT.OsinComponents.revWord [GGT.RelLetter.comp nu vs], D.IsLetter c := by
    intro c hc
    rcases List.mem_append.mp hc with hc1 | hc2
    · rcases List.mem_append.mp hc1 with hc3 | hc4
      · rcases List.mem_append.mp hc3 with hc5 | hc6
        · exact hpxlet c hc5
        · exact hletq c hc6
      · exact hrxlet c hc4
    · exact GGT.OsinComponents.isLetter_of_mem_revWord D hsymm hlets c hc2
  -- a one-letter side is a component by itself
  have hcompq : GGT.OsinComponents.IsComp nu [GGT.RelLetter.comp nu vq] 0 1 := by
    refine ⟨Nat.zero_lt_one, by omega, ?_, ?_, ?_⟩
    · intro n _ hn2 hnv
      have hn0 : n = 0 := by omega
      subst hn0
      exact isCompOf_of_getElem? (b := nu) (x := vq) hnv List.getElem?_cons_zero
    · intro n hn hnv
      exact absurd hn (by omega)
    · intro hk
      exact absurd hk (by omega)
  have hcomps : GGT.OsinComponents.IsComp nu [GGT.RelLetter.comp nu vs] 0 1 := by
    refine ⟨Nat.zero_lt_one, by omega, ?_, ?_, ?_⟩
    · intro n _ hn2 hnv
      have hn0 : n = 0 := by omega
      subst hn0
      exact isCompOf_of_getElem? (b := nu) (x := vs) hnv List.getElem?_cons_zero
    · intro n hn hnv
      exact absurd hn (by omega)
    · intro hk
      exact absurd hk (by omega)
  -- the innermost clause: its range is the base-spelled third side
  have hinner : ∀ t : ℕ, px.length + 0 < t →
      t < px.length + 1 + rx.length + (1 - 1) →
      GGT.OsinComponents.IsCompStart nu
          (px ++ [GGT.RelLetter.comp nu vq] ++ rx ++
            GGT.OsinComponents.revWord [GGT.RelLetter.comp nu vs]) t →
      ¬ GGT.OsinComponents.Connected D.fam nu 1
          (px ++ [GGT.RelLetter.comp nu vq] ++ rx ++
            GGT.OsinComponents.revWord [GGT.RelLetter.comp nu vs])
          (px.length + 0) t := by
    intro t ht1 ht2 hstart
    exact absurd hstart
      (GGT.OsinComponents.not_isCompStart_fourGon_r px
        [GGT.RelLetter.comp nu vq] rx [GGT.RelLetter.comp nu vs] nu hrx
        (by omega) (by omega))
  -- the other arc: an empty range, and the base-spelled first side
  have hother : ∀ o : ℕ,
      (px.length + 1 + rx.length + (1 - 1) < o ∧
          o < (px ++ [GGT.RelLetter.comp nu vq] ++ rx ++
            GGT.OsinComponents.revWord [GGT.RelLetter.comp nu vs]).length)
        ∨ o < px.length + 0 →
      GGT.OsinComponents.IsCompStart nu
          (px ++ [GGT.RelLetter.comp nu vq] ++ rx ++
            GGT.OsinComponents.revWord [GGT.RelLetter.comp nu vs]) o →
      ¬ GGT.OsinComponents.Connected D.fam nu 1
          (px ++ [GGT.RelLetter.comp nu vq] ++ rx ++
            GGT.OsinComponents.revWord [GGT.RelLetter.comp nu vs])
          (px.length + 1 + rx.length + (1 - 1)) o := by
    intro o ho hstart
    rcases ho with ⟨hb1, hb2⟩ | hb3
    · exfalso
      rw [GGT.OsinComponents.length_fourGon] at hb2
      omega
    · exact absurd hstart
        (GGT.OsinComponents.not_isCompStart_fourGon_p px
          [GGT.RelLetter.comp nu vq] rx [GGT.RelLetter.comp nu vs] nu hpx
          (by omega))
  obtain ⟨h1, h2⟩ := hC nu px [GGT.RelLetter.comp nu vq] rx
    [GGT.RelLetter.comp nu vs] 0 1 0 1 hclose' hlet hpx hrx hp0 hqg hcompq
    (Or.inr hr0) hcomps (Or.inr hr0) hconn hinner hother
  -- the two gaps, read off
  have hv1 : GGT.OsinComponents.vertex (1 : G) [GGT.RelLetter.comp nu vq] 1
      = vq := by
    have h := span_eq_val_of_getElem? (v := (1 : G))
      (l := [GGT.RelLetter.comp nu vq]) (i := 0)
      (c := GGT.RelLetter.comp nu vq) List.getElem?_cons_zero
    rw [GGT.OsinComponents.vertex_zero, inv_one, one_mul] at h
    exact h
  have hv2 : GGT.OsinComponents.vertex (1 : G) [GGT.RelLetter.comp nu vs] 1
      = vs := by
    have h := span_eq_val_of_getElem? (v := (1 : G))
      (l := [GGT.RelLetter.comp nu vs]) (i := 0)
      (c := GGT.RelLetter.comp nu vs) List.getElem?_cons_zero
    rw [GGT.OsinComponents.vertex_zero, inv_one, one_mul] at h
    exact h
  have e1 : (GGT.OsinComponents.vertex (1 : G)
        [GGT.RelLetter.comp nu vs] 0)⁻¹ *
      (GGT.RelLetter.listVal px *
        GGT.OsinComponents.vertex (1 : G) [GGT.RelLetter.comp nu vq] 0)
      = GGT.RelLetter.listVal px := by
    rw [GGT.OsinComponents.vertex_zero, GGT.OsinComponents.vertex_zero,
      inv_one, mul_one, one_mul]
  have e2 : (GGT.RelLetter.listVal px *
        GGT.OsinComponents.vertex (1 : G) [GGT.RelLetter.comp nu vq] 1)⁻¹ *
      GGT.OsinComponents.vertex (1 : G) [GGT.RelLetter.comp nu vs] 1
      = GGT.RelLetter.listVal rx := by
    rw [hv1, hv2, hclose]
    group
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1, h2⟩

end Quad

section Cases

variable {G : Type u} [Group G]

/-- **The aligned case, from the polygon's output.**

Both members rotations of the relator.  The design makes the two connectors
trivial, the vertex relation loses its right factor, and the join gives the
identity `RelWord.IsPiece` excludes, with `y` the quadrilateral's own first
side. -/
theorem listVal_conj_of_alignedMatch_quad {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdiag : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * a t ^ i * x' ≠ a t ^ i)
    {p : List G} {c c' i j : ℕ}
    (hi : i < (relatorWord₂ p (a false) (a true) ms).length)
    (hj : j < (relatorWord₂ p (a false) (a true) ms).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms)
    {px rx : List (GGT.RelLetter G Bool)} {y : G}
    (hxb : GGT.RelLetter.listVal px ∈ D.relBall b eps)
    (hrb : GGT.RelLetter.listVal rx ∈ D.relBall b eps)
    (hquad : a b ^ f
      = GGT.RelLetter.listVal px * a b ^ e * GGT.RelLetter.listVal rx)
    (hlet : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)))
    (hlet' : ((relatorWord₂ p (a false) (a true) ms).rotate c')[j]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ f)))
    (hvert : y * GGT.OsinComponents.vertex (1 : G)
          ((relatorWord₂ p (a false) (a true) ms).rotate c) i
        = GGT.OsinComponents.vertex (1 : G)
            ((relatorWord₂ p (a false) (a true) ms).rotate c') j *
          GGT.RelLetter.listVal px) :
    GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c')
      = y * GGT.RelLetter.listVal
          ((relatorWord₂ p (a false) (a true) ms).rotate c) * y⁻¹ := by
  obtain ⟨hef, hx1, -⟩ :=
    trivial_connector_of_alignedMatch_ball hsep hdiag he hf hxb hrb hquad.symm
  rw [hx1, mul_one] at hvert
  have hinj' : ∀ t : Bool,
      Function.Injective (fun n : ℕ => (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  exact listVal_conj_of_alignedTrivial hinj' hnodup hi hj hef hlet hlet' hvert

/-- **The mirrored aligned case, from the polygon's output.**

Both members rotations of the formal inverse.  The letters carry inverses, so
the closing relation of the block quadrilateral does too, and the mirrored form
of the trivial-connector step is what applies. -/
theorem listVal_conj_of_mirroredAlignedMatch_quad {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdiag : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * a t ^ i * x' ≠ a t ^ i)
    {p : List G} {c c' i j : ℕ}
    (hi : i < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    (hj : j < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms)
    {px rx : List (GGT.RelLetter G Bool)} {y : G}
    (hxb : GGT.RelLetter.listVal px ∈ D.relBall b eps)
    (hrb : GGT.RelLetter.listVal rx ∈ D.relBall b eps)
    (hquad : (a b ^ f)⁻¹
      = GGT.RelLetter.listVal px * (a b ^ e)⁻¹ * GGT.RelLetter.listVal rx)
    (hlet : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[i]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ e)⁻¹)))
    (hlet' : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ f)⁻¹)))
    (hvert : y * GGT.OsinComponents.vertex (1 : G)
          ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c) i
        = GGT.OsinComponents.vertex (1 : G)
            ((RelWord.revInv
              (relatorWord₂ p (a false) (a true) ms)).rotate c') j *
          GGT.RelLetter.listVal px) :
    GGT.RelLetter.listVal
        ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')
      = y * GGT.RelLetter.listVal
          ((RelWord.revInv
            (relatorWord₂ p (a false) (a true) ms)).rotate c) * y⁻¹ := by
  obtain ⟨hef, hx1, -⟩ :=
    trivial_connector_of_mirroredAlignedMatch_ball hsymm hsep hdiag he hf hxb
      hrb hquad.symm
  rw [hx1, mul_one] at hvert
  have hinj' : ∀ t : Bool,
      Function.Injective (fun n : ℕ => (if t then a true else a false) ^ n) := by
    intro t
    rw [ite_apply_eq a t]
    exact hinj t
  refine listVal_conj_of_rotate_eq_of_vertex_eq ?_ ?_
    (rotate_eq_of_position_eq
      (RelWord.revInv (relatorWord₂ p (a false) (a true) ms))
      (position_eq_of_alignedMatch_revInv hinj' hnodup hi hj hef hlet hlet'))
    hvert
  · rw [List.length_rotate]
    omega
  · rw [List.length_rotate]
    omega

/-- **The first mixed order, from the polygon's output.**

One member a rotation of the relator, the other of its formal inverse.  Each of
the two matched pairs gives `x · a^e · x' = (a^f)⁻¹` outright, which is the
mirrored half of the separation clause, so both pairs have equal exponents and
the gap estimate closes the case. -/
theorem false_of_mixedMatch_quad {D : GGT.RelGenSet G Bool} {a : Bool → G}
    {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i₁ i₂ j₁ j₂ gapSlack : ℕ}
    (hi₂ : i₂ < (relatorWord₂ p (a false) (a true) ms).length)
    (hj₂ : j₂ < (relatorWord₂ p (a false) (a true) ms).length)
    (hii : i₁ < i₂) (hjj : j₁ < j₂)
    {b₁ b₂ : Bool} {e₁ f₁ e₂ f₂ : ℕ}
    (he₁ : e₁ ∈ ms) (hf₁ : f₁ ∈ ms) (he₂ : e₂ ∈ ms) (hf₂ : f₂ ∈ ms)
    {px₁ rx₁ px₂ rx₂ : List (GGT.RelLetter G Bool)}
    (hx₁ : GGT.RelLetter.listVal px₁ ∈ D.relBall b₁ eps)
    (hr₁ : GGT.RelLetter.listVal rx₁ ∈ D.relBall b₁ eps)
    (hx₂ : GGT.RelLetter.listVal px₂ ∈ D.relBall b₂ eps)
    (hr₂ : GGT.RelLetter.listVal rx₂ ∈ D.relBall b₂ eps)
    (hq₁ : (a b₁ ^ f₁)⁻¹
      = GGT.RelLetter.listVal px₁ * a b₁ ^ e₁ * GGT.RelLetter.listVal rx₁)
    (hq₂ : (a b₂ ^ f₂)⁻¹
      = GGT.RelLetter.listVal px₂ * a b₂ ^ e₂ * GGT.RelLetter.listVal rx₂)
    (hl₁ : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i₁]?
      = some (GGT.RelLetter.comp b₁ ((if b₁ then a true else a false) ^ e₁)))
    (hm₁ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j₁]?
      = some (GGT.RelLetter.comp b₁
          (((if b₁ then a true else a false) ^ f₁)⁻¹)))
    (hl₂ : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i₂]?
      = some (GGT.RelLetter.comp b₂ ((if b₂ then a true else a false) ^ e₂)))
    (hm₂ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j₂]?
      = some (GGT.RelLetter.comp b₂
          (((if b₂ then a true else a false) ^ f₂)⁻¹)))
    (hgap : j₂ - j₁ ≤ i₂ - i₁ + gapSlack)
    (hsmall : 2 * (i₂ - i₁) + gapSlack
      < (relatorWord₂ p (a false) (a true) ms).length) : False :=
  false_of_span_mixed hnodup hinj hsep hi₂ hj₂ hii hjj he₁ hf₁ he₂ hf₂
    hx₁ hr₁ hx₂ hr₂ hl₁ hm₁ hl₂ hm₂ hq₁.symm hq₂.symm hgap hsmall

/-- **The second mixed order, from the polygon's output.**

The members exchanged: now the member carrying the direct powers is the second
one.  The closing relation of each block quadrilateral runs the other way, and
inverting it puts it back in the shape the separation clause reads, the two
connectors staying in the ball because relative balls are closed under
inversion. -/
theorem false_of_mixedMatch_quad_inv {D : GGT.RelGenSet G Bool} {a : Bool → G}
    {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i₁ i₂ j₁ j₂ gapSlack : ℕ}
    (hi₂ : i₂ < (relatorWord₂ p (a false) (a true) ms).length)
    (hj₂ : j₂ < (relatorWord₂ p (a false) (a true) ms).length)
    (hii : i₁ < i₂) (hjj : j₁ < j₂)
    {b₁ b₂ : Bool} {e₁ f₁ e₂ f₂ : ℕ}
    (he₁ : e₁ ∈ ms) (hf₁ : f₁ ∈ ms) (he₂ : e₂ ∈ ms) (hf₂ : f₂ ∈ ms)
    {px₁ rx₁ px₂ rx₂ : List (GGT.RelLetter G Bool)}
    (hx₁ : GGT.RelLetter.listVal px₁ ∈ D.relBall b₁ eps)
    (hr₁ : GGT.RelLetter.listVal rx₁ ∈ D.relBall b₁ eps)
    (hx₂ : GGT.RelLetter.listVal px₂ ∈ D.relBall b₂ eps)
    (hr₂ : GGT.RelLetter.listVal rx₂ ∈ D.relBall b₂ eps)
    (hq₁ : a b₁ ^ e₁
      = GGT.RelLetter.listVal px₁ * (a b₁ ^ f₁)⁻¹ * GGT.RelLetter.listVal rx₁)
    (hq₂ : a b₂ ^ e₂
      = GGT.RelLetter.listVal px₂ * (a b₂ ^ f₂)⁻¹ * GGT.RelLetter.listVal rx₂)
    (hl₁ : ((relatorWord₂ p (a false) (a true) ms).rotate c')[i₁]?
      = some (GGT.RelLetter.comp b₁ ((if b₁ then a true else a false) ^ e₁)))
    (hm₁ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[j₁]?
      = some (GGT.RelLetter.comp b₁
          (((if b₁ then a true else a false) ^ f₁)⁻¹)))
    (hl₂ : ((relatorWord₂ p (a false) (a true) ms).rotate c')[i₂]?
      = some (GGT.RelLetter.comp b₂ ((if b₂ then a true else a false) ^ e₂)))
    (hm₂ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[j₂]?
      = some (GGT.RelLetter.comp b₂
          (((if b₂ then a true else a false) ^ f₂)⁻¹)))
    (hgap : j₂ - j₁ ≤ i₂ - i₁ + gapSlack)
    (hsmall : 2 * (i₂ - i₁) + gapSlack
      < (relatorWord₂ p (a false) (a true) ms).length) : False := by
  have hc₁ : (GGT.RelLetter.listVal px₁)⁻¹ * a b₁ ^ e₁ *
      (GGT.RelLetter.listVal rx₁)⁻¹ = (a b₁ ^ f₁)⁻¹ := by
    rw [hq₁]
    group
  have hc₂ : (GGT.RelLetter.listVal px₂)⁻¹ * a b₂ ^ e₂ *
      (GGT.RelLetter.listVal rx₂)⁻¹ = (a b₂ ^ f₂)⁻¹ := by
    rw [hq₂]
    group
  exact false_of_span_mixed hnodup hinj hsep hi₂ hj₂ hii hjj he₁ hf₁ he₂ hf₂
    (inv_mem_relBall hsymm hx₁) (inv_mem_relBall hsymm hr₁)
    (inv_mem_relBall hsymm hx₂) (inv_mem_relBall hsymm hr₂)
    hl₁ hm₁ hl₂ hm₂ hc₁ hc₂ hgap hsmall

end Cases

end HullSC
end GroupApproximation
