import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyDispatch
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyExp

/-!
# From a deep block to a closed case

Two steps, and after them each case of Olshanskii's step (c) is an application.

`exists_deep_match` is the shared one, and it mentions no relator: a deep
component of the long side is not isolated, so it is connected to another
component of the quadrilateral; the same-side branch is what the design
excludes, and what is left is a match across, at a POSITIVE index, with its
connector named.  Because it is stated over an arbitrary quadrilateral it serves
the direct and the mirrored side alike --- the two differ only in which rotation
the caller instantiates the long sides from, which is a fact about the caller
and not about this step.

The constant is taken as a maximum over the two indices, and that costs nothing:
`GGT.OsinComponents.exists_other_component_of_deep_six` binds the index before
its constant, so there are two, but the constant enters only through the
hypothesis `C · 4 ≤ rho`, which a larger constant only strengthens.  No
ball-monotonicity step is needed.

`listVal_conj_of_alignedMatch_found` is the second: it reads the matched letter.
The block letter the chain chose came with its exponent; the matched one arrives
as `comp b x` and `HullSC.exponent_of_comp_rotate` puts it in the design's
shape, after which `HullSC.listVal_conj_of_alignedMatch_assembled` closes the
case.  The index bookkeeping is the one place care is needed: the match is
returned at `j`, and the component of the far side is `[j - 1, j)`, so what the
closer sees is `j - 1` with `j - 1 + 1 = j` spent on the connector.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u

section Match

variable {G : Type u} [Group G]

/-- **A deep component of the long side is matched across, at a positive
index.** -/
theorem exists_deep_match (D : RelGenSet G Bool)
    (hbound : ∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Bool)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Bool) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    {mu bb : ℝ} (hmu : 1 ≤ mu) (hbb : 0 ≤ bb) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (lam : Bool) (rho : ℕ) (p q r s : List (RelLetter G Bool)) (i : ℕ),
        C * 4 ≤ rho →
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q
            * RelLetter.listVal r →
        (∀ x ∈ p, ∃ g : G, x = RelLetter.base g) →
        (∀ x ∈ r, ∃ g : G, x = RelLetter.base g) →
        0 < r.length →
        IsQuasiGeodesicPolygon D mu bb 4 1 (p ++ q ++ r ++ revWord s) →
        IsComp lam q i (i + 1) →
        (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q (i + 1)
          ∉ D.relBall lam rho →
        (∀ i' : ℕ, i' ≤ q.length → i' ≠ i →
          (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q i' ∉ D.fam lam) →
        ∃ j : ℕ, 0 < j ∧ j ≤ s.length ∧
          (∃ x : G, s[j - 1]? = some (RelLetter.comp lam x)) ∧
          ∃ h : G, h ∈ D.fam lam ∧
            RelLetter.listVal p * vertex (1 : G) q i * h
              = vertex (1 : G) s j := by
  obtain ⟨C₀, h₀, hC₀⟩ :=
    exists_other_component_of_deep_six D hbound false hmu hbb
  obtain ⟨C₁, h₁, hC₁⟩ :=
    exists_other_component_of_deep_six D hbound true hmu hbb
  refine ⟨max C₀ C₁, lt_of_lt_of_le h₀ (Nat.le_max_left C₀ C₁), ?_⟩
  intro lam rho p q r s i hrho hclose hp hr hr0 hpoly hcomp hdeep hqside
  have hrho₀ : C₀ * 4 ≤ rho :=
    le_trans (Nat.mul_le_mul (Nat.le_max_left C₀ C₁) (le_refl 4)) hrho
  have hrho₁ : C₁ * 4 ≤ rho :=
    le_trans (Nat.mul_le_mul (Nat.le_max_right C₀ C₁) (le_refl 4)) hrho
  have hdisj : (∃ i' : ℕ, i' ≤ q.length ∧ i' ≠ i ∧
        IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') ∧
        ∃ h : G, h ∈ D.fam lam ∧
          vertex (1 : G) q i * h = vertex (1 : G) q i')
      ∨ (∃ j : ℕ, j ≤ s.length ∧
        IsCompStart lam (p ++ q ++ r ++ revWord s)
          (p.length + q.length + r.length + (s.length - j)) ∧
        ∃ h : G, h ∈ D.fam lam ∧
          RelLetter.listVal p * vertex (1 : G) q i * h
            = vertex (1 : G) s j) := by
    cases lam with
    | false =>
        exact hC₀ 4 rho (by omega) p q r s hclose hp hr hpoly i (i + 1) hcomp
          (Or.inr hr0) hrho₀ hdeep
    | true =>
        exact hC₁ 4 rho (by omega) p q r s hclose hp hr hpoly i (i + 1) hcomp
          (Or.inr hr0) hrho₁ hdeep
  obtain ⟨j, hj0, hj, hstart, hconn⟩ :=
    cross_of_notSameSide D lam p q r s hqside hdisj
  exact ⟨j, hj0, hj,
    exists_comp_of_isCompStart_rev p q r s lam hj0 hj hstart, hconn⟩

end Match

end OsinComponents
end GGT

namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Found

variable {G : Type u} [Group G]

/-- **The aligned case, from a match that has been found.**

The matched letter is read into the design's shape and its component recovered,
after which the assembled closer applies.  `j - 1 + 1 = j` is where the index
convention of the reversed side is spent: the match is returned at `j` and the
component of the far side is `[j - 1, j)`. -/
theorem listVal_conj_of_alignedMatch_found {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdiag : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * a t ^ i * x' ≠ a t ^ i)
    (hpair : ∀ (lam : Bool) (P Q R S : List (GGT.RelLetter G Bool)) (i j : ℕ),
      GGT.RelLetter.listVal S = GGT.RelLetter.listVal P *
          GGT.RelLetter.listVal Q * GGT.RelLetter.listVal R →
      (∀ x ∈ P ++ Q ++ R ++ GGT.OsinComponents.revWord S, D.IsLetter x) →
      (∀ x ∈ P, ∃ g : G, x = GGT.RelLetter.base g) →
      (∀ x ∈ R, ∃ g : G, x = GGT.RelLetter.base g) →
      0 < P.length →
      (∀ t : ℕ, t < 4 → ∀ x y : ℕ,
        GGT.OsinComponents.fourGonCut P Q R S t ≤ x → x ≤ y →
        y ≤ GGT.OsinComponents.fourGonCut P Q R S (t + 1) →
        ((y - x : ℕ) : ℝ) / 1 - 0
          ≤ ((wordDist D.alphabet.carrier
              (GGT.OsinComponents.vertex (1 : G)
                (P ++ Q ++ R ++ GGT.OsinComponents.revWord S) x)
              (GGT.OsinComponents.vertex (1 : G)
                (P ++ Q ++ R ++ GGT.OsinComponents.revWord S) y) : ℕ) : ℝ)) →
      GGT.OsinComponents.IsComp lam Q i (i + 1) →
      (i + 1 < Q.length ∨ 0 < R.length) →
      GGT.OsinComponents.IsComp lam S j (j + 1) →
      (j + 1 < S.length ∨ 0 < R.length) →
      GGT.OsinComponents.Connected D.fam lam 1
          (P ++ Q ++ R ++ GGT.OsinComponents.revWord S) (P.length + i)
          (P.length + Q.length + R.length + (S.length - (j + 1))) →
      (∀ i' : ℕ, i' ≤ Q.length → i' ≠ i →
        (GGT.OsinComponents.vertex (1 : G) Q i)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) Q i' ∉ D.fam lam) →
      (∀ m : ℕ, m ≤ S.length → m ≠ j + 1 →
        (GGT.OsinComponents.vertex (1 : G) S (j + 1))⁻¹ *
          GGT.OsinComponents.vertex (1 : G) S m ∉ D.fam lam) →
      ((GGT.OsinComponents.vertex (1 : G) S j)⁻¹ *
          (GGT.RelLetter.listVal P * GGT.OsinComponents.vertex (1 : G) Q i)
          ∈ D.relBall lam eps) ∧
        ((GGT.RelLetter.listVal P *
            GGT.OsinComponents.vertex (1 : G) Q (i + 1))⁻¹ *
          GGT.OsinComponents.vertex (1 : G) S (j + 1) ∈ D.relBall lam eps))
    {p : List G} {c c' d j : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
    (hw' : (relatorWord₂ p (a false) (a true) ms).rotate c' = u' ++ tl')
    (hd : d < u.length) (hj0 : 0 < j) (hj : j ≤ u'.length)
    {b : Bool} {e : ℕ} (he : e ∈ ms)
    (hletd : ((relatorWord₂ p (a false) (a true) ms).rotate c)[d]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)))
    {x : G} (hx : u'[j - 1]? = some (GGT.RelLetter.comp b x))
    {h : G} (hh : h ∈ D.fam b)
    (hconn : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u d * h
      = GGT.OsinComponents.vertex (1 : G) u' j)
    (hpy : ∀ z ∈ py, ∃ g : G, z = GGT.RelLetter.base g)
    (hpz : ∀ z ∈ pz, ∃ g : G, z = GGT.RelLetter.base g)
    (hpy0 : 0 < py.length) (hpz0 : 0 < pz.length)
    (hlet4 : ∀ z ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      D.IsLetter z)
    (hclose : GGT.RelLetter.listVal u' = GGT.RelLetter.listVal py *
      GGT.RelLetter.listVal u * GGT.RelLetter.listVal pz)
    (hqg : ∀ t : ℕ, t < 4 → ∀ z y : ℕ,
      GGT.OsinComponents.fourGonCut py u pz u' t ≤ z → z ≤ y →
      y ≤ GGT.OsinComponents.fourGonCut py u pz u' (t + 1) →
      ((y - z : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') z)
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') y) : ℕ) : ℝ))
    (hqside : ∀ i' : ℕ, i' ≤ u.length → i' ≠ d →
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam b)
    (hsside : ∀ m : ℕ, m ≤ u'.length → m ≠ j →
      (GGT.OsinComponents.vertex (1 : G) u' j)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b) :
    GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c')
      = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal
          ((relatorWord₂ p (a false) (a true) ms).rotate c) *
        (GGT.RelLetter.listVal py)⁻¹ := by
  have hjj : j - 1 + 1 = j := by omega
  have hulen : u.length ≤ (relatorWord₂ p (a false) (a true) ms).length := by
    have hL := congrArg List.length hw
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hu'len : u'.length ≤ (relatorWord₂ p (a false) (a true) ms).length := by
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hxR : ((relatorWord₂ p (a false) (a true) ms).rotate c')[j - 1]?
      = some (GGT.RelLetter.comp b x) := by
    rw [hw']
    exact (List.getElem?_append_left (by omega : j - 1 < u'.length)).trans hx
  obtain ⟨f, hf, hxf⟩ := exponent_of_comp_rotate hxR
  have hletj : ((relatorWord₂ p (a false) (a true) ms).rotate c')[j - 1]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ f)) := by
    rw [hxR, hxf]
  have hcompu : GGT.OsinComponents.IsComp b u d (d + 1) :=
    isComp_prefix_rotate_relatorWord₂ hp0 hw hd hletd
  have hcompu' : GGT.OsinComponents.IsComp b u' (j - 1) (j - 1 + 1) :=
    isComp_prefix_rotate_relatorWord₂ hp0 hw' (by omega) hletj
  have hconn' : GGT.RelLetter.listVal py *
      GGT.OsinComponents.vertex (1 : G) u d * h
      = GGT.OsinComponents.vertex (1 : G) u' (j - 1 + 1) := by
    rw [hjj]
    exact hconn
  have hsside' : ∀ m : ℕ, m ≤ u'.length → m ≠ j - 1 + 1 →
      (GGT.OsinComponents.vertex (1 : G) u' (j - 1 + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b := by
    rw [hjj]
    exact hsside
  exact listVal_conj_of_alignedMatch_assembled hnodup hinj hsep hdiag hpair
    (by omega : d < (relatorWord₂ p (a false) (a true) ms).length)
    (by omega : j - 1 < (relatorWord₂ p (a false) (a true) ms).length)
    he hf hw hw' (by omega) (by omega) hpy hpz hpy0 hpz0 hlet4 hclose hqg
    hcompu hcompu' hh hconn' hqside hsside' hletd hletj

/-- **The mirrored aligned case, from a match that has been found.**

`listVal_conj_of_alignedMatch_found` with both members rotations of the formal
inverse; the matched letter is read by `HullSC.exponent_of_comp_rotate_revInv`,
which returns it as the inverse of a power, and the mirrored closer applies. -/
theorem listVal_conj_of_mirroredAlignedMatch_found {D : GGT.RelGenSet G Bool}
    {a : Bool → G} {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hdiag : ∀ i ∈ ms, ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps, x ≠ 1 → x * a t ^ i * x' ≠ a t ^ i)
    (hpair : ∀ (lam : Bool) (P Q R S : List (GGT.RelLetter G Bool)) (i j : ℕ),
      GGT.RelLetter.listVal S = GGT.RelLetter.listVal P *
          GGT.RelLetter.listVal Q * GGT.RelLetter.listVal R →
      (∀ x ∈ P ++ Q ++ R ++ GGT.OsinComponents.revWord S, D.IsLetter x) →
      (∀ x ∈ P, ∃ g : G, x = GGT.RelLetter.base g) →
      (∀ x ∈ R, ∃ g : G, x = GGT.RelLetter.base g) →
      0 < P.length →
      (∀ t : ℕ, t < 4 → ∀ x y : ℕ,
        GGT.OsinComponents.fourGonCut P Q R S t ≤ x → x ≤ y →
        y ≤ GGT.OsinComponents.fourGonCut P Q R S (t + 1) →
        ((y - x : ℕ) : ℝ) / 1 - 0
          ≤ ((wordDist D.alphabet.carrier
              (GGT.OsinComponents.vertex (1 : G)
                (P ++ Q ++ R ++ GGT.OsinComponents.revWord S) x)
              (GGT.OsinComponents.vertex (1 : G)
                (P ++ Q ++ R ++ GGT.OsinComponents.revWord S) y) : ℕ) : ℝ)) →
      GGT.OsinComponents.IsComp lam Q i (i + 1) →
      (i + 1 < Q.length ∨ 0 < R.length) →
      GGT.OsinComponents.IsComp lam S j (j + 1) →
      (j + 1 < S.length ∨ 0 < R.length) →
      GGT.OsinComponents.Connected D.fam lam 1
          (P ++ Q ++ R ++ GGT.OsinComponents.revWord S) (P.length + i)
          (P.length + Q.length + R.length + (S.length - (j + 1))) →
      (∀ i' : ℕ, i' ≤ Q.length → i' ≠ i →
        (GGT.OsinComponents.vertex (1 : G) Q i)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) Q i' ∉ D.fam lam) →
      (∀ m : ℕ, m ≤ S.length → m ≠ j + 1 →
        (GGT.OsinComponents.vertex (1 : G) S (j + 1))⁻¹ *
          GGT.OsinComponents.vertex (1 : G) S m ∉ D.fam lam) →
      ((GGT.OsinComponents.vertex (1 : G) S j)⁻¹ *
          (GGT.RelLetter.listVal P * GGT.OsinComponents.vertex (1 : G) Q i)
          ∈ D.relBall lam eps) ∧
        ((GGT.RelLetter.listVal P *
            GGT.OsinComponents.vertex (1 : G) Q (i + 1))⁻¹ *
          GGT.OsinComponents.vertex (1 : G) S (j + 1) ∈ D.relBall lam eps))
    {p : List G} {c c' d j : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c
      = u ++ tl)
    (hw' : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c'
      = u' ++ tl')
    (hd : d < u.length) (hj0 : 0 < j) (hj : j ≤ u'.length)
    {b : Bool} {e : ℕ} (he : e ∈ ms)
    (hletd : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[d]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ e)⁻¹)))
    {x : G} (hx : u'[j - 1]? = some (GGT.RelLetter.comp b x))
    {h : G} (hh : h ∈ D.fam b)
    (hconn : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u d * h
      = GGT.OsinComponents.vertex (1 : G) u' j)
    (hpy : ∀ z ∈ py, ∃ g : G, z = GGT.RelLetter.base g)
    (hpz : ∀ z ∈ pz, ∃ g : G, z = GGT.RelLetter.base g)
    (hpy0 : 0 < py.length) (hpz0 : 0 < pz.length)
    (hlet4 : ∀ z ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      D.IsLetter z)
    (hclose : GGT.RelLetter.listVal u' = GGT.RelLetter.listVal py *
      GGT.RelLetter.listVal u * GGT.RelLetter.listVal pz)
    (hqg : ∀ t : ℕ, t < 4 → ∀ z y : ℕ,
      GGT.OsinComponents.fourGonCut py u pz u' t ≤ z → z ≤ y →
      y ≤ GGT.OsinComponents.fourGonCut py u pz u' (t + 1) →
      ((y - z : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') z)
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') y) : ℕ) : ℝ))
    (hqside : ∀ i' : ℕ, i' ≤ u.length → i' ≠ d →
      (GGT.OsinComponents.vertex (1 : G) u d)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam b)
    (hsside : ∀ m : ℕ, m ≤ u'.length → m ≠ j →
      (GGT.OsinComponents.vertex (1 : G) u' j)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b) :
    GGT.RelLetter.listVal
        ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')
      = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal
          ((RelWord.revInv
            (relatorWord₂ p (a false) (a true) ms)).rotate c) *
        (GGT.RelLetter.listVal py)⁻¹ := by
  have hjj : j - 1 + 1 = j := by omega
  have hulen : u.length
      ≤ (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length := by
    have hL := congrArg List.length hw
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hu'len : u'.length
      ≤ (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length := by
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hxR : ((RelWord.revInv
      (relatorWord₂ p (a false) (a true) ms)).rotate c')[j - 1]?
      = some (GGT.RelLetter.comp b x) := by
    rw [hw']
    exact (List.getElem?_append_left (by omega : j - 1 < u'.length)).trans hx
  obtain ⟨f, hf, hxf⟩ := exponent_of_comp_rotate_revInv hxR
  have hletj : ((RelWord.revInv
      (relatorWord₂ p (a false) (a true) ms)).rotate c')[j - 1]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ f)⁻¹)) := by
    rw [hxR, hxf]
  have hcompu : GGT.OsinComponents.IsComp b u d (d + 1) :=
    isComp_prefix_rotate_revInv_relatorWord₂ hp0 hw hd hletd
  have hcompu' : GGT.OsinComponents.IsComp b u' (j - 1) (j - 1 + 1) :=
    isComp_prefix_rotate_revInv_relatorWord₂ hp0 hw' (by omega) hletj
  have hconn' : GGT.RelLetter.listVal py *
      GGT.OsinComponents.vertex (1 : G) u d * h
      = GGT.OsinComponents.vertex (1 : G) u' (j - 1 + 1) := by
    rw [hjj]
    exact hconn
  have hsside' : ∀ m : ℕ, m ≤ u'.length → m ≠ j - 1 + 1 →
      (GGT.OsinComponents.vertex (1 : G) u' (j - 1 + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b := by
    rw [hjj]
    exact hsside
  exact listVal_conj_of_mirroredAlignedMatch_assembled hnodup hinj hsymm hsep
    hdiag hpair
    (by omega : d
      < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    (by omega : j - 1
      < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    he hf hw hw' (by omega) (by omega) hpy hpz hpy0 hpz0 hlet4 hclose hqg
    hcompu hcompu' hh hconn' hqside hsside' hletd hletj

end Found

end HullSC
end GroupApproximation
