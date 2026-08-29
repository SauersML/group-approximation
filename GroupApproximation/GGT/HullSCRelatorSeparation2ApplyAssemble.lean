import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyPin
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyClose
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyRotate

/-!
# The aligned cases, assembled

Everything between a named connector and the identity `RelWord.IsPiece` excludes,
in one step each.  The connector `GGT.OsinComponents.exists_other_component_of_deep_six`
returns is a connectedness statement in disguise --- `connected_of_connector` is
that observation --- and `GGT.OsinComponents.exists_eps_matchedPair` turns
connectedness at the pair into the two gaps by name.  From there
`HullSC.listVal_conj_of_alignedMatch_pair` is the whole aligned branch.

So the two theorems here are short, and what they carry is the interface: the
polygon's output at a given radius, taken as a hypothesis so that the design can
be run at that radius; the two matched prefixes with their split; the two block
letters; the connector; the two same-side exclusions.  Nothing else is left
between the geometry and the conclusion.

The mixed cases do not go through here.  They consume the connector relation and
never the vertex relation, and they need TWO matches with an order between them
--- `GGT.OsinComponents.lt_of_two_connectors_qg` --- which the aligned cases do
not.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A named connector is connectedness at the matched pair.**

The converse of `mem_fam_of_connected_cross`: the short first side translates
the `q`-vertex, the closing relation turns the four-gon's reversed-block vertex
back into a vertex of `s`, and what is left is the connector itself. -/
theorem connected_of_connector (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ))
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    {i : ℕ} (hi : i ≤ q.length) (m : ℕ) {h : G} (hh : h ∈ D.fam lam)
    (heq : RelLetter.listVal p * vertex (1 : G) q i * h = vertex (1 : G) s m) :
    Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
      (p.length + q.length + r.length + (s.length - m)) := by
  show (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + i))⁻¹ *
    vertex (1 : G) (p ++ q ++ r ++ revWord s)
      (p.length + q.length + r.length + (s.length - m)) ∈ D.fam lam
  rw [vertex_fourGon_side p q r s 1 hi, one_mul,
    vertex_fourGon_opposite_closed p q r s hclose m, ← heq]
  have hid : (RelLetter.listVal p * vertex (1 : G) q i)⁻¹ *
      (RelLetter.listVal p * vertex (1 : G) q i * h) = h := by
    group
  rw [hid]
  exact hh

end OsinComponents
end GGT

namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Assemble

variable {G : Type u} [Group G]

/-- **The aligned case, from the connector.**

Both members rotations of the relator.  The polygon's output is taken at a fixed
radius so that the design's clauses can be stated at the same one. -/
theorem listVal_conj_of_alignedMatch_assembled {D : GGT.RelGenSet G Bool}
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
    {p : List G} {c c' i j : ℕ}
    (hiR : i < (relatorWord₂ p (a false) (a true) ms).length)
    (hjR : j < (relatorWord₂ p (a false) (a true) ms).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
    (hw' : (relatorWord₂ p (a false) (a true) ms).rotate c' = u' ++ tl')
    (hiu : i + 1 ≤ u.length) (hju : j + 1 ≤ u'.length)
    (hpy : ∀ x ∈ py, ∃ g : G, x = GGT.RelLetter.base g)
    (hpz : ∀ x ∈ pz, ∃ g : G, x = GGT.RelLetter.base g)
    (hpy0 : 0 < py.length) (hpz0 : 0 < pz.length)
    (hlet4 : ∀ x ∈ py ++ u ++ pz ++ GGT.OsinComponents.revWord u',
      D.IsLetter x)
    (hclose : GGT.RelLetter.listVal u' = GGT.RelLetter.listVal py *
      GGT.RelLetter.listVal u * GGT.RelLetter.listVal pz)
    (hqg : ∀ t : ℕ, t < 4 → ∀ x y : ℕ,
      GGT.OsinComponents.fourGonCut py u pz u' t ≤ x → x ≤ y →
      y ≤ GGT.OsinComponents.fourGonCut py u pz u' (t + 1) →
      ((y - x : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') x)
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') y) : ℕ) : ℝ))
    (hcompu : GGT.OsinComponents.IsComp b u i (i + 1))
    (hcompu' : GGT.OsinComponents.IsComp b u' j (j + 1))
    {h : G} (hh : h ∈ D.fam b)
    (hconn : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u i * h
      = GGT.OsinComponents.vertex (1 : G) u' (j + 1))
    (hqside : ∀ i' : ℕ, i' ≤ u.length → i' ≠ i →
      (GGT.OsinComponents.vertex (1 : G) u i)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam b)
    (hsside : ∀ m : ℕ, m ≤ u'.length → m ≠ j + 1 →
      (GGT.OsinComponents.vertex (1 : G) u' (j + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b)
    (hletu : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)))
    (hletu' : ((relatorWord₂ p (a false) (a true) ms).rotate c')[j]?
      = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ f))) :
    GGT.RelLetter.listVal ((relatorWord₂ p (a false) (a true) ms).rotate c')
      = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal
          ((relatorWord₂ p (a false) (a true) ms).rotate c) *
        (GGT.RelLetter.listVal py)⁻¹ := by
  have hConn := GGT.OsinComponents.connected_of_connector D b py u pz u' hclose
    (by omega : i ≤ u.length) (j + 1) hh hconn
  obtain ⟨hxb, hx'b⟩ := hpair b py u pz u' i j hclose hlet4 hpy hpz hpy0 hqg
    hcompu (Or.inr hpz0) hcompu' (Or.inr hpz0) hConn hqside hsside
  exact listVal_conj_of_alignedMatch_pair hnodup hinj hsep hdiag hiR hjR he hf
    hw hw' hiu hju hxb hx'b hletu hletu'

end Assemble

end HullSC
end GroupApproximation
