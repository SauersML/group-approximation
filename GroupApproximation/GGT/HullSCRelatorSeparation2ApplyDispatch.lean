import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyIface
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyAssemble
import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyClose

/-!
# The dispatch's three remaining steps

`GGT.OsinComponents.exists_other_component_of_deep_six` returns a disjunction --
the deep component is matched on its own side, or across -- and the chain has to
kill the first branch and refine the second before the polygon can be run on it.
Both are here, together with the mirrored half of the aligned assembly.

* `cross_of_notSameSide` -- the same-side branch contradicts the design's
  exclusion, and the cross branch's index is positive: a component cannot start
  at the very end of the word, since a component's own end would then lie past
  it.  The positivity is what lets `exists_comp_of_isCompStart_rev` name the
  letter of `s` at `j - 1`.
* `gap_and_order_of_two_matches` -- the two things the mixed cases need of a
  pair of matches and cannot get from the matching itself: that they land in the
  same ORDER, which is the quasi-geodesic pinning, and that their GAP is
  controlled, which is the connector-pair estimate against the quasi-geodesic
  clause on the matched side.  Neither is available from `wordDist_match_le`
  alone -- it bounds the distance and says nothing about the sign.
* `listVal_conj_of_mirroredAlignedMatch_assembled` -- the mirrored half of
  `HullSC.listVal_conj_of_alignedMatch_assembled`, identical except that the
  letters carry inverses and the mirrored closer is the one that applies.

With these the four cases of step (c) are each a single call, and what is left
between them and Hull's §6 is the instantiation of the design.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

section Cross

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The match is across, not on the same side.**

The same-side branch of `exists_other_component_of_deep_six` says two distinct
components of `q` are connected, which the design's exclusion forbids; and the
cross branch's index is positive, because a component start at `|s| - 0` would
be a component start at the very end of the quadrilateral. -/
theorem cross_of_notSameSide (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ)) {i : ℕ}
    (hqside : ∀ i' : ℕ, i' ≤ q.length → i' ≠ i →
      IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') →
      (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q i' ∉ D.fam lam)
    (hdisj : (∃ i' : ℕ, i' ≤ q.length ∧ i' ≠ i ∧
        IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') ∧
        ∃ h : G, h ∈ D.fam lam ∧
          vertex (1 : G) q i * h = vertex (1 : G) q i')
      ∨ (∃ j : ℕ, j ≤ s.length ∧
        IsCompStart lam (p ++ q ++ r ++ revWord s)
          (p.length + q.length + r.length + (s.length - j)) ∧
        ∃ h : G, h ∈ D.fam lam ∧
          RelLetter.listVal p * vertex (1 : G) q i * h
            = vertex (1 : G) s j)) :
    ∃ j : ℕ, 0 < j ∧ j ≤ s.length ∧
      IsCompStart lam (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - j)) ∧
      ∃ h : G, h ∈ D.fam lam ∧
        RelLetter.listVal p * vertex (1 : G) q i * h
          = vertex (1 : G) s j := by
  rcases hdisj with ⟨i', hi', hne, hstart', h, hh, heq⟩ | ⟨j, hj, hstart, hconn⟩
  · refine absurd ?_ (hqside i' hi' hne hstart')
    rw [← heq, inv_mul_cancel_left]
    exact hh
  · refine ⟨j, ?_, hj, hstart, hconn⟩
    by_contra hj0
    have hjz : j = 0 := by omega
    subst hjz
    obtain ⟨k, hcomp⟩ := hstart
    have hlen : (p ++ q ++ r ++ revWord s).length
        = p.length + q.length + r.length + s.length := length_fourGon p q r s
    have h1 := hcomp.1
    have h2 := hcomp.2.1
    omega

/-- **A pair of matches lands in order, with a controlled gap.**

The two facts the mixed cases need and the matching does not give: the order,
from the quasi-geodesic pinning, and the gap, from the connector-pair estimate
against the quasi-geodesic clause on the matched side.  `wordDist_match_le`
alone bounds the distance between the two matches and says nothing about the
sign, which is why the pinning is needed as well. -/
theorem gap_and_order_of_two_matches (D : RelGenSet G Λ) {lam : Λ}
    {p q s : List (RelLetter G Λ)} {bb : ℝ} {Bn eps i₁ i₂ j₁ j₂ : ℕ}
    (hqlet : ∀ x ∈ q, D.IsLetter x) (hslet : ∀ x ∈ s, D.IsLetter x)
    (hqg : ∀ x y : ℕ, x ≤ y → y ≤ q.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) q x)
              (vertex (1 : G) q y) : ℕ) : ℝ))
    (hsg : ∀ x y : ℕ, x ≤ y → y ≤ s.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) s x)
              (vertex (1 : G) s y) : ℕ) : ℝ))
    (hB : bb ≤ (Bn : ℝ)) (hi₁ : i₁ ≤ q.length) (hi₂ : i₂ ≤ q.length)
    (hj₁ : j₁ ≤ s.length) (hj₂ : j₂ ≤ s.length)
    (hple : wordNorm D.alphabet.carrier (RelLetter.listVal p) ≤ eps)
    {h₁ h₂ : G} (hh₁ : h₁ ∈ D.fam lam) (hh₂ : h₂ ∈ D.fam lam)
    (he₁ : RelLetter.listVal p * vertex (1 : G) q i₁ * h₁
      = vertex (1 : G) s j₁)
    (he₂ : RelLetter.listVal p * vertex (1 : G) q i₂ * h₂
      = vertex (1 : G) s j₂)
    (hsep : i₁ + 2 * (eps + 1 + Bn) < i₂) :
    j₁ < j₂ ∧ j₂ - j₁ ≤ i₂ - i₁ + (Bn + 2) := by
  have horder : j₁ < j₂ :=
    lt_of_two_connectors_qg D hqlet hslet hqg hsg hB hi₁ hi₂ hj₁ hj₂ hple hh₁
      hh₂ he₁ he₂ hsep
  refine ⟨horder, ?_⟩
  have hd := wordDist_match_le D hqlet hh₁ hh₂ (by omega : i₁ ≤ i₂) hi₂ he₁ he₂
  have hg := le_of_qg_one (hsg j₁ j₂ (le_of_lt horder) hj₂) hB
  omega

end Cross

end OsinComponents
end GGT

namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Mirrored

variable {G : Type u} [Group G]

/-- **The mirrored aligned case, from the connector.**

`HullSC.listVal_conj_of_alignedMatch_assembled` with both members rotations of
the formal inverse; the letters carry inverses and the mirrored closer is the
one that applies. -/
theorem listVal_conj_of_mirroredAlignedMatch_assembled
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {eps bn : ℕ} {ms : List ℕ}
    (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsymm : ∀ g ∈ D.base, g⁻¹ ∈ D.base)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    (hpair : GGT.OsinComponents.MatchedPairOutput D eps bn)
    {p : List G} {c c' i j : ℕ}
    (hiR : i < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    (hjR : j < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length)
    {b : Bool} {e f : ℕ} (he : e ∈ ms) (hf : f ∈ ms)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c
      = u ++ tl)
    (hw' : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c'
      = u' ++ tl')
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
      ((y - x : ℕ) : ℝ) / 1 - (bn : ℝ)
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
      GGT.OsinComponents.IsCompStart b
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') (py.length + i') →
      (GGT.OsinComponents.vertex (1 : G) u i)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam b)
    (hsside : ∀ m : ℕ, m ≤ u'.length → m ≠ j + 1 →
      GGT.OsinComponents.IsCompStart b
          (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
          (py.length + u.length + pz.length + (u'.length - m)) →
      (GGT.OsinComponents.vertex (1 : G) u' (j + 1))⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b)
    (hx1 : (GGT.OsinComponents.vertex (1 : G) u' j)⁻¹ *
        (GGT.RelLetter.listVal py *
          GGT.OsinComponents.vertex (1 : G) u i) = 1)
    (hletu : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c)[i]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ e)⁻¹)))
    (hletu' : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j]?
      = some (GGT.RelLetter.comp b
          (((if b then a true else a false) ^ f)⁻¹))) :
    GGT.RelLetter.listVal
        ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')
      = GGT.RelLetter.listVal py *
        GGT.RelLetter.listVal
          ((RelWord.revInv
            (relatorWord₂ p (a false) (a true) ms)).rotate c) *
        (GGT.RelLetter.listVal py)⁻¹ := by
  have hConn := GGT.OsinComponents.connected_of_connector D b py u pz u' hclose
    (by omega : i ≤ u.length) (j + 1) hh hconn
  obtain ⟨hxb, hx'b⟩ := hpair b py u pz u' i j hclose hlet4 hpy hpz hpy0 hqg
    hcompu (Or.inr hpz0) hcompu' (Or.inr hpz0) hConn hqside hsside
  exact listVal_conj_of_mirroredAlignedMatch_pair hnodup hinj hsymm hsep
    hiR hjR he hf hw hw' hiu hju hxb hx'b hx1 hletu hletu'

end Mirrored

end HullSC
end GroupApproximation
