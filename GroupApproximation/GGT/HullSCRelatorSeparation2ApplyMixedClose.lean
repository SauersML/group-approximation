import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyMixed

/-!
# The mixed case, closed, and the construction's two constants by name

The two numbers clause (C2) and clause (C3) of the construction are stated
against are written down ONCE here and used by name, because they appear in two
places that must not drift apart: the separation between the two blocks, which
is a hypothesis of the estimate, and the length of the run, which is a choice of
the construction.  Getting them out of step is invisible --- the theorem still
type-checks and still says something, just not what the construction promises.

* `blockConst p c` is `b = |p| + c`, the constant
  `HullSC.quasiGeodesic_relatorWord₂_of_blockCount` produces.
* `blockSeparation p c eps` is `2(eps + 1 + b)`, the separation
  `GGT.OsinComponents.lt_of_two_connectors_qg` asks between the two blocks.

The `+ b` is the whole point.  `GGT.OsinComponents.index_le_of_connector` would
give `2(eps + 1)`, but it reads `wordNorm (vertex 1 q i) = i` off the side being
GEODESIC, and these sides are only `(1, b)`-quasi-geodesic.  What is available
is `index_le_of_connector_qg`, the same statement with `b` added, and the
separation has to be taken against that one.

`false_of_mixedMatch_found` is then the composition: the per-match half twice,
the order and the gap from `GGT.OsinComponents.index_le_of_connector_qg` applied
once per match, and `HullSC.false_of_span_mixed` closes it.  The far indices are
`k - 1`, the component of the reversed side being `[k - 1, k)`, and `0 < k` ---
which `GGT.OsinComponents.exists_deep_match` supplies --- is what makes
`k₁ < k₂ → k₁ - 1 < k₂ - 1` true rather than merely plausible.

## Why not `gap_and_order_of_two_matches`

Because it asks both connectors to lie in ONE `H_λ`, and in the mixed case they
do not.  `HullSC.blockWord_index_alternates` makes consecutive block letters
carry opposite indices, so two blocks share an index exactly when the distance
between them is even --- and the separation this case asks for is
`blockSeparation + 1`, which is odd, `blockSeparation` being twice something.
So `b₁ = b₂` is not merely unproved here, it is false by construction.

Nothing is lost.  The common index was never used for anything: both
`GGT.OsinComponents.index_le_of_connector_qg` and the connector-pair estimate
underneath it read a connector only through `wordNorm h ≤ 1`, which holds
because an element of any `H_λ` is one letter of `X ⊔ ⨆H`.  Pinning each match
separately therefore needs no common index at all, and the two applications
bound the gap at both ends: `k₂ ≤ d₂ + E` and `d₁ ≤ k₁ + E` give
`k₂ - k₁ ≤ (d₂ - d₁) + 2E`, so the slack is `2E = blockSeparation`.  That is
weaker than the `b + 2` the connector-pair estimate would give at a common
index, and the weakening costs nothing: the slack is only ever compared against
`|R|`, and the run is as long as `L` asks.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Constants

variable {G : Type u}

/-- **The block-count constant**, `b = |p| + c`. -/
def blockConst (p : List G) (c : ℕ) : ℕ := p.length + c

/-- **The separation between the two blocks that clause (C2) asks for**,
`2(eps + 1 + b)`.  It is the quasi-geodesic separation, not the geodesic
`2(eps + 1)`. -/
def blockSeparation (p : List G) (c eps : ℕ) : ℕ :=
  2 * (eps + 1 + blockConst p c)

end Constants

section MixedClose

variable {G : Type u} [Group G]

/-- **The mixed case, closed from two found matches.** -/
theorem false_of_mixedMatch_found {D : GGT.RelGenSet G Bool} {a : Bool → G}
    {eps : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
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
    {p : List G} {c c' : ℕ} (hp0 : 0 < p.length)
    {py pz u u' tl tl' : List (GGT.RelLetter G Bool)}
    (hw : (relatorWord₂ p (a false) (a true) ms).rotate c = u ++ tl)
    (hw' : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c'
      = u' ++ tl')
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
    {bb : ℝ} {cnt epsPin : ℕ}
    (hqlet : ∀ z ∈ u, D.IsLetter z) (hslet : ∀ z ∈ u', D.IsLetter z)
    (hqgq : ∀ x y : ℕ, x ≤ y → y ≤ u.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier
              (GGT.OsinComponents.vertex (1 : G) u x)
              (GGT.OsinComponents.vertex (1 : G) u y) : ℕ) : ℝ))
    (hqgs : ∀ x y : ℕ, x ≤ y → y ≤ u'.length →
      ((y - x : ℕ) : ℝ) / 1 - bb
        ≤ ((wordDist D.alphabet.carrier
              (GGT.OsinComponents.vertex (1 : G) u' x)
              (GGT.OsinComponents.vertex (1 : G) u' y) : ℕ) : ℝ))
    (hB : bb ≤ ((blockConst p cnt : ℕ) : ℝ))
    (hple : wordNorm D.alphabet.carrier (GGT.RelLetter.listVal py) ≤ epsPin)
    {d₁ d₂ k₁ k₂ : ℕ} {b₁ b₂ : Bool} {e₁ e₂ : ℕ}
    (he₁ : e₁ ∈ ms) (he₂ : e₂ ∈ ms)
    (hd₁ : d₁ < u.length) (hd₂ : d₂ < u.length)
    (hk01 : 0 < k₁) (hk02 : 0 < k₂)
    (hk₁ : k₁ ≤ u'.length) (hk₂ : k₂ ≤ u'.length)
    (hletd₁ : ((relatorWord₂ p (a false) (a true) ms).rotate c)[d₁]?
      = some (GGT.RelLetter.comp b₁ ((if b₁ then a true else a false) ^ e₁)))
    (hletd₂ : ((relatorWord₂ p (a false) (a true) ms).rotate c)[d₂]?
      = some (GGT.RelLetter.comp b₂ ((if b₂ then a true else a false) ^ e₂)))
    {x₁ x₂ : G}
    (hx₁ : u'[k₁ - 1]? = some (GGT.RelLetter.comp b₁ x₁))
    (hx₂ : u'[k₂ - 1]? = some (GGT.RelLetter.comp b₂ x₂))
    {h₁ h₂ : G} (hh₁ : h₁ ∈ D.fam b₁) (hh₂ : h₂ ∈ D.fam b₂)
    (hconn₁ : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u d₁ * h₁
      = GGT.OsinComponents.vertex (1 : G) u' k₁)
    (hconn₂ : GGT.RelLetter.listVal py *
        GGT.OsinComponents.vertex (1 : G) u d₂ * h₂
      = GGT.OsinComponents.vertex (1 : G) u' k₂)
    (hqside₁ : ∀ i' : ℕ, i' ≤ u.length → i' ≠ d₁ →
      (GGT.OsinComponents.vertex (1 : G) u d₁)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam b₁)
    (hqside₂ : ∀ i' : ℕ, i' ≤ u.length → i' ≠ d₂ →
      (GGT.OsinComponents.vertex (1 : G) u d₂)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u i' ∉ D.fam b₂)
    (hsside₁ : ∀ m : ℕ, m ≤ u'.length → m ≠ k₁ →
      (GGT.OsinComponents.vertex (1 : G) u' k₁)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b₁)
    (hsside₂ : ∀ m : ℕ, m ≤ u'.length → m ≠ k₂ →
      (GGT.OsinComponents.vertex (1 : G) u' k₂)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) u' m ∉ D.fam b₂)
    (hsepn : d₁ + blockSeparation p cnt epsPin < d₂)
    (hlong : 2 * (d₂ - d₁) + blockSeparation p cnt epsPin
      < (relatorWord₂ p (a false) (a true) ms).length) : False := by
  have hsepdef : blockSeparation p cnt epsPin
      = 2 * (epsPin + 1 + blockConst p cnt) := rfl
  have hulen : u.length ≤ (relatorWord₂ p (a false) (a true) ms).length := by
    have hL := congrArg List.length hw
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hu'len : u'.length
      ≤ (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length := by
    have hL := congrArg List.length hw'
    rw [List.length_rotate, List.length_append] at hL
    omega
  have hrev : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length
      = (relatorWord₂ p (a false) (a true) ms).length := RelWord.length_revInv _
  obtain ⟨f₁, X₁, X₁', hf₁, hm₁, hX₁, hX₁', hid₁⟩ :=
    mixed_data_of_found_match hpair hp0 hw hw' hd₁ hk01 hk₁ hletd₁ hx₁ hh₁
      hconn₁ hpy hpz hpy0 hpz0 hlet4 hclose hqg hqside₁ hsside₁
  obtain ⟨f₂, X₂, X₂', hf₂, hm₂, hX₂, hX₂', hid₂⟩ :=
    mixed_data_of_found_match hpair hp0 hw hw' hd₂ hk02 hk₂ hletd₂ hx₂ hh₂
      hconn₂ hpy hpz hpy0 hpz0 hlet4 hclose hqg hqside₂ hsside₂
  obtain ⟨hp₁, hp₁'⟩ :=
    GGT.OsinComponents.index_le_of_connector_qg D hqlet hslet hqgq hqgs hB
      (by omega : d₁ ≤ u.length) hk₁ hple hh₁ hconn₁
  obtain ⟨hp₂, hp₂'⟩ :=
    GGT.OsinComponents.index_le_of_connector_qg D hqlet hslet hqgq hqgs hB
      (by omega : d₂ ≤ u.length) hk₂ hple hh₂ hconn₂
  exact false_of_span_mixed (gapSlack := blockSeparation p cnt epsPin) hnodup
    hinj hsep (by omega) (by omega) (by omega) (by omega) he₁ hf₁ he₂ hf₂ hX₁
    hX₁' hX₂ hX₂' hletd₁ hm₁ hletd₂ hm₂ hid₁ hid₂ (by omega) (by omega)

end MixedClose

end HullSC
end GroupApproximation
