import GroupApproximation.GGT.HullSCRelatorSeparation2Published

/-!
# Splitting Hull's published filling input into Lemmas 4.4 and 4.9

`HullConeOffStatement₂Published` deliberately asks for the whole output used by
the manuscript at one set of small-cancellation constants.  In the source this
output is obtained from two different lemmas:

* Lemma 4.4 supplies the injectivity/hyperbolic-embedding geometry and the
  quotient alphabet;
* Lemma 4.9, using the additional prime-piece clause, supplies the
  order-preserving lift of finite-order elements.

The constants in the two lemmas need not initially agree.  This file proves
the parameter monotonicity of the complete published input and synchronises the
two triples by taking the larger `eps` and `rho` and the smaller `mu`.  Thus the
remaining interfaces below are source-sized: the Lemma 4.4 record omits exactly
`finiteOrder_lift`, and the Lemma 4.9 interface concludes exactly that field.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

namespace RelWord

/-! ## Monotonicity of every published small-cancellation clause -/

/-- An `eps'`-piece is an `eps`-piece when `eps' ≤ eps`. -/
theorem IsPiece.mono_eps {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps' eps : ℕ} {a v : List (GGT.RelLetter G Λ)}
    (h : IsPiece D W eps' a v) (heps : eps' ≤ eps) :
    IsPiece D W eps a v := by
  obtain ⟨hv, hpre, v', hv', hne, a', s', hv'pre,
    y, z, hy, hz, hval, hexcl⟩ := h
  exact ⟨hv, hpre, v', hv', hne, a', s', hv'pre,
    y, z, le_trans hy heps, le_trans hz heps, hval, hexcl⟩

/-- A published `eps'`-piece is a published `eps`-piece when `eps' ≤ eps`. -/
theorem IsPublishedPiece.mono_eps {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps' eps : ℕ} {a a' v : List (GGT.RelLetter G Λ)}
    (h : IsPublishedPiece D W eps' a a' v) (heps : eps' ≤ eps) :
    IsPublishedPiece D W eps a a' v := by
  obtain ⟨hv, hpre, v', hv', s', hv'pre,
    y, z, hy, hz, hval, hexcl⟩ := h
  exact ⟨hv, hpre, v', hv', s', hv'pre,
    y, z, le_trans hy heps, le_trans hz heps, hval, hexcl⟩

/-- A published `eps'`-primepiece is an `eps`-primepiece when
`eps' ≤ eps`. -/
theorem IsPrimePiece.mono_eps {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps' eps : ℕ} {a a' v : List (GGT.RelLetter G Λ)}
    (h : IsPrimePiece D W eps' a a' v) (heps : eps' ≤ eps) :
    IsPrimePiece D W eps a a' v := by
  obtain ⟨hv, middle, tail, hsplit, y, z, hy, hz, hval⟩ := h
  exact ⟨hv, middle, tail, hsplit, y, z,
    le_trans hy heps, le_trans hz heps, hval⟩

/-- Hull's `C(eps,mu,rho)` condition becomes weaker when `eps` and `rho`
decrease and `mu` increases. -/
theorem IsSmallCancellation.mono_parameters
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps eps' rho rho' : ℕ} {mu mu' : ℝ}
    (h : IsSmallCancellation D W eps mu rho)
    (heps : eps' ≤ eps) (hmu : mu ≤ mu') (hrho : rho' ≤ rho) :
    IsSmallCancellation D W eps' mu' rho' where
  admissible := h.admissible
  inv_mem := h.inv_mem
  rotate_mem := h.rotate_mem
  long := fun v hv => le_trans hrho (h.long v hv)
  deep := by
    intro v hv a ha lam hcomp hball
    exact h.deep v hv a ha lam hcomp
      (GGT.OsinComponents.relBall_mono_radius D lam hrho hball)
  pieces_small := by
    intro a v hp
    have hlt := h.pieces_small a v (hp.mono_eps heps)
    have hle : mu * (v.length : ℝ) ≤ mu' * v.length :=
      mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)
    exact lt_of_lt_of_le hlt hle

/-- The complete Lemma 4.4 input has the same parameter monotonicity. -/
theorem IsLemma44Input.mono_parameters
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps eps' rho rho' : ℕ} {mu mu' : ℝ}
    (h : IsLemma44Input D W eps mu rho)
    (heps : eps' ≤ eps) (hmu : mu ≤ mu') (hrho : rho' ≤ rho) :
    IsLemma44Input D W eps' mu' rho' where
  toIsSmallCancellation :=
    h.toIsSmallCancellation.mono_parameters heps hmu hrho
  quasiGeodesic := h.quasiGeodesic
  publishedPiecesSmall := by
    intro a a' v hp
    have hlt := h.publishedPiecesSmall a a' v (hp.mono_eps heps)
    have hle : mu * (v.length : ℝ) ≤ mu' * v.length :=
      mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)
    exact lt_of_lt_of_le hlt hle
  stronglyBounded := h.stronglyBounded

/-- The complete Lemma 4.9 `C₁` input has the same parameter monotonicity. -/
theorem IsLemma49Input.mono_parameters
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ} {W : Set (List (GGT.RelLetter G Λ))}
    {eps eps' rho rho' : ℕ} {mu mu' : ℝ}
    (h : IsLemma49Input D W eps mu rho)
    (heps : eps' ≤ eps) (hmu : mu ≤ mu') (hrho : rho' ≤ rho) :
    IsLemma49Input D W eps' mu' rho' where
  toIsLemma44Input := h.toIsLemma44Input.mono_parameters heps hmu hrho
  primePiecesSmall := by
    intro a a' v hp
    have hlt := h.primePiecesSmall a a' v (hp.mono_eps heps)
    have hle : mu * (v.length : ℝ) ≤ mu' * v.length :=
      mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)
    exact lt_of_lt_of_le hlt hle

end RelWord

/-! ## The exact Lemma 4.4 cone-off record -/

/-- `ConeOffData₂` with exactly the Lemma 4.9 field removed.

Every field here belongs to the Lemma 4.4/cone-off half of Hull's argument.
The omitted `finiteOrder_lift` is precisely the conclusion of Lemma 4.9. -/
structure ConeOffData₂Lemma44 {G : Type u} [Group G] {Λ : Type w}
    (A : Alphabet G) (K : Λ → Subgroup G) (L : ℝ) where
  Space : Type u
  [metric : PseudoMetricSpace Space]
  [action : MulAction G Space]
  isometric : IsIsometricAction G Space
  base : Space
  letter_dist : ∀ a ∈ A.carrier, dist base (a • base) ≤ 1
  apex : Λ → Space
  fix : ∀ (lam : Λ), ∀ k ∈ K lam, k • apex lam = apex lam
  normal_in_stab : ∀ (lam : Λ) (s : G), s • apex lam = apex lam →
    ∀ k ∈ K lam, s * k * s⁻¹ ∈ K lam
  apex_ne : ∀ (lam mu : Λ), lam ≠ mu → ∀ g g' : G,
    g • apex lam ≠ g' • apex mu
  delta : ℝ
  delta_pos : 0 < delta
  hyperbolic : IsHyperbolicSpace delta Space
  isGeodesic : IsGeodesicSpace Space
  sep : ℝ
  sep_ge : 200 * delta ≤ sep
  separated : ∀ (lam mu : Λ) (g g' : G),
    g • apex lam ≠ g' • apex mu →
      sep ≤ dist (g • apex lam) (g' • apex mu)
  injRadius : ℝ
  lt_injRadius : L < injRadius
  kernel_moves : ∀ g ∈ Subgroup.normalClosure (⋃ lam : Λ, (K lam : Set G)),
    g ≠ 1 → injRadius ≤ dist base (g • base)
  veryRotating : ∀ (lam : Λ) (g k : G), k ∈ K lam →
    g * k * g⁻¹ ≠ 1 → ∀ x y : Space,
      20 * delta ≤ dist x (g • apex lam) →
      dist x (g • apex lam) ≤ 40 * delta →
      20 * delta ≤ dist y (g • apex lam) →
      dist y (g • apex lam) ≤ 40 * delta →
      dist ((g * k * g⁻¹) • x) y ≤ 15 * delta →
      ∀ f : ℝ → Space, IsGeodesicSegment f 0 (dist x y) → f 0 = x →
        f (dist x y) = y →
          ∃ s ∈ Set.Icc (0 : ℝ) (dist x y), f s = g • apex lam

namespace ConeOffData₂Lemma44

instance instMetric {G : Type u} [Group G] {Λ : Type w} {A : Alphabet G}
    {K : Λ → Subgroup G} {L : ℝ} (P : ConeOffData₂Lemma44 A K L) :
    PseudoMetricSpace P.Space := P.metric

instance instAction {G : Type u} [Group G] {Λ : Type w} {A : Alphabet G}
    {K : Λ → Subgroup G} {L : ℝ} (P : ConeOffData₂Lemma44 A K L) :
    MulAction G P.Space := P.action

/-- Add exactly Hull Lemma 4.9's conclusion to the Lemma 4.4 record. -/
def toConeOffData₂ {G : Type u} [Group G] {Λ : Type w} {A : Alphabet G}
    {K : Λ → Subgroup G} {L : ℝ} (P : ConeOffData₂Lemma44 A K L)
    (hfinite : ∀ {Q : Type u} [Group Q] (q : G →* Q),
      q.ker = Subgroup.normalClosure (⋃ lam : Λ, (K lam : Set G)) →
        ∀ y : Q, IsOfFinOrder y →
          ∃ g : G, q g = y ∧ orderOf g = orderOf y) :
    ConeOffData₂ A K L where
  Space := P.Space
  metric := P.metric
  action := P.action
  isometric := P.isometric
  base := P.base
  letter_dist := P.letter_dist
  apex := P.apex
  fix := P.fix
  normal_in_stab := P.normal_in_stab
  apex_ne := P.apex_ne
  delta := P.delta
  delta_pos := P.delta_pos
  hyperbolic := P.hyperbolic
  isGeodesic := P.isGeodesic
  sep := P.sep
  sep_ge := P.sep_ge
  separated := P.separated
  injRadius := P.injRadius
  lt_injRadius := P.lt_injRadius
  kernel_moves := P.kernel_moves
  finiteOrder_lift := hfinite
  veryRotating := P.veryRotating

end ConeOffData₂Lemma44

/-! ## Source-sized statements and their assembly -/

/-- Hull Lemma 4.4 in exactly the form used by the pair construction.

The premise is only `IsLemma44Input`; the result contains every cone-off field
except no-new-torsion, together with the quotient alphabet and preservation of
the prescribed suitable subgroups. -/
def HullLemma44ConeOffStatement₂Published : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore₂ A N), Suitable A.alphabet N →
      ∀ {k : ℕ} (S : Fin k → Subgroup G),
        (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ R : ℕ,
          ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
            ∀ (W : Set (List (GGT.RelLetter G Bool)))
              (v : List (GGT.RelLetter G Bool)), v ∈ W →
              RelWord.IsLemma44Input E.rel W eps mu rho →
                (∃ (K : Bool → Subgroup G)
                    (_ : ConeOffData₂Lemma44 A.alphabet K (2 * (R : ℝ))),
                    Subgroup.normalClosure (⋃ b : Bool, (K b : Set G)) =
                      Subgroup.normalClosure
                        ({GGT.RelLetter.listVal v} : Set G)) ∧
                  ∀ {Q : Type u} [Group Q] (q : G →* Q),
                    Function.Surjective q →
                    q.ker = Subgroup.normalClosure
                      ({GGT.RelLetter.listVal v} : Set G) →
                    Nonempty (FillingAlphabetData A N S q)

/-- Hull Lemma 4.9 in its exact order-preserving form.  Unlike the combined
filling statement it has no radius or prescribed subgroup family: those data
play no role in the printed lemma. -/
def HullLemma49FiniteOrderStatement₂Published : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    (E : HypEmbeddedCore₂ A N),
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G Bool)))
          (v : List (GGT.RelLetter G Bool)), v ∈ W →
          RelWord.IsLemma49Input E.rel W eps mu rho →
            ∀ {Q : Type u} [Group Q] (q : G →* Q),
              q.ker = Subgroup.normalClosure
                ({GGT.RelLetter.listVal v} : Set G) →
                ∀ y : Q, IsOfFinOrder y →
                  ∃ g : G, q g = y ∧ orderOf g = orderOf y

/-- The two printed lemmas imply the combined published cone-off statement.

The only work here is real parameter bookkeeping: use
`max eps₄₄ eps₄₉`, `max rho₄₄ rho₄₉`, and `min mu₄₄ mu₄₉`,
then project the resulting stronger `C₁` input to each lemma at its own
constants. -/
theorem hullConeOffStatement₂Published_of_lemma44_of_lemma49
    (h44 : HullLemma44ConeOffStatement₂Published.{u})
    (h49 : HullLemma49FiniteOrderStatement₂Published.{u}) :
    HullConeOffStatement₂Published.{u} := by
  intro G _ A N E hN k S hS R
  obtain ⟨eps44, rho44, mu44, hmu44, hgood44⟩ := h44 A N E hN S hS R
  obtain ⟨eps49, rho49, mu49, hmu49, hgood49⟩ := h49 E
  refine ⟨max eps44 eps49, max rho44 rho49, min mu44 mu49,
    lt_min hmu44 hmu49, ?_⟩
  intro W v hv hsc
  have hsc44 : RelWord.IsLemma44Input E.rel W eps44 mu44 rho44 :=
    hsc.toIsLemma44Input.mono_parameters
      (Nat.le_max_left _ _) (min_le_left _ _) (Nat.le_max_left _ _)
  have hsc49 : RelWord.IsLemma49Input E.rel W eps49 mu49 rho49 :=
    hsc.mono_parameters
      (Nat.le_max_right _ _) (min_le_right _ _) (Nat.le_max_right _ _)
  obtain ⟨⟨K, P, hclosure⟩, halphabet⟩ := hgood44 W v hv hsc44
  have hfinite : ∀ {Q : Type u} [Group Q] (q : G →* Q),
      q.ker = Subgroup.normalClosure (⋃ b : Bool, (K b : Set G)) →
        ∀ y : Q, IsOfFinOrder y →
          ∃ g : G, q g = y ∧ orderOf g = orderOf y := by
    intro Q _ q hker y hy
    apply hgood49 W v hv hsc49 q
    · exact hker.trans hclosure
    · exact hy
  exact ⟨⟨K, P.toConeOffData₂ hfinite, hclosure⟩, halphabet⟩

end HullSC
end GroupApproximation
