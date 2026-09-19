import GroupApproximation.GGT.KazhdanHypSymplecticQuadrangleCounts

/-!
# The Tits polarity coordinate layer for `W(8)`

The coordinate charts below are the Klein--orthogonal presentation of the
Suzuki--Tits polarity, with the two middle symplectic coordinates put in the
order used by `KazhdanHypSymplecticQuadrangle`.  The field automorphism is
`x ↦ x⁴`; its square is Frobenius and its inverse is `x ↦ x²`, so the chart
formula is a genuine involutive point--line correspondence.

The coordinate layer is kept separate from the triangle-table layer.  It
records the normalized representatives, the four line charts, and the finite
field identities used by the later incidence and absolute-point proofs.
-/

noncomputable section

namespace GroupApproximation
namespace KazhdanHyp
namespace SymplecticQuadrangle
namespace TitsPolarity

open scoped LinearAlgebra.Projectivization

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

abbrev K := FieldEight
abbrev V := Vec

/-- The Tits automorphism on `GF(8)`, so `theta x = x⁴`. -/
noncomputable def theta : K ≃+* K :=
  iterateFrobeniusEquiv K 2 2

/-- The inverse Tits automorphism, so `thetaInv x = x²`. -/
noncomputable def thetaInv : K ≃+* K :=
  iterateFrobeniusEquiv K 2 1

theorem theta_apply (x : K) : theta x = x ^ 4 := by
  rw [theta, iterateFrobeniusEquiv_def]
  norm_num

theorem thetaInv_apply (x : K) : thetaInv x = x ^ 2 := by
  rw [thetaInv, iterateFrobeniusEquiv_def]
  norm_num

theorem theta_sq (x : K) : theta (theta x) = x ^ 2 := by
  calc
    theta (theta x) = x ^ (4 * 4) := by
      rw [theta_apply, theta_apply, ← pow_mul]
    _ = x ^ (8 * 2) := by norm_num
    _ = (x ^ 8) ^ 2 := by rw [pow_mul]
    _ = x ^ 2 := by
      have hx : x ^ 8 = x := by
        simpa [fieldEight_card] using FiniteField.pow_card x
      rw [hx]

theorem thetaInv_theta (x : K) : thetaInv (theta x) = x := by
  calc
    thetaInv (theta x) = x ^ (4 * 2) := by
      rw [thetaInv_apply, theta_apply, ← pow_mul]
    _ = x ^ 8 := by norm_num
    _ = x := by simpa [fieldEight_card] using FiniteField.pow_card x

theorem theta_thetaInv (x : K) : theta (thetaInv x) = x := by
  calc
    theta (thetaInv x) = x ^ (2 * 4) := by
      rw [theta_apply, thetaInv_apply, ← pow_mul]
    _ = x ^ 8 := by norm_num
    _ = x := by simpa [fieldEight_card] using FiniteField.pow_card x

theorem thetaInv_sq (x : K) : thetaInv (x ^ 2) = theta x := by
  rw [thetaInv_apply, theta_apply, ← pow_mul]

noncomputable instance KDecidableEq : DecidableEq K := Classical.decEq K

/-- The four normalized point charts in the standard `W(8)` coordinates. -/
inductive CoordPoint where
  | infinity
  | one (a : K)
  | two (k b : K)
  | three (a l a' : K)
  deriving DecidableEq, Fintype

/-- The four normalized line charts in the standard `W(8)` coordinates. -/
inductive CoordLine where
  | infinity
  | one (k : K)
  | two (a l : K)
  | three (k b k' : K)
  deriving DecidableEq, Fintype

/-- Normalized vector for each point chart. -/
def pointVector : CoordPoint → V
  | .infinity => ![1, 0, 0, 0]
  | .one a => ![a, 1, 0, 0]
  | .two k b => ![-b, k, 0, 1]
  | .three a l a' => ![l - a * a', -a', 1, -a]

/-- First line generator for each line chart. -/
def lineVector₁ : CoordLine → V
  | .infinity => ![1, 0, 0, 0]
  | .one _ => ![1, 0, 0, 0]
  | .two a _ => ![a, 1, 0, 0]
  | .three k b _ => ![-b, k, 0, 1]

/-- Second line generator for each line chart. -/
def lineVector₂ : CoordLine → V
  | .infinity => ![0, 1, 0, 0]
  | .one k => ![0, k, 0, 1]
  | .two a l => ![l, 0, 1, -a]
  | .three _ b k' => ![k', -b, 1, 0]

private theorem pointVector_ne_zero (p : CoordPoint) : pointVector p ≠ 0 := by
  cases p <;> intro h
  · have h0 := congrFun h 0
    simpa [pointVector] using h0
  · have h1 := congrFun h 1
    simpa [pointVector] using h1
  · have h3 := congrFun h 3
    simpa [pointVector] using h3
  · have h2 := congrFun h 2
    simpa [pointVector] using h2

private theorem coordinate_pair_linearIndependent
    (u v : V) (i j : Fin 4)
    (hui : u i = 1) (hvi : v i = 0)
    (huj : u j = 0) (hvj : v j = 1) :
    LinearIndependent K ![u, v] := by
  rw [LinearIndependent.pair_iff' (by
    intro hu
    have := congrFun hu i
    simpa [hui] using this)]
  intro c hc
  have hci := congrFun hc i
  have hcj := congrFun hc j
  have hc0 : c = 0 := by
    simpa [Pi.smul_apply, smul_eq_mul, hui, hvi] using hci
  subst c
  have hbad : (0 : K) = 1 := by
    simpa [Pi.smul_apply, smul_eq_mul, huj, hvj] using hcj
  exact zero_ne_one hbad

private theorem line_pair_linearIndependent (l : CoordLine) :
    LinearIndependent K ![lineVector₁ l, lineVector₂ l] := by
  cases l with
  | infinity =>
      exact coordinate_pair_linearIndependent _ _ 0 1 (by simp [lineVector₁])
        (by simp [lineVector₂]) (by simp [lineVector₁]) (by simp [lineVector₂])
  | one k =>
      exact coordinate_pair_linearIndependent _ _ 0 3 (by simp [lineVector₁])
        (by simp [lineVector₂]) (by simp [lineVector₁]) (by simp [lineVector₂])
  | two a l =>
      exact coordinate_pair_linearIndependent _ _ 1 2 (by simp [lineVector₁])
        (by simp [lineVector₂]) (by simp [lineVector₁]) (by simp [lineVector₂])
  | three k b k' =>
      exact coordinate_pair_linearIndependent _ _ 3 2 (by simp [lineVector₁])
        (by simp [lineVector₂]) (by simp [lineVector₁]) (by simp [lineVector₂])

private theorem line_pair_orthogonal (l : CoordLine) :
    form (lineVector₁ l) (lineVector₂ l) = 0 := by
  cases l with
  | infinity => simp [lineVector₁, lineVector₂, form_apply]
  | one k => simp [lineVector₁, lineVector₂, form_apply]
  | two a l => simp [lineVector₁, lineVector₂, form_apply]
  | three k b k' => simp [lineVector₁, lineVector₂, form_apply]

private theorem span_pair_isotropic (u v : V) (huv : form u v = 0) :
    IsTotallyIsotropic (Submodule.span K {u, v}) := by
  intro x hx y hy
  rw [Submodule.mem_span_pair] at hx hy
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  have hvu : form v u = 0 := (form_eq_zero_comm u v).mp huv
  simp [map_add, map_smul, form_isAlt.self_eq_zero, huv, hvu]

private theorem line_span_finrank (l : CoordLine) :
    Module.finrank K (Submodule.span K {lineVector₁ l, lineVector₂ l}) = 2 := by
  rw [← Matrix.range_cons_cons_empty (lineVector₁ l) (lineVector₂ l) ![]]
  simpa using finrank_span_eq_card (line_pair_linearIndependent l)

private def pointOfCoord (p : CoordPoint) : Point :=
  Projectivization.mk K (pointVector p) (pointVector_ne_zero p)

private def lineOfCoord (l : CoordLine) : Line :=
  ⟨Submodule.span K {lineVector₁ l, lineVector₂ l}, line_span_finrank l,
    span_pair_isotropic _ _ (line_pair_orthogonal l)⟩

private theorem pointOfCoord_injective : Function.Injective pointOfCoord := by
  intro p q hpq
  cases p <;> cases q
  all_goals try rfl
  all_goals simp only [pointOfCoord] at hpq
  all_goals
    rw [Projectivization.mk_eq_mk_iff'] at hpq
  all_goals
    rcases hpq with ⟨c, hc⟩
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    have h2 := congrFun hc 2
    have h3 := congrFun hc 3
    simp [pointVector, Pi.smul_apply, smul_eq_mul] at h0 h1 h2 h3 ⊢
    try simp_all
    try subst_vars
    try simp_all

private theorem lineOfCoord_injective : Function.Injective lineOfCoord := by
  intro l m h
  have h1 : lineVector₁ l ∈ (lineOfCoord m).1 := by
    rw [← h]
    exact Submodule.subset_span (by simp)
  have h2 : lineVector₂ l ∈ (lineOfCoord m).1 := by
    rw [← h]
    exact Submodule.subset_span (by simp)
  change lineVector₁ l ∈ Submodule.span K {lineVector₁ m, lineVector₂ m} at h1
  change lineVector₂ l ∈ Submodule.span K {lineVector₁ m, lineVector₂ m} at h2
  rw [Submodule.mem_span_pair] at h1 h2
  cases l <;> cases m
  all_goals try rfl
  all_goals
    rcases h1 with ⟨r₁, s₁, hr₁⟩
    rcases h2 with ⟨r₂, s₂, hr₂⟩
    have h10 := congrFun hr₁ 0
    have h11 := congrFun hr₁ 1
    have h12 := congrFun hr₁ 2
    have h13 := congrFun hr₁ 3
    have h20 := congrFun hr₂ 0
    have h21 := congrFun hr₂ 1
    have h22 := congrFun hr₂ 2
    have h23 := congrFun hr₂ 3
    simp [lineVector₁, lineVector₂, Pi.smul_apply, smul_eq_mul] at h10 h11 h12 h13 h20 h21 h22 h23 ⊢
    try simp_all
    try subst_vars
    try simp_all

private def coordPointSumEquiv :
    CoordPoint ≃ Unit ⊕ K ⊕ (K × K) ⊕ (K × K × K) where
  toFun
    | .infinity => Sum.inl ()
    | .one a => Sum.inr (Sum.inl a)
    | .two k b => Sum.inr (Sum.inr (Sum.inl (k, b)))
    | .three a l a' => Sum.inr (Sum.inr (Sum.inr (a, l, a')))
  invFun
    | Sum.inl () => .infinity
    | Sum.inr (Sum.inl a) => .one a
    | Sum.inr (Sum.inr (Sum.inl (k, b))) => .two k b
    | Sum.inr (Sum.inr (Sum.inr (a, l, a'))) => .three a l a'
  left_inv := by intro p; cases p <;> rfl
  right_inv := by
    intro p
    cases p with
    | inl u => cases u; rfl
    | inr p =>
        cases p with
        | inl a => rfl
        | inr p =>
            cases p with
            | inl ab => rcases ab with ⟨k, b⟩; rfl
            | inr abc => rcases abc with ⟨a, l, a'⟩; rfl

private def coordLineSumEquiv :
    CoordLine ≃ Unit ⊕ K ⊕ (K × K) ⊕ (K × K × K) where
  toFun
    | .infinity => Sum.inl ()
    | .one k => Sum.inr (Sum.inl k)
    | .two a l => Sum.inr (Sum.inr (Sum.inl (a, l)))
    | .three k b k' => Sum.inr (Sum.inr (Sum.inr (k, b, k')))
  invFun
    | Sum.inl () => .infinity
    | Sum.inr (Sum.inl k) => .one k
    | Sum.inr (Sum.inr (Sum.inl (a, l))) => .two a l
    | Sum.inr (Sum.inr (Sum.inr (k, b, k'))) => .three k b k'
  left_inv := by intro l; cases l <;> rfl
  right_inv := by
    intro l
    cases l with
    | inl u => cases u; rfl
    | inr l =>
        cases l with
        | inl k => rfl
        | inr l =>
            cases l with
            | inl ab => rcases ab with ⟨a, l⟩; rfl
            | inr abc => rcases abc with ⟨k, b, k'⟩; rfl

theorem card_coordPoint : Fintype.card CoordPoint = 585 := by
  rw [Fintype.card_congr coordPointSumEquiv]
  simp [fieldEight_card]

theorem card_coordLine : Fintype.card CoordLine = 585 := by
  rw [Fintype.card_congr coordLineSumEquiv]
  simp [fieldEight_card]

theorem pointOfCoord_bijective : Function.Bijective pointOfCoord := by
  apply (Fintype.bijective_iff_injective_and_card pointOfCoord).2
  exact ⟨pointOfCoord_injective, by rw [card_coordPoint, point_card]⟩

theorem lineOfCoord_bijective : Function.Bijective lineOfCoord := by
  apply (Fintype.bijective_iff_injective_and_card lineOfCoord).2
  exact ⟨lineOfCoord_injective, by rw [card_coordLine, line_card]⟩

noncomputable def pointCoordEquiv : CoordPoint ≃ Point :=
  Equiv.ofBijective pointOfCoord pointOfCoord_bijective

noncomputable def lineCoordEquiv : CoordLine ≃ Line :=
  Equiv.ofBijective lineOfCoord lineOfCoord_bijective

private theorem coordIncident_iff (p : CoordPoint) (l : CoordLine) :
    Incident (pointOfCoord p) (lineOfCoord l) ↔
      pointVector p ∈ Submodule.span K {lineVector₁ l, lineVector₂ l} := by
  change Projectivization.mk K (pointVector p) _ ∈
    (Submodule.span K {lineVector₁ l, lineVector₂ l}).projectivization ↔ _
  rw [Submodule.mk_mem_projectivization_iff]

/-- The chart formula for the Tits polarity on point coordinates. -/
def polarityCoord : CoordPoint ≃ CoordLine where
  toFun
    | .infinity => .infinity
    | .one a => .one (theta a)
    | .two k b => .two (thetaInv k) (theta b)
    | .three a l a' => .three (theta a) (thetaInv l) (theta a')
  invFun
    | .infinity => .infinity
    | .one k => .one (thetaInv k)
    | .two a l => .two (theta a) (thetaInv l)
    | .three k b k' => .three (thetaInv k) (theta b) (thetaInv k')
  left_inv := by
    intro p
    cases p <;> simp [thetaInv_theta, theta_thetaInv]
  right_inv := by
    intro l
    cases l <;> simp [thetaInv_theta, theta_thetaInv]

noncomputable def titsPolarity : Point ≃ Line :=
  pointCoordEquiv.symm.trans (polarityCoord.trans lineCoordEquiv)

theorem titsPolarity_bijective : Function.Bijective titsPolarity :=
  titsPolarity.bijective

theorem titsPolarity_apply (p : CoordPoint) :
    titsPolarity (pointOfCoord p) = lineOfCoord (polarityCoord p) := by
  simp [titsPolarity, pointCoordEquiv, lineCoordEquiv]

private theorem three_three_forward (a₁ l₁ c₁ a l c : K)
    (h :
      a₁ * thetaInv l + theta c = l₁ - a₁ * c₁ ∧
        -(a₁ * theta a) + -thetaInv l = -c₁) :
    a * thetaInv l₁ + theta c₁ = l - a * c ∧
      -(a * theta a₁) + -thetaInv l₁ = -c := by
  rcases h with ⟨h₁, h₂⟩
  have hzl : thetaInv l = c₁ + a₁ * theta a := by
    simp only [CharTwo.neg_eq] at h₂ ⊢
    rw [CharTwo.eq_add_iff_add_eq]
    simpa [add_comm] using h₂
  have htc : theta c = l₁ + a₁ ^ 2 * theta a := by
    rw [hzl] at h₁
    have h₁' := congrArg (fun z : K => z + a₁ * c₁) h₁
    ring_nf at h₁'
    rw [CharTwo.eq_add_iff_add_eq]
    simpa [CharTwo.two_eq_zero, add_comm] using h₁'
  have htl₁_aux : c = thetaInv l₁ + theta a₁ * a := by
    have haux := congrArg thetaInv htc
    simpa [map_add, map_mul, thetaInv_theta, thetaInv_sq] using haux
  have htl₁ : thetaInv l₁ = c + a * theta a₁ := by
    rw [CharTwo.eq_add_iff_add_eq]
    simpa [add_comm, mul_comm] using htl₁_aux.symm
  have htc₁_aux : l = theta c₁ + theta a₁ * a ^ 2 := by
    have haux := congrArg theta hzl
    simpa [map_add, map_mul, theta_thetaInv, theta_sq] using haux
  have htc₁ : theta c₁ = l + theta a₁ * a ^ 2 := by
    rw [CharTwo.eq_add_iff_add_eq]
    simpa [add_comm] using htc₁_aux.symm
  constructor
  · rw [htl₁, htc₁]
    ring_nf
    simp [CharTwo.two_eq_zero, CharTwo.neg_eq]
  · rw [htl₁]
    ring_nf
    simp [CharTwo.two_eq_zero, CharTwo.neg_eq]

private theorem three_three_symm (a₁ l₁ c₁ a l c : K) :
    (a₁ * thetaInv l + theta c = l₁ - a₁ * c₁ ∧
      -(a₁ * theta a) + -thetaInv l = -c₁) ↔
    (a * thetaInv l₁ + theta c₁ = l - a * c ∧
      -(a * theta a₁) + -thetaInv l₁ = -c) := by
  constructor
  · exact three_three_forward a₁ l₁ c₁ a l c
  · exact three_three_forward a l c a₁ l₁ c₁

theorem polarity_incidence_symm_coord (p q : CoordPoint) :
    Incident (pointOfCoord p) (lineOfCoord (polarityCoord q)) ↔
      Incident (pointOfCoord q) (lineOfCoord (polarityCoord p)) := by
  cases p <;> cases q
  all_goals simp only [coordIncident_iff]
  all_goals
    simp [polarityCoord, pointVector, lineVector₁, lineVector₂,
      Submodule.mem_span_pair, Pi.smul_apply, smul_eq_mul]
  case one.two =>
    constructor
    · intro h
      simpa [theta_thetaInv, eq_comm] using congrArg theta h
    · intro h
      simpa [thetaInv_theta, eq_comm] using congrArg thetaInv h
  case two.one =>
    constructor
    · intro h
      simpa [thetaInv_theta, eq_comm] using congrArg thetaInv h
    · intro h
      simpa [theta_thetaInv, eq_comm] using congrArg theta h
  case two.three =>
    rename_i k b a l a'
    constructor
    · rintro ⟨hl, hk⟩
      have hka : thetaInv k = a := by
        simpa [thetaInv_theta, eq_comm] using congrArg thetaInv hk
      have hbl : theta b = l := by
        simpa [theta_thetaInv, eq_comm] using congrArg theta hl
      refine ⟨?_, hka⟩
      rw [hka, hbl]
      ring
    · rintro ⟨h₁, hka⟩
      have hbl : theta b = l := by
        rw [hka] at h₁
        linear_combination h₁
      have hl : thetaInv l = b := by
        simpa [thetaInv_theta, eq_comm] using congrArg thetaInv hbl
      have hk : theta a = k := by
        simpa [theta_thetaInv, eq_comm] using congrArg theta hka
      exact ⟨hl, hk⟩
  case three.two =>
    rename_i a l a' k b
    constructor
    · rintro ⟨h₁, hka⟩
      have hbl : theta b = l := by
        rw [hka] at h₁
        linear_combination h₁
      have hl : thetaInv l = b := by
        simpa [thetaInv_theta, eq_comm] using congrArg thetaInv hbl
      have hk : theta a = k := by
        simpa [theta_thetaInv, eq_comm] using congrArg theta hka
      exact ⟨hl, hk⟩
    · rintro ⟨hl, hk⟩
      have hka : thetaInv k = a := by
        simpa [thetaInv_theta, eq_comm] using congrArg thetaInv hk
      have hbl : theta b = l := by
        simpa [theta_thetaInv, eq_comm] using congrArg theta hl
      refine ⟨?_, hka⟩
      rw [hka, hbl]
      ring
  case three.three =>
    rename_i a₁ l₁ c₁ a l c
    exact three_three_symm a₁ l₁ c₁ a l c

theorem titsPolarity_incidence_symm (p q : Point) :
    Incident p (titsPolarity q) ↔ Incident q (titsPolarity p) := by
  obtain ⟨p₀, rfl⟩ := pointOfCoord_bijective.2 p
  obtain ⟨q₀, rfl⟩ := pointOfCoord_bijective.2 q
  rw [titsPolarity_apply, titsPolarity_apply]
  exact polarity_incidence_symm_coord p₀ q₀

private theorem coord_absolute_three_iff (a l c : K) :
    Incident (pointOfCoord (.three a l c))
        (lineOfCoord (polarityCoord (.three a l c))) ↔
      l = theta c + a ^ 2 * theta a := by
  rw [coordIncident_iff]
  simp [polarityCoord, pointVector, lineVector₁, lineVector₂,
    Submodule.mem_span_pair, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₂' : a * theta a + thetaInv l = c := by
      simpa [CharTwo.neg_eq, add_comm] using h₂
    have hθ := congrArg theta h₂'
    have hθ' : theta a * theta (theta a) + l = theta c := by
      simpa [map_add, map_mul, theta_thetaInv] using hθ
    rw [CharTwo.eq_add_iff_add_eq]
    simpa [theta_sq, add_comm, mul_comm] using hθ'
  · intro h
    have hInv : thetaInv l = c + a * theta a := by
      rw [h]
      simp [map_add, map_mul, thetaInv_theta, thetaInv_sq, mul_comm]
    constructor
    · rw [hInv, h]
      ring_nf
      simp [CharTwo.two_eq_zero, CharTwo.neg_eq, add_comm]
    · rw [hInv]
      ring_nf
      simp [CharTwo.two_eq_zero, CharTwo.neg_eq, add_comm]

private theorem coord_absolute_infinity :
    Incident (pointOfCoord .infinity)
      (lineOfCoord (polarityCoord .infinity)) := by
  rw [coordIncident_iff]
  simp [polarityCoord, pointVector, lineVector₁, lineVector₂,
    Submodule.mem_span_pair, Pi.smul_apply, smul_eq_mul]

private theorem coord_absolute_one_false (a : K) :
    ¬ Incident (pointOfCoord (.one a))
      (lineOfCoord (polarityCoord (.one a))) := by
  rw [coordIncident_iff]
  simp [polarityCoord, pointVector, lineVector₁, lineVector₂,
    Submodule.mem_span_pair, Pi.smul_apply, smul_eq_mul]

private theorem coord_absolute_two_false (k b : K) :
    ¬ Incident (pointOfCoord (.two k b))
      (lineOfCoord (polarityCoord (.two k b))) := by
  rw [coordIncident_iff]
  simp [polarityCoord, pointVector, lineVector₁, lineVector₂,
    Submodule.mem_span_pair, Pi.smul_apply, smul_eq_mul]

private abbrev CoordAbsolutePoint :=
  {p : CoordPoint // Incident (pointOfCoord p) (lineOfCoord (polarityCoord p))}

private def coordAbsolutePointEquiv :
    CoordAbsolutePoint ≃ Unit ⊕ (K × K) where
  toFun
    | ⟨.infinity, _⟩ => Sum.inl ()
    | ⟨.one a, h⟩ => (coord_absolute_one_false a h).elim
    | ⟨.two k b, h⟩ => (coord_absolute_two_false k b h).elim
    | ⟨.three a l c, _⟩ => Sum.inr (a, c)
  invFun
    | Sum.inl () => ⟨.infinity, coord_absolute_infinity⟩
    | Sum.inr (a, c) =>
        ⟨.three a (theta c + a ^ 2 * theta a) c,
          (coord_absolute_three_iff a _ c).2 rfl⟩
  left_inv := by
    intro p
    rcases p with ⟨p, hp⟩
    cases p with
    | infinity => rfl
    | one a => exact (coord_absolute_one_false a hp).elim
    | two k b => exact (coord_absolute_two_false k b hp).elim
    | three a l c =>
        have hl := (coord_absolute_three_iff a l c).1 hp
        simp [hl]
  right_inv := by
    intro p
    cases p with
    | inl u => cases u; rfl
    | inr ac => rcases ac with ⟨a, c⟩; rfl

theorem card_coordAbsolutePoint : Fintype.card CoordAbsolutePoint = 65 := by
  rw [Fintype.card_congr coordAbsolutePointEquiv]
  simp [fieldEight_card]

theorem titsAbsolutePoint_card :
    Fintype.card {p : Point // Incident p (titsPolarity p)} = 65 := by
  let e : CoordAbsolutePoint ≃ {p : Point // Incident p (titsPolarity p)} :=
    pointCoordEquiv.subtypeEquiv (fun p => by
      change Incident (pointOfCoord p) (lineOfCoord (polarityCoord p)) ↔
        Incident (pointOfCoord p) (titsPolarity (pointOfCoord p))
      rw [titsPolarity_apply])
  rw [← Fintype.card_congr e]
  exact card_coordAbsolutePoint

end TitsPolarity
end SymplecticQuadrangle
end KazhdanHyp
end GroupApproximation
