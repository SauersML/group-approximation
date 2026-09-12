import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftFlip

/-!
# The pair bridge: two lifts on `H`, doubled, with the flip supplying the swap

`Analysis/ShulmanFillNormingExistentialLiftFlip` shows that doubling *one* lift
is useless for Shulman's Theorem 10: the flip commutes with every `diag(a, a)`,
so the second leg it produces is the first leg again, and the amalgam collapses.
The repair is to double the pair.  Given two asymptotic lifts `φ₁`, `φ₂` of two
representations `ρ₁`, `ρ₂ : D → B(H)` into the *same* `𝒟`, put

    `Ψ_t b = (n ↦ diag (φ₁_t b n, φ₂_t b n))` ,

an asymptotic lift of `pairRep ρ₁ ρ₂ : b ↦ hBlockOp (diag (ρ₁ b, ρ₂ b))` into
the doubled `𝒟`.  This is `StarStrongAsymptoticLift.doubleLR`, and now the flip
does what the paper wants:

    `u diag(x, y) u* = diag(y, x)`   (`ShulmanFill.flip2_conj_diagonal2`)

so `conjugate` sends `doubleLR φ₁ φ₂` to `doubleLR φ₂ φ₁` **exactly**, term by
term (`conjugate_doubleLR_toFun`), and at the level of representations
`Ad (q U) ∘ pairRep ρ₁ ρ₂ = pairRep ρ₂ ρ₁` (`pairRep_conjugate_eq`).  That is
Shulman's `ρ₁ = π₁ ⊕ π₂`, `ρ₂ = π₂ ⊕ π₁` with the flip conjugation carried out
inside `𝒟` rather than through a Halmos dilation.  So the *second doubled lift
is free*: Theorem 10 never needs a lift of the doubled representation twice.

## The one place a norm has to be computed

`diag(x, x)` was contractive for free, because `x ↦ diag(x, x)` is a
`*`-homomorphism of `E`.  `diag(x, y)` is not the image of `E` under anything;
it is the image of `E × E` under `diagonalPairHom2`, and the C-star norm of
`E × E` is the *maximum* of the two.  So the contractivity clause of `doubleLR`
reads `‖diag(x, y)‖ ≤ max ‖x‖ ‖y‖` (`norm_diagonalPairHom2_le`), which is again
just `NonUnitalStarAlgHom.norm_apply_le` — this time at `E × E` — together with
`Prod.norm_def`.  Each defect clause is then dominated by the maximum of the two
defects of `φ₁` and `φ₂`, and `Filter.Tendsto.max` sends that to zero.

## What is still assumed above this

`Analysis/ShulmanFillNormingExistentialLiftTwoLeg` states the honest binder
(one model chosen after *both* representations, carrying lifts of both) and
wires `isMFAlgebra_amalgam_of_glue` to it.  The faithfulness hypothesis `hΛ` of
that theorem stays a binder, exactly as it already was; deriving it from
faithfulness of `ρ₁ * ρ₂` on the double — the paper's "symmetry" step — needs
injectivity of `hBlockOp` and a universal-property identification of the glued
limit with `hBlockOpHom ∘ diagonalPairHom2 ∘ (Λ, Λ_swap)`, and is not written.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-! ## A pair of homomorphisms into a product -/

section Pairing

variable {D E : Type} [CStarAlgebra D] [CStarAlgebra E]

/-- Two `*`-homomorphisms with a common source and target, as one
homomorphism into the product.  Mathlib has `AlgHom.prod` but no
`StarAlgHom.prod` at this revision. -/
def starAlgHomPair (f g : D →⋆ₐ[ℂ] E) : D →⋆ₐ[ℂ] E × E where
  toFun d := (f d, g d)
  map_one' := Prod.ext (map_one f) (map_one g)
  map_mul' x y := Prod.ext (map_mul f x y) (map_mul g x y)
  map_zero' := Prod.ext (map_zero f) (map_zero g)
  map_add' x y := Prod.ext (map_add f x y) (map_add g x y)
  commutes' z := Prod.ext (AlgHomClass.commutes f z) (AlgHomClass.commutes g z)
  map_star' x := Prod.ext (map_star f x) (map_star g x)

@[simp] theorem starAlgHomPair_apply (f g : D →⋆ₐ[ℂ] E) (d : D) :
    starAlgHomPair f g d = (f d, g d) := rfl

end Pairing

/-! ## The diagonal of a pair -/

section DiagonalPair

variable {E : Type} [CStarAlgebra E]

/-- **The diagonal embedding of a pair** `(a, b) ↦ diag(a, b)`.  Unlike
`ShulmanFill.diagonalHom2` its source is `E × E`, which is where the two
entries of Shulman's `ρ₁ = π₁ ⊕ π₂` come from. -/
def diagonalPairHom2 : E × E →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) E where
  toFun pr := cStarDiagonal2 pr.1 pr.2
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CStarMatrix.mul_apply, Fin.sum_univ_two]
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CStarMatrix.zero_apply]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CStarMatrix.add_apply]
  commutes' z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.algebraMap_eq_smul_one, CStarMatrix.smul_apply]
  map_star' x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CStarMatrix.star_apply]

@[simp] theorem diagonalPairHom2_apply (pr : E × E) :
    diagonalPairHom2 pr = cStarDiagonal2 pr.1 pr.2 := rfl

/-- **The diagonal of a pair is contractive for the product norm.**  It is a
`*`-homomorphism of C-star algebras, and the C-star norm of `E × E` is the
maximum of the two coordinate norms. -/
theorem norm_diagonalPairHom2_le (pr : E × E) :
    ‖(diagonalPairHom2 pr : CStarMatrix (Fin 2) (Fin 2) E)‖
      ≤ max ‖pr.1‖ ‖pr.2‖ := by
  have hle : ‖(diagonalPairHom2 pr : CStarMatrix (Fin 2) (Fin 2) E)‖ ≤ ‖pr‖ :=
    NonUnitalStarAlgHom.norm_apply_le
      (diagonalPairHom2 :
        E × E →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) E).toNonUnitalStarAlgHom pr
  rwa [Prod.norm_def] at hle

/-- The diagonal entries of `diag(a, b)`, read off the two-element vector. -/
theorem diagonalPairHom2_entry_self (pr : E × E) (i : Fin 2) :
    (diagonalPairHom2 pr : CStarMatrix (Fin 2) (Fin 2) E) i i
      = ![pr.1, pr.2] i := by
  show (cStarDiagonal2 pr.1 pr.2 : CStarMatrix (Fin 2) (Fin 2) E) i i
    = ![pr.1, pr.2] i
  fin_cases i
  · exact cStarDiagonal2_apply_zero_zero pr.1 pr.2
  · exact cStarDiagonal2_apply_one_one pr.1 pr.2

/-- The off-diagonal entries of `diag(a, b)`. -/
theorem diagonalPairHom2_entry_ne (pr : E × E) {i j : Fin 2} (hij : i ≠ j) :
    (diagonalPairHom2 pr : CStarMatrix (Fin 2) (Fin 2) E) i j = 0 := by
  show (cStarDiagonal2 pr.1 pr.2 : CStarMatrix (Fin 2) (Fin 2) E) i j = 0
  fin_cases i
  · fin_cases j
    · exact absurd rfl hij
    · exact cStarDiagonal2_apply_zero_one pr.1 pr.2
  · fin_cases j
    · exact cStarDiagonal2_apply_one_zero pr.1 pr.2
    · exact absurd rfl hij

end DiagonalPair

/-! ## The paired representation -/

section PairRepresentation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- **Shulman's `ρ₁ = π₁ ⊕ π₂`.**  Two representations on `H`, read as one
representation on `H ⊕ H` by putting them on the diagonal. -/
def pairRep {B : Type} [CStarAlgebra B] (ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    B →⋆ₐ[ℂ] (BlockSpace H 2 →L[ℂ] BlockSpace H 2) :=
  (hBlockOpHom (E := H) (n := 2)).comp
    (diagonalPairHom2.comp (starAlgHomPair ρ₁ ρ₂))

@[simp] theorem pairRep_apply {B : Type} [CStarAlgebra B]
    (ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (b : B) :
    pairRep ρ₁ ρ₂ b = hBlockOp (diagonalPairHom2 (ρ₁ b, ρ₂ b)) := rfl

end PairRepresentation

/-! ## The entries of a paired sequence -/

section PairEntries

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- **The entries of a paired sequence converge.**  The `(0,0)` entry is
`ι n (xₙ)` and the `(1,1)` entry is `ι n (yₙ)`; the off-diagonal entries are
`0`.  The diagonal case is stated through `![·, ·]` so that the rewriting
happens at an abstract index and only the final `exact` is a case split. -/
theorem tendsto_diagonalPairHom2_entry
    (x y : StarStrong.BoundedStarSequence A) {S T : H →L[ℂ] H}
    (hS : ∀ v : H, Tendsto (fun n ↦ ι n (x n) v) atTop (𝓝 (S v)))
    (hT : ∀ v : H, Tendsto (fun n ↦ ι n (y n) v) atTop (𝓝 (T v)))
    (i j : Fin 2) (v : H) :
    Tendsto (fun n ↦ ((CStarMatrix.mapₙₐ (ι n))
        (diagonalPairHom2 ((x n, y n) : A n × A n) :
          CStarMatrix (Fin 2) (Fin 2) (A n)) i j) v) atTop
      (𝓝 (((diagonalPairHom2 ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H)) :
        CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i j) v)) := by
  by_cases hij : i = j
  · subst hij
    have hL : (fun n ↦ ((CStarMatrix.mapₙₐ (ι n))
          (diagonalPairHom2 ((x n, y n) : A n × A n) :
            CStarMatrix (Fin 2) (Fin 2) (A n)) i i) v)
        = fun n ↦ ι n (![x n, y n] i) v := by
      funext n
      have hentry : (diagonalPairHom2 ((x n, y n) : A n × A n) :
          CStarMatrix (Fin 2) (Fin 2) (A n)) i i = ![x n, y n] i :=
        diagonalPairHom2_entry_self ((x n, y n) : A n × A n) i
      rw [mapₙₐ_entry, hentry]
    have hR : ((diagonalPairHom2 ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H)) :
        CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i i) v = (![S, T] i) v := by
      rw [diagonalPairHom2_entry_self ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H)) i]
    rw [hL, hR]
    fin_cases i
    · exact hS v
    · exact hT v
  · have hL : (fun n ↦ ((CStarMatrix.mapₙₐ (ι n))
          (diagonalPairHom2 ((x n, y n) : A n × A n) :
            CStarMatrix (Fin 2) (Fin 2) (A n)) i j) v)
        = fun _ : ℕ ↦ (0 : H) := by
      funext n
      have hentry : (diagonalPairHom2 ((x n, y n) : A n × A n) :
          CStarMatrix (Fin 2) (Fin 2) (A n)) i j = 0 :=
        diagonalPairHom2_entry_ne ((x n, y n) : A n × A n) hij
      rw [mapₙₐ_entry, hentry, map_zero, _root_.zero_apply]
    have hR : ((diagonalPairHom2 ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H)) :
        CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) i j) v = 0 := by
      rw [diagonalPairHom2_entry_ne ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H)) hij,
        _root_.zero_apply]
    rw [hL, hR]
    exact tendsto_const_nhds

end PairEntries

/-! ## The paired sequence -/

section PairSequence

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)]
variable [∀ n, PartialOrder (A n)] [∀ n, StarOrderedRing (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- **The paired sequence** `n ↦ diag(xₙ, yₙ)`. -/
def doubledPairSeq (x y : StarStrong.BoundedStarSequence A) :
    StarStrong.BoundedStarSequence (fun n ↦ DoubledModel A n) :=
  ⟨fun n ↦ diagonalPairHom2 ((x n, y n) : A n × A n),
    memℓp_infty ⟨max ‖x‖ ‖y‖, by
      rintro _ ⟨n, rfl⟩
      exact (norm_diagonalPairHom2_le ((x n, y n) : A n × A n)).trans
        (max_le_max (lp.norm_apply_le_norm ENNReal.top_ne_zero x n)
          (lp.norm_apply_le_norm ENNReal.top_ne_zero y n))⟩⟩

@[simp] theorem doubledPairSeq_apply (x y : StarStrong.BoundedStarSequence A)
    (n : ℕ) : (doubledPairSeq (A := A) x y) n
      = diagonalPairHom2 ((x n, y n) : A n × A n) := rfl

theorem doubledPairSeq_sub (x y x' y' : StarStrong.BoundedStarSequence A) :
    doubledPairSeq (A := A) (x - x') (y - y')
      = doubledPairSeq x y - doubledPairSeq x' y' := by
  apply lp.ext
  funext n
  exact map_sub (diagonalPairHom2 (E := A n)) ((x n, y n) : A n × A n)
    ((x' n, y' n) : A n × A n)

-- There is deliberately no `doubledPairSeq_smul` here.  Writing `z • y` with
-- `y : lp (fun n ↦ DoubledModel A n) ∞` in a *statement* opens a bare
-- `SMul ℂ (lp …)` goal, whose search walks the whole `CStarMatrix` tower and
-- overruns the instance budget; `Analysis/ShulmanFillNormingExistentialLiftDouble`
-- carries the same note.  The homomorphism below supplies the same equation
-- inside a proof for free, because `map_smul` reads the scalar action off its
-- own type instead of opening a goal.

/-- **The paired sequence map, as a `*`-homomorphism of the bounded products.**
Its only role is to carry the scalar action: `map_smul doubledPairSeqHom` is
how the `tendsto_smul` clause of `doubleLR` gets `diag(z • x, z • y) =
z • diag(x, y)` without naming the scalar action on the doubled product. -/
def doubledPairSeqHom :
    StarStrong.BoundedStarSequence A × StarStrong.BoundedStarSequence A →⋆ₙₐ[ℂ]
      StarStrong.BoundedStarSequence (fun n ↦ DoubledModel A n) where
  toFun p := doubledPairSeq p.1 p.2
  map_zero' := by
    apply lp.ext
    funext n
    exact map_zero (diagonalPairHom2 (E := A n))
  map_add' p q := by
    apply lp.ext
    funext n
    exact map_add (diagonalPairHom2 (E := A n)) ((p.1 n, p.2 n) : A n × A n)
      ((q.1 n, q.2 n) : A n × A n)
  map_mul' p q := by
    apply lp.ext
    funext n
    exact map_mul (diagonalPairHom2 (E := A n)) ((p.1 n, p.2 n) : A n × A n)
      ((q.1 n, q.2 n) : A n × A n)
  map_smul' z p := by
    apply lp.ext
    funext n
    exact map_smul (diagonalPairHom2 (E := A n)) z ((p.1 n, p.2 n) : A n × A n)
  map_star' p := by
    apply lp.ext
    funext n
    exact map_star (diagonalPairHom2 (E := A n)) ((p.1 n, p.2 n) : A n × A n)

@[simp] theorem doubledPairSeqHom_apply
    (x y : StarStrong.BoundedStarSequence A) :
    doubledPairSeqHom (A := A) (x, y) = doubledPairSeq x y := rfl

theorem doubledPairSeq_mul (x y x' y' : StarStrong.BoundedStarSequence A) :
    doubledPairSeq (A := A) (x * x') (y * y')
      = doubledPairSeq x y * doubledPairSeq x' y' := by
  apply lp.ext
  funext n
  exact map_mul (diagonalPairHom2 (E := A n)) ((x n, y n) : A n × A n)
    ((x' n, y' n) : A n × A n)

theorem doubledPairSeq_star (x y : StarStrong.BoundedStarSequence A) :
    doubledPairSeq (A := A) (star x) (star y) = star (doubledPairSeq x y) := by
  apply lp.ext
  funext n
  exact map_star (diagonalPairHom2 (E := A n)) ((x n, y n) : A n × A n)

/-- **The paired sequence map is contractive for the maximum.** -/
theorem norm_doubledPairSeq_le (x y : StarStrong.BoundedStarSequence A) :
    ‖doubledPairSeq (A := A) x y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun n ↦
    (norm_diagonalPairHom2_le ((x n, y n) : A n × A n)).trans
      (max_le_max (lp.norm_apply_le_norm ENNReal.top_ne_zero x n)
        (lp.norm_apply_le_norm ENNReal.top_ne_zero y n))

/-- **The paired sequence converges strongly to the paired limit.** -/
theorem tendsto_doubledPairSeq_apply (x y : StarStrong.BoundedStarSequence A)
    {S T : H →L[ℂ] H}
    (hS : ∀ v : H, Tendsto (fun n ↦ ι n (x n) v) atTop (𝓝 (S v)))
    (hT : ∀ v : H, Tendsto (fun n ↦ ι n (y n) v) atTop (𝓝 (T v)))
    (w : BlockSpace H 2) :
    Tendsto (fun n ↦ doubledIota ι n ((doubledPairSeq (A := A) x y) n) w) atTop
      (𝓝 (hBlockOp (diagonalPairHom2
        ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H))) w)) := by
  have key : Tendsto
      (fun n ↦ hBlockOp ((CStarMatrix.mapₙₐ (ι n))
        (diagonalPairHom2 ((x n, y n) : A n × A n) :
          CStarMatrix (Fin 2) (Fin 2) (A n))) w) atTop
      (𝓝 (hBlockOp (diagonalPairHom2
        ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H))) w)) :=
    tendsto_hBlockOp_of_coord
      (fun i j z ↦ tendsto_diagonalPairHom2_entry ι x y hS hT i j z) w
  exact key

/-- **The `*`-strong limit of a paired sequence is the paired limit.** -/
theorem isStarStrongLimit_doubledPairSeq
    (x y : StarStrong.BoundedStarSequence A) {S T : H →L[ℂ] H}
    (hS : StarStrong.IsStarStrongLimit (fun n ↦ ι n (x n)) S)
    (hT : StarStrong.IsStarStrongLimit (fun n ↦ ι n (y n)) T) :
    StarStrong.IsStarStrongLimit
      (fun n ↦ doubledIota ι n ((doubledPairSeq (A := A) x y) n))
      (hBlockOp (diagonalPairHom2 ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H)))) := by
  refine ⟨fun w ↦ tendsto_doubledPairSeq_apply ι x y hS.1 hT.1 w, fun w ↦ ?_⟩
  have hstar : ∀ (u : StarStrong.BoundedStarSequence A) (R : H →L[ℂ] H),
      (∀ z : H, Tendsto (fun n ↦ (star (ι n (u n))) z) atTop (𝓝 ((star R) z))) →
      ∀ z : H, Tendsto
        (fun n ↦ ι n ((star u : StarStrong.BoundedStarSequence A) n) z) atTop
        (𝓝 ((star R) z)) := by
    intro u R hu z
    have hfun : (fun n ↦ ι n ((star u : StarStrong.BoundedStarSequence A) n) z)
        = fun n ↦ (star (ι n (u n))) z := by
      funext n
      have h : ι n ((star u : StarStrong.BoundedStarSequence A) n)
          = star (ι n (u n)) := map_star (ι n) (u n)
      rw [h]
    rw [hfun]
    exact hu z
  have key := tendsto_doubledPairSeq_apply ι
    (star x : StarStrong.BoundedStarSequence A)
    (star y : StarStrong.BoundedStarSequence A)
    (hstar x S hS.2) (hstar y T hT.2) w
  have hL : (fun n ↦ doubledIota ι n ((doubledPairSeq (A := A)
        (star x : StarStrong.BoundedStarSequence A)
        (star y : StarStrong.BoundedStarSequence A)) n) w)
      = fun n ↦
        (star (doubledIota ι n ((doubledPairSeq (A := A) x y) n))) w := by
    funext n
    have h1 : (doubledPairSeq (A := A)
        (star x : StarStrong.BoundedStarSequence A)
        (star y : StarStrong.BoundedStarSequence A)) n
        = star ((doubledPairSeq (A := A) x y) n) :=
      map_star (diagonalPairHom2 (E := A n)) ((x n, y n) : A n × A n)
    have h : doubledIota ι n ((doubledPairSeq (A := A)
        (star x : StarStrong.BoundedStarSequence A)
        (star y : StarStrong.BoundedStarSequence A)) n)
        = star (doubledIota ι n ((doubledPairSeq (A := A) x y) n)) := by
      rw [h1, map_star]
    rw [h]
  have hR : hBlockOp (diagonalPairHom2
        ((star S, star T) : (H →L[ℂ] H) × (H →L[ℂ] H)))
      = star (hBlockOp (diagonalPairHom2
        ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H)))) := by
    have h1 : (diagonalPairHom2
        ((star S, star T) : (H →L[ℂ] H) × (H →L[ℂ] H)) :
          CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H))
        = star (diagonalPairHom2
          ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H))) :=
      map_star (diagonalPairHom2 (E := H →L[ℂ] H))
        ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H))
    rw [h1]
    exact hBlockOp_star _
  rw [hL, hR] at key
  exact key

/-! ## The bridge, and the flip -/

section Unital

variable [∀ n, Nontrivial (A n)]

/-- The paired sequence of the two units is the unit. -/
theorem doubledPairSeq_one : doubledPairSeq (A := A) 1 1 = 1 := by
  apply lp.ext
  funext n
  exact map_one (diagonalHom2 (E := A n))

/-- **A paired sequence lies in the doubled `𝒟`.** -/
theorem doubledPairSeq_mem
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    (x y : StarStrong.BoundedStarSequence A)
    (hx : x ∈ StarStrong.starStrongSubalgebra ι hnorm hone)
    (hy : y ∈ StarStrong.starStrongSubalgebra ι hnorm hone) :
    doubledPairSeq (A := A) x y ∈
      StarStrong.starStrongSubalgebra (doubledIota ι) (doubled_norm_le ι)
        (doubled_hone ι hone) := by
  obtain ⟨S, hS⟩ : ∃ S : H →L[ℂ] H,
    StarStrong.IsStarStrongLimit (fun n ↦ ι n (x n)) S := hx
  obtain ⟨T, hT⟩ : ∃ T : H →L[ℂ] H,
    StarStrong.IsStarStrongLimit (fun n ↦ ι n (y n)) T := hy
  exact ⟨hBlockOp (diagonalPairHom2 ((S, T) : (H →L[ℂ] H) × (H →L[ℂ] H))),
    isStarStrongLimit_doubledPairSeq ι x y hS hT⟩

namespace StarStrongAsymptoticLift

/-- **The pair bridge.**  Two asymptotic lifts of `ρ₁` and `ρ₂` into one `𝒟`
give an asymptotic lift of `pairRep ρ₁ ρ₂` into the doubled `𝒟`.

Each defect of the paired family is the paired sequence of the two defects, and
`norm_doubledPairSeq_le` bounds it by their maximum, which `Filter.Tendsto.max`
sends to zero.  The lifting clause stays exact. -/
def doubleLR {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
    {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
    {B : Type} [CStarAlgebra B] {ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂) :
    StarStrongAsymptoticLift (doubledIota ι) (doubled_norm_le ι)
      (doubled_hone ι hone) (pairRep ρ₁ ρ₂) where
  toFun t b := doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b)
  mem t b := doubledPairSeq_mem ι hnorm hone (φ₁.toFun t b) (φ₂.toFun t b)
    (φ₁.mem t b) (φ₂.mem t b)
  norm_le t b := (norm_doubledPairSeq_le _ _).trans
    (max_le (φ₁.norm_le t b) (φ₂.norm_le t b))
  tendsto_add b c := by
    have hmax : Tendsto (fun t ↦ max
        ‖φ₁.toFun t (b + c) - φ₁.toFun t b - φ₁.toFun t c‖
        ‖φ₂.toFun t (b + c) - φ₂.toFun t b - φ₂.toFun t c‖) atTop (𝓝 0) := by
      have h := (φ₁.tendsto_add b c).max (φ₂.tendsto_add b c)
      rwa [max_self] at h
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) hmax
    have h : doubledPairSeq (A := A) (φ₁.toFun t (b + c)) (φ₂.toFun t (b + c))
          - doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b)
          - doubledPairSeq (A := A) (φ₁.toFun t c) (φ₂.toFun t c)
        = doubledPairSeq (A := A)
            (φ₁.toFun t (b + c) - φ₁.toFun t b - φ₁.toFun t c)
            (φ₂.toFun t (b + c) - φ₂.toFun t b - φ₂.toFun t c) := by
      rw [doubledPairSeq_sub, doubledPairSeq_sub]
    rw [h]
    exact norm_doubledPairSeq_le _ _
  tendsto_smul z b := by
    have hmax : Tendsto (fun t ↦ max
        ‖φ₁.toFun t (z • b) - z • φ₁.toFun t b‖
        ‖φ₂.toFun t (z • b) - z • φ₂.toFun t b‖) atTop (𝓝 0) := by
      have h := (φ₁.tendsto_smul z b).max (φ₂.tendsto_smul z b)
      rwa [max_self] at h
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) hmax
    -- `hsm` is obtained, never stated: `map_smul` builds the scalar action into
    -- its own conclusion, so the expensive `SMul ℂ (lp (fun n ↦ DoubledModel A n) ∞)`
    -- goal is never opened.
    have hsm := map_smul (doubledPairSeqHom (A := A)) z
      ((φ₁.toFun t b, φ₂.toFun t b) :
        StarStrong.BoundedStarSequence A × StarStrong.BoundedStarSequence A)
    rw [show (z • ((φ₁.toFun t b, φ₂.toFun t b) :
        StarStrong.BoundedStarSequence A × StarStrong.BoundedStarSequence A))
        = (z • φ₁.toFun t b, z • φ₂.toFun t b) from rfl] at hsm
    simp only [doubledPairSeqHom_apply] at hsm
    rw [← hsm, ← doubledPairSeq_sub]
    exact norm_doubledPairSeq_le _ _
  tendsto_mul b c := by
    have hmax : Tendsto (fun t ↦ max
        ‖φ₁.toFun t (b * c) - φ₁.toFun t b * φ₁.toFun t c‖
        ‖φ₂.toFun t (b * c) - φ₂.toFun t b * φ₂.toFun t c‖) atTop (𝓝 0) := by
      have h := (φ₁.tendsto_mul b c).max (φ₂.tendsto_mul b c)
      rwa [max_self] at h
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) hmax
    have h : doubledPairSeq (A := A) (φ₁.toFun t (b * c)) (φ₂.toFun t (b * c))
          - doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b)
            * doubledPairSeq (A := A) (φ₁.toFun t c) (φ₂.toFun t c)
        = doubledPairSeq (A := A)
            (φ₁.toFun t (b * c) - φ₁.toFun t b * φ₁.toFun t c)
            (φ₂.toFun t (b * c) - φ₂.toFun t b * φ₂.toFun t c) := by
      rw [doubledPairSeq_sub, doubledPairSeq_mul]
    rw [h]
    exact norm_doubledPairSeq_le _ _
  tendsto_star b := by
    have hmax : Tendsto (fun t ↦ max
        ‖φ₁.toFun t (star b) - star (φ₁.toFun t b)‖
        ‖φ₂.toFun t (star b) - star (φ₂.toFun t b)‖) atTop (𝓝 0) := by
      have h := (φ₁.tendsto_star b).max (φ₂.tendsto_star b)
      rwa [max_self] at h
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) hmax
    have h : doubledPairSeq (A := A) (φ₁.toFun t (star b))
            (φ₂.toFun t (star b))
          - star (doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b))
        = doubledPairSeq (A := A) (φ₁.toFun t (star b) - star (φ₁.toFun t b))
            (φ₂.toFun t (star b) - star (φ₂.toFun t b)) := by
      rw [doubledPairSeq_sub, doubledPairSeq_star]
    rw [h]
    exact norm_doubledPairSeq_le _ _
  tendsto_one := by
    have hmax : Tendsto (fun t ↦ max ‖φ₁.toFun t (1 : B) - 1‖
        ‖φ₂.toFun t (1 : B) - 1‖) atTop (𝓝 0) := by
      have h := φ₁.tendsto_one.max φ₂.tendsto_one
      rwa [max_self] at h
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) hmax
    have h : doubledPairSeq (A := A) (φ₁.toFun t (1 : B)) (φ₂.toFun t (1 : B))
          - 1
        = doubledPairSeq (A := A) (φ₁.toFun t (1 : B) - 1)
            (φ₂.toFun t (1 : B) - 1) := by
      rw [doubledPairSeq_sub, doubledPairSeq_one]
    rw [h]
    exact norm_doubledPairSeq_le _ _
  lift t b := by
    have hS : StarStrong.IsStarStrongLimit
        (fun n ↦ ι n ((φ₁.toFun t b) n)) (ρ₁ b) := by
      have h := StarStrong.starStrongLimit_spec ι hnorm hone
        ⟨φ₁.toFun t b, φ₁.mem t b⟩
      rwa [φ₁.starStrongLimit_toFun t b] at h
    have hT : StarStrong.IsStarStrongLimit
        (fun n ↦ ι n ((φ₂.toFun t b) n)) (ρ₂ b) := by
      have h := StarStrong.starStrongLimit_spec ι hnorm hone
        ⟨φ₂.toFun t b, φ₂.mem t b⟩
      rwa [φ₂.starStrongLimit_toFun t b] at h
    exact StarStrong.starStrongLimit_eq (doubledIota ι) (doubled_norm_le ι)
      (doubled_hone ι hone) _
      (isStarStrongLimit_doubledPairSeq ι (φ₁.toFun t b) (φ₂.toFun t b) hS hT)

@[simp] theorem doubleLR_toFun {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
    {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
    {B : Type} [CStarAlgebra B] {ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂) (t : ℕ) (b : B) :
    (doubleLR ι φ₁ φ₂).toFun t b
      = doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b) := rfl

end StarStrongAsymptoticLift

/-! ## The flip swaps the two legs -/

/-- **The flip conjugates a paired sequence into the swapped one.**
Coordinatewise this is `ShulmanFill.flip2_conj_diagonal2`. -/
theorem doubledFlipSeq_conj_doubledPairSeq
    (x y : StarStrong.BoundedStarSequence A) :
    doubledFlipSeq (A := A) * doubledPairSeq (A := A) x y
        * star (doubledFlipSeq (A := A))
      = doubledPairSeq (A := A) y x := by
  apply lp.ext
  funext n
  show (flip2 : DoubledModel A n) * cStarDiagonal2 (x n) (y n) * star flip2
    = cStarDiagonal2 (y n) (x n)
  rw [star_flip2, flip2_conj_diagonal2]

/-- **The second doubled lift is free.**  Conjugating `doubleLR φ₁ φ₂` by the
flip gives `doubleLR φ₂ φ₁`, exactly and term by term.  This is the step for
which the paper needs the Halmos dilation of Lemma 9. -/
theorem conjugate_doubleLR_toFun
    (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    {B : Type} [CStarAlgebra B] {ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂) (t : ℕ) (b : B) :
    (StarStrongAsymptoticLift.conjugate (doubledFlipSeq (A := A))
        (doubledFlipSeq_mem ι hone) (doubledFlipSeq_star_mul_self (A := A))
        (doubledFlipSeq_mul_star_self (A := A))
        (norm_doubledFlipSeq_le_one (A := A))
        (StarStrongAsymptoticLift.doubleLR ι φ₁ φ₂)).toFun t b
      = (StarStrongAsymptoticLift.doubleLR ι φ₂ φ₁).toFun t b := by
  show doubledFlipSeq (A := A)
      * doubledPairSeq (A := A) (φ₁.toFun t b) (φ₂.toFun t b)
      * star (doubledFlipSeq (A := A))
    = doubledPairSeq (A := A) (φ₂.toFun t b) (φ₁.toFun t b)
  exact doubledFlipSeq_conj_doubledPairSeq (φ₁.toFun t b) (φ₂.toFun t b)

/-- **The flip swaps the paired representation.**  `Ad (q U) ∘ pairRep ρ₁ ρ₂`
is `pairRep ρ₂ ρ₁`, which is Shulman's `ρ₁ = u* ρ₂ u`. -/
theorem pairRep_conjugate_eq
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))
    {B : Type} [CStarAlgebra B] (ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (unitaryConj (D := BlockSpace H 2 →L[ℂ] BlockSpace H 2)
        (limitUnitaryBundled (doubledFlipSeq (A := A))
          (doubledFlipSeq_mem ι hone) (doubledFlipSeq_star_mul_self (A := A))
          (doubledFlipSeq_mul_star_self (A := A)))).comp (pairRep ρ₁ ρ₂)
      = pairRep ρ₂ ρ₁ := by
  have hu : ((limitUnitaryBundled (doubledFlipSeq (A := A))
        (doubledFlipSeq_mem ι hone) (doubledFlipSeq_star_mul_self (A := A))
        (doubledFlipSeq_mul_star_self (A := A)) :
          unitary (BlockSpace H 2 →L[ℂ] BlockSpace H 2)) :
        BlockSpace H 2 →L[ℂ] BlockSpace H 2)
      = hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) :=
    limitUnitary_doubledFlipSeq ι hone
  have hstar :
      star (hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)))
        = hBlockOp (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) := by
    rw [← hBlockOp_star, star_flip2]
  apply StarAlgHom.ext
  intro b
  show unitaryConj (D := BlockSpace H 2 →L[ℂ] BlockSpace H 2)
      (limitUnitaryBundled (doubledFlipSeq (A := A))
        (doubledFlipSeq_mem ι hone) (doubledFlipSeq_star_mul_self (A := A))
        (doubledFlipSeq_mul_star_self (A := A))) (pairRep ρ₁ ρ₂ b)
    = pairRep ρ₂ ρ₁ b
  rw [unitaryConj_apply, hu, pairRep_apply, pairRep_apply, hstar,
    ← hBlockOp_mul, ← hBlockOp_mul]
  congr 1
  show (flip2 : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H))
      * cStarDiagonal2 (ρ₁ b) (ρ₂ b) * flip2
    = cStarDiagonal2 (ρ₂ b) (ρ₁ b)
  rw [flip2_conj_diagonal2]

end Unital

end PairSequence

end

end ShulmanFill
end GroupApproximation
