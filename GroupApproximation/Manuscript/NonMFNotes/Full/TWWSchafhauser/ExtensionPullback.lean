import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Algebra.Star.Subalgebra

/-!
# The pullback of an extension along a ⋆-homomorphism

Lane TWWSchafhauser-3c (work order WO-TWWCore-3, piece 3c).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378).  It
cites Tikuisis--White--Winter, *Quasidiagonality of nuclear C⋆-algebras*,
Ann. of Math. (2) **185** (2017), Theorem A, through C. Schafhauser, *A new
proof of the Tikuisis--White--Winter theorem*, J. reine angew. Math. **759**
(2020), §3--4.

A C⋆-algebra extension `0 → J → E → Q → 0` is presented here by its quotient map
`π : E →⋆ₐ[ℂ] Q`; the ideal is `ker π`.  Given a ⋆-homomorphism `θ : S → Q`, the
**pulled-back extension** is

  `P = { (s, e) ∈ S × E | θ s = π e }`,

with quotient map `P → S`, `(s, e) ↦ s`.  Its kernel is `0 × ker π`, so `P` is an
extension of `S` by the same ideal (Schafhauser 2020, §3, the extension `E_θ`).
A splitting of `P → S` is the same thing as a lift of `θ` through `π`.  This is
the form in which the obstruction theory of §4--5 is applied.

Proved here, with no hypotheses:

* `extensionPullback π θ` is a closed star subalgebra of `S × E`, so it is a
  C⋆-algebra.
* `extensionPullbackFst`, `extensionPullbackSnd` are the two projections, and
  `extensionPullback_comm` is the commuting square.
* `extensionPullbackFst_surjective`: if `π` is onto, so is `P → S`.
* `extensionPullbackSplitting`: a ⋆-homomorphic lift `ψ` of `θ` gives a splitting
  of `P → S`.  Conversely, `lifts_of_extensionPullbackSplitting` recovers a lift
  from a splitting.
* `extensionPullbackLinearSplitting`: a linear lift of `θ` gives a linear
  splitting.  This is the shape of nuclear liftability, where the lift is ucp.
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

/-- **The pulled-back extension** `P = {(s, e) | θ s = π e} ⊆ S × E`
(Schafhauser 2020, §3). -/
def extensionPullback {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E] [CStarAlgebra Q]
    (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) : StarSubalgebra ℂ (S × E) :=
  StarAlgHom.equalizer (θ.comp (StarAlgHom.fst ℂ S E)) (π.comp (StarAlgHom.snd ℂ S E))

theorem mem_extensionPullback {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (x : S × E) :
    x ∈ extensionPullback π θ ↔ θ x.1 = π x.2 :=
  Iff.rfl

/-- The pulled-back extension is norm closed, because star-algebra homomorphisms
between C⋆-algebras are contractive. -/
theorem isClosed_extensionPullback {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) :
    IsClosed ((extensionPullback π θ : StarSubalgebra ℂ (S × E)) : Set (S × E)) := by
  have hθ : Continuous θ :=
    AddMonoidHomClass.continuous_of_bound θ 1 fun a => by
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le θ a
  have hπ : Continuous π :=
    AddMonoidHomClass.continuous_of_bound π 1 fun a => by
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le π a
  have hset : ((extensionPullback π θ : StarSubalgebra ℂ (S × E)) : Set (S × E))
      = {x : S × E | θ x.1 = π x.2} :=
    Set.ext fun x => mem_extensionPullback π θ x
  rw [hset]
  exact isClosed_eq (hθ.comp continuous_fst) (hπ.comp continuous_snd)

instance extensionPullback_isClosed {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] {π : E →⋆ₐ[ℂ] Q} {θ : S →⋆ₐ[ℂ] Q} :
    IsClosed ((extensionPullback π θ : StarSubalgebra ℂ (S × E)) : Set (S × E)) :=
  isClosed_extensionPullback π θ

/-- The quotient map `P → S` of the pulled-back extension. -/
def extensionPullbackFst {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) :
    extensionPullback π θ →⋆ₐ[ℂ] S :=
  (StarAlgHom.fst ℂ S E).comp (extensionPullback π θ).subtype

/-- The map `P → E` of the pulled-back extension. -/
def extensionPullbackSnd {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) :
    extensionPullback π θ →⋆ₐ[ℂ] E :=
  (StarAlgHom.snd ℂ S E).comp (extensionPullback π θ).subtype

theorem extensionPullbackFst_apply {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (x : extensionPullback π θ) :
    extensionPullbackFst π θ x = (x : S × E).1 :=
  rfl

theorem extensionPullbackSnd_apply {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (x : extensionPullback π θ) :
    extensionPullbackSnd π θ x = (x : S × E).2 :=
  rfl

/-- **The pullback square commutes:** `θ ∘ fst = π ∘ snd` on `P`. -/
theorem extensionPullback_comm {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (x : extensionPullback π θ) :
    θ (extensionPullbackFst π θ x) = π (extensionPullbackSnd π θ x) :=
  (mem_extensionPullback π θ (x : S × E)).1 x.2

/-- **The pulled-back extension is an extension of `S`:** if `π` is onto, so is
`P → S`. -/
theorem extensionPullbackFst_surjective {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (hπ : Function.Surjective π) :
    Function.Surjective (extensionPullbackFst π θ) := by
  intro s
  obtain ⟨e, he⟩ := hπ (θ s)
  exact ⟨⟨(s, e), (mem_extensionPullback π θ (s, e)).2 he.symm⟩, rfl⟩

/-- The kernel of `P → S` is `0 × ker π`: an element of `P` with first coordinate
`0` has second coordinate in `ker π`. -/
theorem extensionPullbackSnd_mem_ker {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (x : extensionPullback π θ)
    (hx : extensionPullbackFst π θ x = 0) : π (extensionPullbackSnd π θ x) = 0 := by
  rw [← extensionPullback_comm π θ x, hx, map_zero]

/-- Every element of `ker π` gives an element `(0, j)` of `P`. -/
def extensionPullbackKernelElement {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (j : E) (hj : π j = 0) :
    extensionPullback π θ :=
  ⟨(0, j), (mem_extensionPullback π θ (0, j)).2 ((map_zero θ).trans hj.symm)⟩

theorem extensionPullbackFst_kernelElement {S E Q : Type*} [CStarAlgebra S]
    [CStarAlgebra E] [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (j : E)
    (hj : π j = 0) :
    extensionPullbackFst π θ (extensionPullbackKernelElement π θ j hj) = 0 :=
  rfl

theorem extensionPullbackSnd_kernelElement {S E Q : Type*} [CStarAlgebra S]
    [CStarAlgebra E] [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (j : E)
    (hj : π j = 0) :
    extensionPullbackSnd π θ (extensionPullbackKernelElement π θ j hj) = j :=
  rfl

/-- **A lift of `θ` splits the pulled-back extension.**  If `ψ : S → E` is a
⋆-homomorphism with `π ∘ ψ = θ`, then `s ↦ (s, ψ s)` splits `P → S`. -/
def extensionPullbackSplitting {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (ψ : S →⋆ₐ[ℂ] E)
    (hψ : ∀ s, π (ψ s) = θ s) : S →⋆ₐ[ℂ] extensionPullback π θ :=
  ((StarAlgHom.id ℂ S).prod ψ).codRestrict (extensionPullback π θ) fun s =>
    (mem_extensionPullback π θ _).2 (hψ s).symm

theorem extensionPullbackFst_splitting {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (ψ : S →⋆ₐ[ℂ] E)
    (hψ : ∀ s, π (ψ s) = θ s) (s : S) :
    extensionPullbackFst π θ (extensionPullbackSplitting π θ ψ hψ s) = s :=
  rfl

theorem extensionPullbackSnd_splitting {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (ψ : S →⋆ₐ[ℂ] E)
    (hψ : ∀ s, π (ψ s) = θ s) (s : S) :
    extensionPullbackSnd π θ (extensionPullbackSplitting π θ ψ hψ s) = ψ s :=
  rfl

/-- **A splitting of the pulled-back extension is a lift of `θ`.**  If `σ` splits
`P → S`, then `snd ∘ σ` lifts `θ` through `π`. -/
theorem lifts_of_extensionPullbackSplitting {S E Q : Type*} [CStarAlgebra S]
    [CStarAlgebra E] [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q)
    (σ : S →⋆ₐ[ℂ] extensionPullback π θ) (hσ : ∀ s, extensionPullbackFst π θ (σ s) = s)
    (s : S) : π (extensionPullbackSnd π θ (σ s)) = θ s := by
  rw [← extensionPullback_comm π θ (σ s), hσ s]

/-- **A linear lift of `θ` gives a linear splitting of the pulled-back extension.**
When the lift is completely positive, this is the nuclear liftability of the
extension. -/
def extensionPullbackLinearSplitting {S E Q : Type*} [CStarAlgebra S] [CStarAlgebra E]
    [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (L : S →ₗ[ℂ] E)
    (hL : ∀ s, π (L s) = θ s) : S →ₗ[ℂ] extensionPullback π θ where
  toFun s := ⟨(s, L s), (mem_extensionPullback π θ (s, L s)).2 (hL s).symm⟩
  map_add' a b := by
    apply Subtype.ext
    exact Prod.ext rfl (map_add L a b)
  map_smul' c a := by
    apply Subtype.ext
    exact Prod.ext rfl (map_smul L c a)

theorem extensionPullbackFst_linearSplitting {S E Q : Type*} [CStarAlgebra S]
    [CStarAlgebra E] [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (L : S →ₗ[ℂ] E)
    (hL : ∀ s, π (L s) = θ s) (s : S) :
    extensionPullbackFst π θ (extensionPullbackLinearSplitting π θ L hL s) = s :=
  rfl

theorem extensionPullbackSnd_linearSplitting {S E Q : Type*} [CStarAlgebra S]
    [CStarAlgebra E] [CStarAlgebra Q] (π : E →⋆ₐ[ℂ] Q) (θ : S →⋆ₐ[ℂ] Q) (L : S →ₗ[ℂ] E)
    (hL : ∀ s, π (L s) = θ s) (s : S) :
    extensionPullbackSnd π θ (extensionPullbackLinearSplitting π θ L hL s) = L s :=
  rfl

end

end GroupApproximation.Full.TWWSchafhauser
