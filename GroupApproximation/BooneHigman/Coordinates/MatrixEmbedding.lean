import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Faithful matrix representations of rings

The coordinate step of the Boone–Higman route for linear groups replaces the coefficient ring of a
finitely generated linear group by a polynomial ring, one ring extension at a time.  Every extension
used there is free of finite rank, so it is realized by left multiplication matrices, and the steps
compose by flattening blocks.  This file records that bookkeeping.

* `MatrixEmbedding R P`: some injective unital ring homomorphism `R →+* M_N(P)` exists.
* `MatrixEmbedding.of_injective`, `MatrixEmbedding.of_basis` (left multiplication matrices along a
  finite basis) and `MatrixEmbedding.trans` (`M_N(M_M(Q)) ≅ M_{N·M}(Q)`).
* `blockRingHom n Φ : M_n(R) →+* M_{n × N}(P)` applies `Φ : R →+* M_N(P)` entrywise and flattens the
  blocks; `blockGL n Φ` is the induced map of general linear groups.  Both are injective when `Φ`
  is.  `blockGL_apply` computes the entries, so a matrix with zero entries below the diagonal and
  ones on it goes to a block matrix with zero blocks below the diagonal and identity blocks on it
  (`blockGL_apply_eq_zero`, `blockGL_apply_eq_one`).
* `exists_injective_gl`: a matrix embedding `R ↪ M_N(P)` gives an injective homomorphism
  `GL_n(R) → GL_{n·N}(P)`.
* `glMap_injective`: `Matrix.GeneralLinearGroup.map f` is injective when `f` is.
-/

namespace GroupApproximation.BooneHigman.Coordinates

open Matrix

/-- `R` embeds in a full matrix ring over `P`: some injective unital ring homomorphism
`R →+* M_N(P)` exists. -/
def MatrixEmbedding (R P : Type*) [Ring R] [CommRing P] : Prop :=
  ∃ N : ℕ, ∃ Φ : R →+* Matrix (Fin N) (Fin N) P, Function.Injective Φ

namespace MatrixEmbedding

/-- An injective ring homomorphism is a `1 × 1` matrix embedding. -/
theorem of_injective {R P : Type*} [Ring R] [CommRing P] (f : R →+* P)
    (hf : Function.Injective f) : MatrixEmbedding R P := by
  refine ⟨1, (Matrix.scalar (Fin 1) : P →+* Matrix (Fin 1) (Fin 1) P).comp f, ?_⟩
  intro x y h
  apply hf
  simpa using congrFun (congrFun h 0) 0

/-- Every commutative ring embeds in `M_1` of itself. -/
theorem refl (R : Type*) [CommRing R] : MatrixEmbedding R R :=
  of_injective (RingHom.id R) Function.injective_id

/-- An algebra that is free of finite rank embeds by left multiplication matrices. -/
theorem of_basis {P S : Type*} [CommRing P] [Ring S] [Algebra P S] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι P S) : MatrixEmbedding S P :=
  ⟨Fintype.card ι,
    (Matrix.reindexRingEquiv (R := P) (Fintype.equivFin ι)).toRingHom.comp
      (Algebra.leftMulMatrix b).toRingHom,
    (Matrix.reindexRingEquiv (R := P) (Fintype.equivFin ι)).injective.comp
      (Algebra.leftMulMatrix_injective b)⟩

/-- Matrix embeddings compose. -/
theorem trans {R P Q : Type*} [Ring R] [CommRing P] [CommRing Q] (h₁ : MatrixEmbedding R P)
    (h₂ : MatrixEmbedding P Q) : MatrixEmbedding R Q := by
  obtain ⟨N, Φ, hΦ⟩ := h₁
  obtain ⟨M, Ψ, hΨ⟩ := h₂
  exact ⟨N * M,
    (Matrix.reindexRingEquiv (R := Q) finProdFinEquiv).toRingHom.comp
      ((Matrix.compRingEquiv (Fin N) (Fin M) Q).toRingHom.comp (Ψ.mapMatrix.comp Φ)),
    (Matrix.reindexRingEquiv (R := Q) finProdFinEquiv).injective.comp
      ((Matrix.compRingEquiv (Fin N) (Fin M) Q).injective.comp
        ((Matrix.map_injective hΨ).comp hΦ))⟩

end MatrixEmbedding

section Block

variable {R P : Type*} [Ring R] [CommRing P] (n : Type*) [Fintype n] [DecidableEq n] {N : ℕ}
  (Φ : R →+* Matrix (Fin N) (Fin N) P)

/-- Apply `Φ : R →+* M_N(P)` entrywise, then flatten `M_n(M_N(P))` to `M_{n × N}(P)`. -/
def blockRingHom : Matrix n n R →+* Matrix (n × Fin N) (n × Fin N) P :=
  (Matrix.compRingEquiv n (Fin N) P).toRingHom.comp Φ.mapMatrix

theorem blockRingHom_apply (M : Matrix n n R) (i j : n) (a b : Fin N) :
    blockRingHom n Φ M (i, a) (j, b) = Φ (M i j) a b :=
  rfl

theorem blockRingHom_injective (hΦ : Function.Injective Φ) :
    Function.Injective (blockRingHom n Φ) :=
  (Matrix.compRingEquiv n (Fin N) P).injective.comp (Matrix.map_injective hΦ)

/-- The homomorphism `GL_n(R) → GL_{n × N}(P)` induced by `blockRingHom n Φ`. -/
def blockGL : GL n R →* GL (n × Fin N) P :=
  Units.map (blockRingHom n Φ).toMonoidHom

theorem blockGL_injective (hΦ : Function.Injective Φ) : Function.Injective (blockGL n Φ) :=
  Units.map_injective (blockRingHom_injective n Φ hΦ)

theorem blockGL_apply (g : GL n R) (i j : n) (a b : Fin N) :
    (blockGL n Φ g : Matrix (n × Fin N) (n × Fin N) P) (i, a) (j, b) =
      Φ ((g : Matrix n n R) i j) a b :=
  rfl

/-- A zero entry becomes a zero block. -/
theorem blockGL_apply_eq_zero {g : GL n R} {i j : n} (h : (g : Matrix n n R) i j = 0)
    (a b : Fin N) : (blockGL n Φ g : Matrix (n × Fin N) (n × Fin N) P) (i, a) (j, b) = 0 := by
  rw [blockGL_apply, h, map_zero, Matrix.zero_apply]

/-- An entry equal to one becomes an identity block. -/
theorem blockGL_apply_eq_one {g : GL n R} {i j : n} (h : (g : Matrix n n R) i j = 1)
    (a b : Fin N) : (blockGL n Φ g : Matrix (n × Fin N) (n × Fin N) P) (i, a) (j, b) =
      (1 : Matrix (Fin N) (Fin N) P) a b := by
  rw [blockGL_apply, h, map_one]

end Block

/-- A matrix embedding `R ↪ M_N(P)` gives an injective homomorphism `GL_n(R) → GL_{n·N}(P)`. -/
theorem MatrixEmbedding.exists_injective_gl {R P : Type*} [Ring R] [CommRing P]
    (h : MatrixEmbedding R P) (n : ℕ) :
    ∃ M : ℕ, ∃ ψ : GL (Fin n) R →* GL (Fin M) P, Function.Injective ψ := by
  obtain ⟨N, Φ, hΦ⟩ := h
  exact ⟨n * N,
    (Units.map (Matrix.reindexRingEquiv (R := P) finProdFinEquiv).toRingHom.toMonoidHom).comp
      (blockGL (Fin n) Φ),
    (Units.map_injective (Matrix.reindexRingEquiv (R := P) finProdFinEquiv).injective).comp
      (blockGL_injective (Fin n) Φ hΦ)⟩

/-- `Matrix.GeneralLinearGroup.map f` is injective when `f` is. -/
theorem glMap_injective {R S : Type*} [CommRing R] [CommRing S] {n : Type*} [Fintype n]
    [DecidableEq n] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := n) f) :=
  Units.map_injective (f := (RingHom.mapMatrix (m := n) f).toMonoidHom) (Matrix.map_injective hf)

end GroupApproximation.BooneHigman.Coordinates
