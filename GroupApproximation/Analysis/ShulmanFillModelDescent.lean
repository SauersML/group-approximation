import GroupApproximation.Analysis.ShulmanFillConjugationEstimate

/-!
# From asymptotic models to a corona homomorphism, and to faithfulness

This is the bridge between Shulman's Theorem 4 and the corona vocabulary the
rest of the `ShulmanFill` chain speaks.  Theorem 4 produces a *discrete
asymptotic homomorphism* — maps `φ_n` into the matrix models that are only
approximately multiplicative — and the statement that has to come out is a
genuine `*`-homomorphism into a corona.  The passage is free: the corona kills
null sequences, so a family whose algebraic defects are null descends to an
honest homomorphism.

`AsymptoticModel` below packages exactly the clauses of "contractive discrete
asymptotic homomorphism", `AsymptoticModel.toCoronaHom` is the descent, and
`toCoronaHom_injective` records what makes it faithful.

## The derivation of `ConjugatedPairFaithfulStatement`, step by step

With `D` separable MF, `C ⊆ D`, and `π = π₁ * π₂ : D *_C D → B(H)` faithful:

1. `ρ₂ = π₂ ⊕ π₁` is a `*`-homomorphism of `D` into `M₂(B(H))`.  Theorem 4
   lifts it to a contractive discrete asymptotic homomorphism `φ_k` with
   `q ∘ φ = ρ₂`.  In the vocabulary here, `φ` is an `AsymptoticModel`.
2. The flip conjugates `ρ₂` to `ρ₁` and commutes with `ρ₂(C)` exactly
   (`Analysis/ShulmanFillSymmetricDoubleFlip`).  Its lift `V_k` — Lemma 9 —
   commutes with the models only up to `1/k`.
3. Those two families agree asymptotically on `C`: this is
   `ShulmanFill.tendsto_norm_unitaryConj_sub`, proved in
   `Analysis/ShulmanFillConjugationEstimate`.
4. `toCoronaHom` below turns `φ` into a genuine `*`-homomorphism
   `Φ : D → 𝒬`, and `ShulmanFill.coronaUnitary_commutes_of_tendsto_commutator`
   turns the `V_k` into a unitary of `𝒬` commuting with `Φ(C)` **exactly**.
   So the conjugated pair `(Φ, Ad V ∘ Φ)` of
   `ShulmanFill.conjugateRepresentation` exists at this point, with no
   approximation left in it.
5. Faithfulness is the only remaining step, and it is where `𝒟` — not the
   corona — is needed.  The corona norm of `Φ(a)` is `limsup ‖φ_n(a)‖`, while
   `q` is a `*`-strong limit, so `‖q(x)‖ ≤ liminf ‖x_n‖`: the norm is weakly
   lower semicontinuous.  Hence
   `‖a‖ = ‖π(a)‖ = ‖q(Φ a)‖ ≤ liminf ‖φ_n a‖ ≤ limsup ‖φ_n a‖ = ‖Φ a‖`,
   which is the hypothesis `hlower` of `toCoronaHom_injective` — the corona
   norm of a class being the limsup of its coordinate norms is
   `norm_filterMatrixCorona_mk_eq_limsup`.  That single
   inequality is the whole use of `𝒟` in the argument: the corona alone cannot
   see it, because passing to the corona discards the limit that `q` records.
6. The descended pair evaluates the double faithfully: the evaluation and the
   descended homomorphism are two `*`-homomorphisms on the amalgam agreeing on
   both factor images, so they agree on the closure of the generated
   `*`-algebra, which is the amalgam
   (`ShulmanFill.dense_adjoin_universalCStarAmalgam`).

Steps 1 and 2 are the named inputs (Theorem 4, Lemma 9); 3, 4 and 6 are
proved in this repository; 5 is the inequality above, which is a statement
about `𝒟` and belongs with its construction.

## What Lemma 9 is still for

Theorem 4's lift is only asymptotically multiplicative, so `V_k` cannot be
obtained by conjugating a genuine homomorphism: the flip has to be lifted
through the same approximation, and that is exactly Lemma 9's job.  But note
what step 4 does with it — the descent to the corona converts "commutes up to
`1/k`" into "commutes exactly", so Lemma 9 is needed only to produce the
*sequence* `V_k`, never to control it afterwards.  A conjugated pair of
asymptotic models is therefore a genuine corona pair, with no further
hypothesis: the conjugate of an `AsymptoticModel` by a sequence of unitaries
is again an `AsymptoticModel` (conjugation preserves each defect clause, being
isometric), and `toCoronaHom` descends it.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter

noncomputable section

variable {A : Type} [CStarAlgebra A] (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-- A contractive discrete asymptotic homomorphism into the matrix models:
uniformly contractive maps whose algebraic defects are null. -/
structure AsymptoticModel where
  /-- The maps into the finite models. -/
  map : ∀ n, A → Matrix (X n) (X n) ℂ
  /-- Contractivity, as in the paper's Remark 6. -/
  contractive : ∀ n a, ‖map n a‖ ≤ ‖a‖
  /-- The zero defect is null. -/
  zero : Tendsto (fun n ↦ ‖map n 0‖) cofinite (nhds 0)
  /-- The additive defect is null. -/
  add : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a + b) - (map n a + map n b)‖) cofinite (nhds 0)
  /-- The multiplicative defect is null. -/
  mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) cofinite (nhds 0)
  /-- The scalar defect is null. -/
  smul : ∀ (c : ℂ) (a : A),
    Tendsto (fun n ↦ ‖map n (c • a) - c • map n a‖) cofinite (nhds 0)
  /-- The adjoint defect is null. -/
  star : ∀ a : A,
    Tendsto (fun n ↦ ‖map n (star a) - star (map n a)‖) cofinite (nhds 0)

namespace AsymptoticModel

variable {X}

/-- The coordinates of a model, as a bounded matrix sequence. -/
def seq (M : AsymptoticModel (A := A) X) (a : A) :
    BoundedMatrixSequence (fun n ↦ X n) :=
  ⟨fun n ↦ M.map n a, memℓp_infty ⟨‖a‖, by
    rintro _ ⟨n, rfl⟩
    exact M.contractive n a⟩⟩

@[simp] theorem seq_apply (M : AsymptoticModel (A := A) X) (a : A) (n : ℕ) :
    M.seq a n = M.map n a := rfl

/-- Two bounded sequences with null difference have the same corona class. -/
theorem mk_eq_of_tendsto (u v : BoundedMatrixSequence (fun n ↦ X n))
    (h : Tendsto (fun n ↦ ‖u n - v n‖) cofinite (nhds 0)) :
    normMatrixCStarCoronaMk (fun n ↦ X n) u =
      normMatrixCStarCoronaMk (fun n ↦ X n) v := by
  rw [← sub_eq_zero, ← map_sub, normMatrixCStarCoronaMk_eq_zero_iff]
  show Tendsto (fun n ↦ ‖(u - v) n‖) cofinite (nhds 0)
  have hfun : ∀ n, ‖u n - v n‖ = ‖(u - v) n‖ := by
    intro n
    simp only [lp.coeFn_sub, Pi.sub_apply]
  exact Filter.Tendsto.congr hfun h

/-- **The descent.**  A contractive discrete asymptotic homomorphism descends
to a genuine nonunital `*`-homomorphism into the corona: every defect is null,
and the corona is the quotient by the null sequences. -/
def toCoronaHom (M : AsymptoticModel (A := A) X) :
    A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n) where
  toFun a := normMatrixCStarCoronaMk (fun n ↦ X n) (M.seq a)
  map_zero' := by
    have h : normMatrixCStarCoronaMk (fun n ↦ X n) (M.seq 0) =
        normMatrixCStarCoronaMk (fun n ↦ X n) 0 := by
      refine mk_eq_of_tendsto _ _ ?_
      have hfun : ∀ n, ‖M.map n 0‖ = ‖M.seq 0 n - (0 : BoundedMatrixSequence
          (fun n ↦ X n)) n‖ := by
        intro n
        simp only [seq_apply, lp.coeFn_zero, Pi.zero_apply, sub_zero]
      exact Filter.Tendsto.congr hfun M.zero
    rw [h, map_zero]
  map_add' a b := by
    rw [← map_add]
    refine mk_eq_of_tendsto _ _ ?_
    have hfun : ∀ n, ‖M.map n (a + b) - (M.map n a + M.map n b)‖ =
        ‖M.seq (a + b) n - (M.seq a + M.seq b) n‖ := by
      intro n
      simp only [seq_apply, lp.coeFn_add, Pi.add_apply]
    exact Filter.Tendsto.congr hfun (M.add a b)
  map_mul' a b := by
    rw [← map_mul]
    refine mk_eq_of_tendsto _ _ ?_
    have hfun : ∀ n, ‖M.map n (a * b) - M.map n a * M.map n b‖ =
        ‖M.seq (a * b) n - (M.seq a * M.seq b) n‖ := by
      intro n
      simp only [seq_apply, lp.infty_coeFn_mul, Pi.mul_apply]
    exact Filter.Tendsto.congr hfun (M.mul a b)
  map_smul' c a := by
    show normMatrixCStarCoronaMk (fun n ↦ X n) (M.seq (c • a)) =
      c • normMatrixCStarCoronaMk (fun n ↦ X n) (M.seq a)
    rw [← MFAlgebraDimension.normMatrixCStarCoronaMk_smul]
    refine mk_eq_of_tendsto _ _ ?_
    have hfun : ∀ n, ‖M.map n (c • a) - c • M.map n a‖ =
        ‖M.seq (c • a) n - (c • M.seq a) n‖ := by
      intro n
      simp only [seq_apply, lp.coeFn_smul, Pi.smul_apply]
    exact Filter.Tendsto.congr hfun (M.smul c a)
  map_star' a := by
    show normMatrixCStarCoronaMk (fun n ↦ X n) (M.seq (star a)) =
      star (normMatrixCStarCoronaMk (fun n ↦ X n) (M.seq a))
    rw [normMatrixCStarCorona_star_mk]
    refine mk_eq_of_tendsto _ _ ?_
    have hfun : ∀ n, ‖M.map n (star a) - star (M.map n a)‖ =
        ‖M.seq (star a) n - (star (M.seq a)) n‖ := by
      intro n
      simp only [seq_apply, lp.coeFn_star, Pi.star_apply]
    exact Filter.Tendsto.congr hfun (M.star a)

@[simp] theorem toCoronaHom_apply (M : AsymptoticModel (A := A) X) (a : A) :
    M.toCoronaHom a = normMatrixCStarCoronaMk (fun n ↦ X n) (M.seq a) := rfl

/-- **What makes the descent faithful.**  The corona norm of the descended
class is the limsup of the coordinate norms, so a lower bound on that limsup
by the source norm makes the descent isometric, hence injective.

On Shulman's route the lower bound comes from `𝒟`: the `*`-strong limit `q`
satisfies `‖q(x)‖ ≤ liminf ‖x_n‖`, and `q` of the lift is a faithful
representation.  The corona cannot supply it, having discarded the limit. -/
theorem toCoronaHom_injective (M : AsymptoticModel (A := A) X)
    (hlower : ∀ a : A, ‖a‖ ≤ ‖M.toCoronaHom a‖) :
    Function.Injective M.toCoronaHom := by
  intro a b hab
  have hzero : M.toCoronaHom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hle : ‖a - b‖ ≤ ‖M.toCoronaHom (a - b)‖ := hlower (a - b)
  rw [hzero, norm_zero] at hle
  have hsub : a - b = 0 :=
    norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact sub_eq_zero.mp hsub

end AsymptoticModel

end

end ShulmanFill
end GroupApproximation
