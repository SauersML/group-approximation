import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.ShulmanFillModelDescent

/-!
# Lemma 7 for corona-valued conclusions, where it is free

Shulman's Lemma 7 (arXiv:2603.13564v2, pp. 5–6) glues two contractive discrete
asymptotic homomorphisms `φ_λ : A → D` and `ψ_λ : B → D` that agree
asymptotically on `C` into one asymptotic homomorphism on `A *_C B`.  Her proof
induces `*`-homomorphisms into `C_b(Λ, D)/C_0(Λ, D)`, applies the universal
property of the amalgam there, and then comes back down with a *contractive
section* of `C_b(Λ, D) → C_b(Λ, D)/C_0(Λ, D)`, quoted from her [26, Th. 3].

The section is needed only for the return trip.  Everything the `ShulmanFill`
chain consumes lives on the quotient: what Theorem 10 finally needs is a
compatible pair into a corona-like algebra, and the quotient is exactly where
asymptotic agreement becomes *exact* agreement.  So for corona-valued
conclusions Lemma 7 costs nothing beyond the descent:

* descend `φ` and `ψ` to `Q_D = ℓ∞(ℕ, D)/c₀(ℕ, D)`, where approximate
  multiplicativity, additivity and adjoint-compatibility become exact;
* asymptotic agreement on `C` becomes an equation there;
* the universal property of `UniversalCStarAmalgam` gives the map on the
  amalgam.

`Q_D` is already in the repository: it is
`PolarLiftingGeneralCStar.CStarProductCorona (fun _ ↦ D) cofinite`, the
quotient of the bounded product by the null-sequence ideal, with
`cStarProductCoronaQuotient` and `cStarProductCoronaQuotient_eq_zero_iff`.  The
matrix case used elsewhere in this development is the same construction at
`D = M_{k_n}`.

## What this module proves

`SeqAsymptoticHom` packages a contractive discrete asymptotic homomorphism into
a constant sequence of coefficient algebras; `toQuotientHom` descends it to a
unital `*`-homomorphism into `Q_D`; `comp_eq_of_tendsto_sub` turns asymptotic
agreement on `C` into exact agreement of the two descents; and
`glueToSequenceQuotient` is the resulting map on the amalgam, which is Lemma 7
in the form the chain uses.

Nothing here needs the contractive section, and nothing here needs `𝒟`: this is
the step of Theorem 10 that the corona vocabulary really does make free.  The
step it does not make free is faithfulness — see
`Analysis/ShulmanFillModelDescent`.

This module is not in the root import list.  It was authored while builds were
suspended, so it is kept out of the closure until it has been elaborated.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter PolarLiftingGeneralCStar

noncomputable section

variable {A B C D : Type} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [CStarAlgebra D] [Nontrivial D]

/-- A contractive discrete asymptotic homomorphism from `A` into `D`, indexed
by `ℕ`: contractive maps whose algebraic defects are null. -/
structure SeqAsymptoticHom (A D : Type) [CStarAlgebra A] [CStarAlgebra D] where
  /-- The maps into the coefficient algebra. -/
  map : ℕ → A → D
  /-- Contractivity, as in the paper's Remark 6. -/
  contractive : ∀ n a, ‖map n a‖ ≤ ‖a‖
  /-- The unit defect is null. -/
  one : Tendsto (fun n ↦ ‖map n 1 - 1‖) cofinite (nhds 0)
  /-- The zero defect is null. -/
  zero : Tendsto (fun n ↦ ‖map n 0‖) cofinite (nhds 0)
  /-- The additive defect is null. -/
  add : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a + b) - (map n a + map n b)‖) cofinite (nhds 0)
  /-- The multiplicative defect is null. -/
  mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) cofinite (nhds 0)
  /-- The scalar defect is null. -/
  smul : ∀ (z : ℂ) (a : A),
    Tendsto (fun n ↦ ‖map n (z • a) - z • map n a‖) cofinite (nhds 0)
  /-- The adjoint defect is null. -/
  star : ∀ a : A,
    Tendsto (fun n ↦ ‖map n (star a) - star (map n a)‖) cofinite (nhds 0)

namespace SeqAsymptoticHom

/-- The coordinates of an asymptotic homomorphism, as a bounded sequence. -/
def seq (F : SeqAsymptoticHom A D) (a : A) :
    BoundedCStarSequence (fun _ : ℕ ↦ D) :=
  ⟨fun n ↦ F.map n a, memℓp_infty ⟨‖a‖, by
    rintro _ ⟨n, rfl⟩
    exact F.contractive n a⟩⟩

@[simp] theorem seq_apply (F : SeqAsymptoticHom A D) (a : A) (n : ℕ) :
    F.seq a n = F.map n a := rfl

/-- Two bounded sequences with null difference have the same class. -/
theorem quotient_eq_of_tendsto (u v : BoundedCStarSequence (fun _ : ℕ ↦ D))
    (h : Tendsto (fun n ↦ ‖u n - v n‖) cofinite (nhds 0)) :
    cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite u =
      cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite v := by
  rw [← sub_eq_zero, ← map_sub, cStarProductCoronaQuotient_eq_zero_iff]
  show Tendsto (fun n ↦ ‖(u - v) n‖) cofinite (nhds 0)
  have hfun : ∀ n, ‖u n - v n‖ = ‖(u - v) n‖ := by
    intro n
    simp only [lp.coeFn_sub, Pi.sub_apply]
  exact Filter.Tendsto.congr hfun h

/-- **The descent.**  On the quotient by the null sequences every defect
vanishes, so an asymptotic homomorphism becomes a genuine unital
`*`-homomorphism. -/
def toQuotientHom (F : SeqAsymptoticHom A D) :
    A →⋆ₐ[ℂ] CStarProductCorona (fun _ : ℕ ↦ D) cofinite where
  toFun a := cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (F.seq a)
  map_one' := by
    have h : cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (F.seq 1) =
        cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite 1 := by
      refine quotient_eq_of_tendsto _ _ ?_
      have hfun : ∀ n, ‖F.map n 1 - 1‖ =
          ‖F.seq 1 n - (1 : BoundedCStarSequence (fun _ : ℕ ↦ D)) n‖ := by
        intro n
        simp only [seq_apply, lp.infty_coeFn_one, Pi.one_apply]
      exact Filter.Tendsto.congr hfun F.one
    rw [h, map_one]
  map_zero' := by
    have h : cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (F.seq 0) =
        cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite 0 := by
      refine quotient_eq_of_tendsto _ _ ?_
      have hfun : ∀ n, ‖F.map n 0‖ =
          ‖F.seq 0 n - (0 : BoundedCStarSequence (fun _ : ℕ ↦ D)) n‖ := by
        intro n
        simp only [seq_apply, lp.coeFn_zero, Pi.zero_apply, sub_zero]
      exact Filter.Tendsto.congr hfun F.zero
    rw [h, map_zero]
  map_add' a b := by
    rw [← map_add]
    refine quotient_eq_of_tendsto _ _ ?_
    have hfun : ∀ n, ‖F.map n (a + b) - (F.map n a + F.map n b)‖ =
        ‖F.seq (a + b) n - (F.seq a + F.seq b) n‖ := by
      intro n
      simp only [seq_apply, lp.coeFn_add, Pi.add_apply]
    exact Filter.Tendsto.congr hfun (F.add a b)
  map_mul' a b := by
    rw [← map_mul]
    refine quotient_eq_of_tendsto _ _ ?_
    have hfun : ∀ n, ‖F.map n (a * b) - F.map n a * F.map n b‖ =
        ‖F.seq (a * b) n - (F.seq a * F.seq b) n‖ := by
      intro n
      simp only [seq_apply, lp.infty_coeFn_mul, Pi.mul_apply]
    exact Filter.Tendsto.congr hfun (F.mul a b)
  commutes' z := by
    show cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite
        (F.seq (algebraMap ℂ A z)) = algebraMap ℂ _ z
    have halg : algebraMap ℂ A z = z • (1 : A) :=
      Algebra.algebraMap_eq_smul_one z
    have hsmul : cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite
        (F.seq (z • (1 : A))) =
          z • cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (F.seq 1) := by
      rw [← map_smul]
      refine quotient_eq_of_tendsto _ _ ?_
      have hfun : ∀ n, ‖F.map n (z • (1 : A)) - z • F.map n 1‖ =
          ‖F.seq (z • (1 : A)) n - (z • F.seq 1) n‖ := by
        intro n
        simp only [seq_apply, lp.coeFn_smul, Pi.smul_apply]
      exact Filter.Tendsto.congr hfun (F.smul z 1)
    have hone : cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (F.seq 1) =
        1 := by
      have h : cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (F.seq 1) =
          cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite 1 := by
        refine quotient_eq_of_tendsto _ _ ?_
        have hfun : ∀ n, ‖F.map n 1 - 1‖ =
            ‖F.seq 1 n - (1 : BoundedCStarSequence (fun _ : ℕ ↦ D)) n‖ := by
          intro n
          simp only [seq_apply, lp.infty_coeFn_one, Pi.one_apply]
        exact Filter.Tendsto.congr hfun F.one
      rw [h, map_one]
    rw [halg, hsmul, hone, Algebra.algebraMap_eq_smul_one, smul_eq_mul, mul_one]
  map_star' a := by
    show cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (F.seq (star a)) =
      star (cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (F.seq a))
    rw [← map_star]
    refine quotient_eq_of_tendsto _ _ ?_
    have hfun : ∀ n, ‖F.map n (star a) - star (F.map n a)‖ =
        ‖F.seq (star a) n - (star (F.seq a)) n‖ := by
      intro n
      simp only [seq_apply, lp.coeFn_star, Pi.star_apply]
    exact Filter.Tendsto.congr hfun (F.star a)

@[simp] theorem toQuotientHom_apply (F : SeqAsymptoticHom A D) (a : A) :
    F.toQuotientHom a =
      cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (F.seq a) := rfl

end SeqAsymptoticHom

/-! ## Lemma 7, in the form the chain uses -/

/-- **Asymptotic agreement becomes exact agreement.**  This is the whole point
of descending: on the quotient the two glued homomorphisms agree on `C` on the
nose, which is what the universal property of the amalgam requires. -/
theorem comp_eq_of_tendsto_sub (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    (F : SeqAsymptoticHom A D) (G : SeqAsymptoticHom B D)
    (hagree : ∀ c : C,
      Tendsto (fun n ↦ ‖F.map n (iA c) - G.map n (iB c)‖) cofinite (nhds 0)) :
    F.toQuotientHom.comp iA = G.toQuotientHom.comp iB := by
  apply StarAlgHom.ext
  intro c
  show cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (F.seq (iA c)) =
    cStarProductCoronaQuotient (fun _ : ℕ ↦ D) cofinite (G.seq (iB c))
  refine SeqAsymptoticHom.quotient_eq_of_tendsto _ _ ?_
  have hfun : ∀ n, ‖F.map n (iA c) - G.map n (iB c)‖ =
      ‖F.seq (iA c) n - G.seq (iB c) n‖ := by
    intro n
    simp only [SeqAsymptoticHom.seq_apply]
  exact Filter.Tendsto.congr hfun (hagree c)

/-- **Lemma 7 for corona-valued conclusions.**  Two contractive asymptotic
homomorphisms agreeing asymptotically on `C` induce a homomorphism of the full
amalgam into the sequence quotient.  No contractive section is used: the
quotient is where the approximation disappears. -/
def glueToSequenceQuotient (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (F : SeqAsymptoticHom A D) (G : SeqAsymptoticHom B D)
    (hagree : ∀ c : C,
      Tendsto (fun n ↦ ‖F.map n (iA c) - G.map n (iB c)‖) cofinite (nhds 0)) :
    UniversalCStarAmalgam iA iB →⋆ₐ[ℂ]
      CStarProductCorona (fun _ : ℕ ↦ D) cofinite :=
  universalCStarAmalgamEval iA iB
    (CStarAmalgamRepresentation.ofCompatiblePair iA iB
      F.toQuotientHom G.toQuotientHom
      (comp_eq_of_tendsto_sub iA iB F G hagree))

@[simp] theorem glueToSequenceQuotient_left (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (F : SeqAsymptoticHom A D) (G : SeqAsymptoticHom B D)
    (hagree : ∀ c : C,
      Tendsto (fun n ↦ ‖F.map n (iA c) - G.map n (iB c)‖) cofinite (nhds 0))
    (a : A) :
    glueToSequenceQuotient iA iB F G hagree
        (universalCStarAmalgamLeft iA iB a) = F.toQuotientHom a := rfl

@[simp] theorem glueToSequenceQuotient_right (iA : C →⋆ₐ[ℂ] A)
    (iB : C →⋆ₐ[ℂ] B) [Nonempty (CStarAmalgamRepresentation iA iB)]
    (F : SeqAsymptoticHom A D) (G : SeqAsymptoticHom B D)
    (hagree : ∀ c : C,
      Tendsto (fun n ↦ ‖F.map n (iA c) - G.map n (iB c)‖) cofinite (nhds 0))
    (b : B) :
    glueToSequenceQuotient iA iB F G hagree
        (universalCStarAmalgamRight iA iB b) = G.toQuotientHom b := rfl

end

end ShulmanFill
end GroupApproximation
