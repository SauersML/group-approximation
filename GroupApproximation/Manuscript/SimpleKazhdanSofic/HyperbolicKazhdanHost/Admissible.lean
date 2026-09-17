import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.LimitLemma
import GroupApproximation.GGT.HullSCTheorem71General
import GroupApproximation.GGT.HullSCConeOff
import GroupApproximation.Manuscript.NonMF.HullBallForm
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Algebra.HyperbolicGroup
import GroupApproximation.Kazhdan.Kazhdan
import Mathlib.GroupTheory.Coprod.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Admissible kernels of `H ∗ Γ`: the Coulon–Fournier-Facio limit

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.477–481 (census row
`fc84c012b409`):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

This module builds the `LimitScheme` behind the middle clause.

## The route

Let `H` be an infinite torsion-free hyperbolic group with property (T), and let `Γ` be a
countable group. The free product `E = H ∗ Γ` is countable. We look for a quotient
`E ⧸ K` that is simple, in which `H` surjects and `Γ` embeds.

A kernel `K ◁ E` is **admissible** when `q : E → Q = E ⧸ K` satisfies:

1. `Q` carries a Hull generating set `A`, so `Γ(Q, A)` is hyperbolic and `Q` acts on it
   acylindrically and non-elementarily;
2. every letter `q(γ)` with `γ ∈ Γ` lies in `A`;
3. `q ∘ inr` is injective;
4. `q(H)` is suitable in the sense of Hull, Definition 1.4.

Admissible kernels satisfy the steps of `LimitScheme`:

* **Push step.** Hull's Theorem 7.1 with `N = q(H)`, no extra subgroups, target `q(c)` and
  radius `1` gives a further quotient `s : Q → Q'` with `s(q c) ∈ s(q(H))`. Hence `p⁻¹ c`
  dies for some `p ∈ H`.
  - The new alphabet contains the image of `A`, so it contains every `Γ`-letter.
  - `s` is injective on the `1`-ball, which contains every `Γ`-letter, so `Γ` still
    embeds.
  - `s(q(H))` is suitable by clause (d) of Hull's theorem.
* **Simplicity step.** For `x ∉ K`, the normal closure `⟨⟨q x⟩⟩` is suitable (clause G2
  below). Hull's theorem with `N = ⟨⟨q x⟩⟩`, the one extra subgroup `q(H)`, target `q(y)` and
  radius `1` makes `q(y)` congruent to an element of `⟨⟨q x⟩⟩ = q(⟨⟨x⟩⟩)`. So
  `y ∈ ⟨⟨x⟩⟩ ⊔ K'`. The extra subgroup keeps `q(H)` suitable, and the other clauses
  persist as for the push step.
* `⊥` is admissible by clause G1 below. `inr γ₀` survives every admissible kernel when
  `γ₀ ≠ 1`, because `Γ` embeds.

## The residual geometry (`CoulonFournierFacioGeometryStatement`)

* **G1** (start). `H ∗ Γ`, with the whole of `Γ` coned off, is hyperbolic relative to `Γ`.
  It has a Hull generating set containing `Γ`, namely a finite generating set of `H`
  together with `Γ`. The action on the relative Cayley graph is acylindrical (Osin,
  *Acylindrically hyperbolic groups*, Prop. 5.2). `H`, being non-elementary hyperbolic
  (infinite with (T), hence not virtually cyclic), acts non-elementarily. It normalizes no
  nontrivial finite subgroup, since every such subgroup fixes a unique vertex of the
  Bass–Serre tree.
* **G2** (Osin, Lemma 7.1, general form, and Hull, Lemma 3.9). Assume some subgroup of `Q` is
  suitable. Then `Q` is non-elementary and has no nontrivial finite normal subgroup. So every
  nontrivial normal subgroup is infinite, hence non-elementary. Its maximal normalized finite
  subgroup is normal, hence trivial.

The corpus proves Osin's Lemma 7.1 only in the torsion-free printed form
(`OsinLemma71Printed`), and it has no relative-hyperbolicity combination theorem for free
products. That is why G1 ∧ G2 is the one isolated residual `Prop`.

Hull's Theorem 7.1 is consumed as `HullSC.HullOneStepStatementGeneral.{0}`. The corpus
proves it from the least-area Greendlinger leaf
(`HullSC.hullOneStepStatementGeneral_of_greendlinger`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HyperbolicKazhdanHost

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

/-- **The residual geometry of the Coulon–Fournier-Facio route**, the one isolated `Prop`:

* (G1) the start geometry on `H ∗ Γ`;
* (G2) normal closures of nontrivial elements are suitable once some subgroup is. -/
def CoulonFournierFacioGeometryStatement : Prop :=
  (∀ (H Γ : Type) [Group H] [Group Γ], Infinite H → IsPowerTorsionFree H →
      Hyperbolic.IsHyperbolicGroup H → HasKazhdanPropertyT.{0, 0} H →
      ∃ A : HullGeneratingSet (Monoid.Coprod H Γ),
        (∀ γ : Γ, (Monoid.Coprod.inr γ : Monoid.Coprod H Γ) ∈ A.alphabet.carrier) ∧
          Suitable A.alphabet (Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range) ∧
    ∀ (Q : Type) [Group Q] (A : HullGeneratingSet Q) (N : Subgroup Q),
      Suitable A.alphabet N → ∀ x : Q, x ≠ 1 →
        Suitable A.alphabet (Subgroup.normalClosure {x})

/-- A letter lies in the `1`-ball of the Cayley graph. -/
theorem mem_cayleyBall_one_of_mem {Q : Type} [Group Q] (A : Alphabet Q) {x : Q}
    (hx : x ∈ A.carrier) : x ∈ cayleyBall A 1 := by
  rw [HullSC.mem_cayleyBall_iff, wordDist_one_left]
  exact wordNorm_le_one_of_mem hx

section Admissible

variable {H Γ : Type} [Group H] [Group Γ]

/-- **An admissible kernel** of `H ∗ Γ`: the quotient carries a Hull generating set containing
the `Γ`-letters, `Γ` embeds, and the image of `H` is suitable. -/
def IsAdmissible (K : Subgroup (Monoid.Coprod H Γ)) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (q : Monoid.Coprod H Γ →* Q), Function.Surjective q ∧ q.ker = K ∧
    ∃ A : HullGeneratingSet Q,
      (∀ γ : Γ, q (Monoid.Coprod.inr γ) ∈ A.alphabet.carrier) ∧
        Function.Injective (q.comp (Monoid.Coprod.inr : Γ →* Monoid.Coprod H Γ)) ∧
          Suitable A.alphabet ((Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range.map q)

/-- One Hull step at radius `1` keeps a quotient admissible, given suitability of the image
of `H`. -/
theorem isAdmissible_step {Q : Type} [Group Q] {q : Monoid.Coprod H Γ →* Q}
    (hq : Function.Surjective q) (A : HullGeneratingSet Q)
    (halph : ∀ γ : Γ, q (Monoid.Coprod.inr γ) ∈ A.alphabet.carrier)
    (hinj : Function.Injective (q.comp (Monoid.Coprod.inr : Γ →* Monoid.Coprod H Γ)))
    {N : Subgroup Q} {k : ℕ} {S : Fin k → Subgroup Q} (s : HullSC.HullStep A N S 1)
    (hP : Suitable s.hullSet.alphabet
      (((Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range.map q).map s.q)) :
    IsAdmissible (s.q.comp q).ker := by
  refine ⟨s.Q, inferInstance, s.q.comp q, s.surjective.comp hq, rfl, s.hullSet,
    fun γ => s.alphabet_image (q (Monoid.Coprod.inr γ)) (halph γ), ?_, ?_⟩
  · intro a b hab
    have hab' : s.q (q (Monoid.Coprod.inr a)) = s.q (q (Monoid.Coprod.inr b)) := hab
    have h : (q.comp (Monoid.Coprod.inr : Γ →* Monoid.Coprod H Γ)) a =
        (q.comp (Monoid.Coprod.inr : Γ →* Monoid.Coprod H Γ)) b :=
      s.injOn (mem_cayleyBall_one_of_mem A.alphabet (halph a))
        (mem_cayleyBall_one_of_mem A.alphabet (halph b)) hab'
    exact hinj h
  · rw [← Subgroup.map_map]
    exact hP

/-- The trivial kernel is admissible from the start geometry. -/
theorem isAdmissible_bot (A : HullGeneratingSet (Monoid.Coprod H Γ))
    (halph : ∀ γ : Γ, (Monoid.Coprod.inr γ : Monoid.Coprod H Γ) ∈ A.alphabet.carrier)
    (hsuit : Suitable A.alphabet (Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range) :
    IsAdmissible (⊥ : Subgroup (Monoid.Coprod H Γ)) := by
  refine ⟨Monoid.Coprod H Γ, inferInstance, MonoidHom.id _, fun z => ⟨z, rfl⟩,
    (MonoidHom.ker_eq_bot_iff _).2 fun _ _ h => h, A, halph, ?_, ?_⟩
  · rw [MonoidHom.id_comp]
    exact Monoid.Coprod.inr_injective
  · rw [Subgroup.map_id]
    exact hsuit

/-- A nontrivial `Γ`-letter survives every admissible kernel. -/
theorem inr_not_mem_of_isAdmissible {K : Subgroup (Monoid.Coprod H Γ)} (hK : IsAdmissible K)
    {γ : Γ} (hγ : γ ≠ 1) : (Monoid.Coprod.inr γ : Monoid.Coprod H Γ) ∉ K := by
  obtain ⟨Q, _, q, _, rfl, _, _, hinj, _⟩ := hK
  intro h
  apply hγ
  apply hinj
  have h' : q (Monoid.Coprod.inr γ) = 1 := MonoidHom.mem_ker.1 h
  simp only [MonoidHom.comp_apply, h', map_one]

/-- **The push step.** -/
theorem admissible_push_step (hhull : HullSC.HullOneStepStatementGeneral.{0})
    {K : Subgroup (Monoid.Coprod H Γ)} (hK : IsAdmissible K) (c : Monoid.Coprod H Γ) :
    ∃ K', IsAdmissible K' ∧ K ≤ K' ∧
      ∃ p ∈ (Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range, p⁻¹ * c ∈ K' := by
  obtain ⟨Q, _, q, hq, rfl, A, halph, hinj, hsuit⟩ := hK
  obtain ⟨T⟩ := hhull (k := 0) (S := fun j : Fin 0 => Fin.elim0 j) A hsuit
    (fun j : Fin 0 => Fin.elim0 j) (q c) 1
  have hm : T.step.q (q c) ∈
      ((Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range.map q).map T.step.q :=
    T.mem_map 0
  obtain ⟨n, hn, hnc⟩ := Subgroup.mem_map.1 hm
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hn
  refine ⟨(T.step.q.comp q).ker,
    isAdmissible_step hq A halph hinj T.step T.step.suitable_map, ?_, p, hp, ?_⟩
  · intro z hz
    have hz' : q z = 1 := MonoidHom.mem_ker.1 hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hz', map_one]
  · rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, hnc,
      inv_mul_cancel]

/-- **The simplicity step.** -/
theorem admissible_simp_step (hhull : HullSC.HullOneStepStatementGeneral.{0})
    (hgeom : CoulonFournierFacioGeometryStatement)
    {K : Subgroup (Monoid.Coprod H Γ)} (hK : IsAdmissible K) (x y : Monoid.Coprod H Γ)
    (hx : x ∉ K) :
    ∃ K', IsAdmissible K' ∧ K ≤ K' ∧ y ∈ Subgroup.normalClosure {x} ⊔ K' := by
  obtain ⟨Q, _, q, hq, rfl, A, halph, hinj, hsuit⟩ := hK
  have hx1 : q x ≠ 1 := fun h => hx (MonoidHom.mem_ker.2 h)
  have hN : Suitable A.alphabet (Subgroup.normalClosure {q x}) :=
    And.right hgeom Q A _ hsuit (q x) hx1
  obtain ⟨T⟩ := hhull (k := 1)
    (S := fun _ : Fin 1 => (Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range.map q) A hN
    (fun _ : Fin 1 => hsuit) (q y) 1
  have hmem : T.step.q (q y) ∈ (Subgroup.normalClosure {q x}).map T.step.q := T.mem_map 0
  obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.1 hmem
  have hNC : (Subgroup.normalClosure {x}).map q = Subgroup.normalClosure {q x} := by
    rw [Subgroup.map_normalClosure _ q hq, Set.image_singleton]
  rw [← hNC] at hn
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hn
  have hker : m⁻¹ * y ∈ (T.step.q.comp q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, hny,
      inv_mul_cancel]
  have hfam : Suitable T.step.hullSet.alphabet
      (((Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range.map q).map T.step.q) :=
    T.step.suitable_map_family 0
  refine ⟨(T.step.q.comp q).ker, isAdmissible_step hq A halph hinj T.step hfam, ?_, ?_⟩
  · intro z hz
    have hz' : q z = 1 := MonoidHom.mem_ker.1 hz
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hz', map_one]
  · have h := Subgroup.mul_mem_sup hm hker
    rwa [mul_inv_cancel_left] at h

/-- `Γ` embeds in the limit quotient when every killed element is killed admissibly. -/
theorem injective_mk_inr {K : Subgroup (Monoid.Coprod H Γ)} [K.Normal]
    (hK : ∀ z ∈ K, ∃ K', IsAdmissible K' ∧ z ∈ K') :
    Function.Injective
      ((QuotientGroup.mk' K).comp (Monoid.Coprod.inr : Γ →* Monoid.Coprod H Γ)) := by
  intro a b hab
  have hab' : ((Monoid.Coprod.inr a : Monoid.Coprod H Γ) : Monoid.Coprod H Γ ⧸ K) =
      ((Monoid.Coprod.inr b : Monoid.Coprod H Γ) : Monoid.Coprod H Γ ⧸ K) := hab
  obtain ⟨_, ⟨Q, _, q, _, rfl, _, _, hinj, _⟩, hz⟩ := hK _ (QuotientGroup.eq.1 hab')
  apply hinj
  have h : q ((Monoid.Coprod.inr a : Monoid.Coprod H Γ)⁻¹ * Monoid.Coprod.inr b) = 1 :=
    MonoidHom.mem_ker.1 hz
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h

end Admissible

/-- **The Coulon–Fournier-Facio limit scheme** on `H ∗ Γ`. -/
noncomputable def limitScheme (hhull : HullSC.HullOneStepStatementGeneral.{0})
    (hgeom : CoulonFournierFacioGeometryStatement) (H Γ : Type) [Group H] [Group Γ]
    {γ₀ : Γ} (hγ₀ : γ₀ ≠ 1) (hinf : Infinite H) (htf : IsPowerTorsionFree H)
    (hhyp : Hyperbolic.IsHyperbolicGroup H) (hT : HasKazhdanPropertyT.{0, 0} H) :
    LimitScheme (Monoid.Coprod H Γ) where
  Adm := IsAdmissible
  P := (Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range
  adm_bot := by
    obtain ⟨A, halph, hsuit⟩ := And.left hgeom H Γ hinf htf hhyp hT
    exact isAdmissible_bot A halph hsuit
  normal := fun _ hK => by
    obtain ⟨Q, _, q, _, rfl, _⟩ := hK
    exact q.normal_ker
  proper := ⟨Monoid.Coprod.inr γ₀, fun _ hK => inr_not_mem_of_isAdmissible hK hγ₀⟩
  simp_step := fun _ hK x y hx => admissible_simp_step hhull hgeom hK x y hx
  push_step := fun _ hK c => admissible_push_step hhull hK c

end HyperbolicKazhdanHost
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.admissible_simp_step
#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.admissible_push_step
#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.limitScheme
