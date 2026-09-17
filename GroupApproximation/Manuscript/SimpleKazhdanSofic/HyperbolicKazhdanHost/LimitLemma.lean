import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Order.Directed
import GroupApproximation.Meta.AxiomGuard

/-!
# The Olshanskii limit behind a simple quotient

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.477–481 (census row
`fc84c012b409`):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

This module proves the purely combinatorial part of the middle clause. It has no
hypotheses beyond those of `LimitScheme` and uses no geometry.

## The limit lemma

Let `E` be a countable group and let `Adm` be a family of normal subgroups of `E`, the
*admissible* kernels. Assume that:

* `⊥` is admissible;
* one fixed element `e` lies in no admissible kernel;
* **(simplicity step)** for admissible `K`, `x ∉ K` and any `y`, some admissible
  `K' ≥ K` has `y ∈ ⟨⟨x⟩⟩ ⊔ K'`;
* **(push step)** for admissible `K` and any `c`, some admissible `K' ≥ K` has `p ∈ P`
  with `p⁻¹ c ∈ K'`, where `P ≤ E` is a fixed subgroup.

Then there is a normal subgroup `K` such that:

1. `E ⧸ K` is simple;
2. every coset of `K` meets `P`;
3. every element of `K` lies in some admissible kernel.

## Proof

The tasks are `(E × E) ⊕ E`, which is countable, and `enum` enumerates them. Starting
from `⊥`, stage `n + 1` applies the step for task `enum n` to stage `n`:

* a pair `(x, y)` gets the simplicity step, or nothing when `x` is already killed;
* an element `c` gets the push step.

The stages increase, so their supremum `K` is their directed union
(`Subgroup.mem_iSup_of_directed`). This gives normality, clause 3, and `e ∉ K`.

For clause 1, let `x ∉ K` and take any `y`. At the stage `n` where `enum n = (x, y)`,
`x` is not yet killed. Hence `y ∈ ⟨⟨x⟩⟩ ⊔ K`.

So if `N ◁ E ⧸ K` is not trivial, its preimage `M` contains some `x ∉ K`. `M` also
contains `K` and `⟨⟨x⟩⟩`, hence every `y`, so `N = ⊤`. `E ⧸ K` is nontrivial because
`e ∉ K`.

Clause 2 comes from the stage at which `enum n = c`.
-/

universe u

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HyperbolicKazhdanHost

/-- The admissible kernels of an Olshanskii-type limit, with its two steps. Instances
are built unconditionally from their own hypotheses; this structure only packages
the combinatorics of the limit. -/
structure LimitScheme (E : Type u) [Group E] where
  /-- The admissible kernels. -/
  Adm : Subgroup E → Prop
  /-- The subgroup that is pushed onto the whole quotient. -/
  P : Subgroup E
  /-- The trivial kernel is admissible. -/
  adm_bot : Adm ⊥
  /-- Admissible kernels are normal. -/
  normal : ∀ K, Adm K → K.Normal
  /-- A fixed element survives in every admissible quotient. -/
  proper : ∃ e : E, ∀ K, Adm K → e ∉ K
  /-- The simplicity step. -/
  simp_step : ∀ K, Adm K → ∀ x y : E, x ∉ K →
    ∃ K', Adm K' ∧ K ≤ K' ∧ y ∈ Subgroup.normalClosure {x} ⊔ K'
  /-- The push step. -/
  push_step : ∀ K, Adm K → ∀ c : E, ∃ K', Adm K' ∧ K ≤ K' ∧ ∃ p ∈ P, p⁻¹ * c ∈ K'

/-- An enumeration of the tasks `(E × E) ⊕ E` of a countable group. -/
noncomputable def enum (E : Type u) [Group E] [Countable E] : ℕ → (E × E) ⊕ E :=
  Classical.choose (@exists_surjective_nat ((E × E) ⊕ E) ⟨Sum.inr 1⟩ inferInstance)

theorem enum_surjective (E : Type u) [Group E] [Countable E] :
    Function.Surjective (enum E) :=
  Classical.choose_spec (@exists_surjective_nat ((E × E) ⊕ E) ⟨Sum.inr 1⟩ inferInstance)

/-- **A quotient is simple** when it is proper and every element outside the kernel
normally generates everything modulo the kernel. -/
theorem isSimpleGroup_quotient {E : Type u} [Group E] (K : Subgroup E) [K.Normal]
    {e : E} (he : e ∉ K)
    (hsimp : ∀ x : E, x ∉ K → ∀ y : E, y ∈ Subgroup.normalClosure {x} ⊔ K) :
    IsSimpleGroup (E ⧸ K) := by
  haveI : Nontrivial (E ⧸ K) :=
    ⟨⟨(e : E ⧸ K), 1, fun h => he ((QuotientGroup.eq_one_iff e).1 h)⟩⟩
  refine ⟨fun N hN => ?_⟩
  by_cases hMK : N.comap (QuotientGroup.mk' K) ≤ K
  · refine Or.inl ((Subgroup.eq_bot_iff_forall (H := N)).2 fun w hw => ?_)
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective w
    have hz : z ∈ N.comap (QuotientGroup.mk' K) := hw
    exact (QuotientGroup.eq_one_iff z).2 (hMK hz)
  · refine Or.inr ((Subgroup.eq_top_iff' (H := N)).2 fun w => ?_)
    obtain ⟨x, hxM, hxK⟩ := SetLike.not_le_iff_exists.1 hMK
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    haveI : (N.comap (QuotientGroup.mk' K)).Normal := hN.comap _
    have hle : Subgroup.normalClosure {x} ⊔ K ≤ N.comap (QuotientGroup.mk' K) := by
      refine sup_le ?_ ?_
      · exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.2 hxM)
      · intro z hz
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz]
        exact N.one_mem
    exact Subgroup.mem_comap.1 (hle (hsimp x hxK y))

namespace LimitScheme

variable {E : Type u} [Group E] (L : LimitScheme E)

/-- The stages of the limit: admissible kernels. -/
abbrev Stage : Type u := {K : Subgroup E // L.Adm K}

theorem exists_simp (K : L.Stage) (x y : E) :
    ∃ K' : L.Stage, K.1 ≤ K'.1 ∧ (x ∉ K.1 → y ∈ Subgroup.normalClosure {x} ⊔ K'.1) := by
  by_cases h : x ∈ K.1
  · exact ⟨K, le_rfl, fun h' => absurd h h'⟩
  · obtain ⟨K', hK', hle, hy⟩ := L.simp_step K.1 K.2 x y h
    exact ⟨⟨K', hK'⟩, hle, fun _ => hy⟩

theorem exists_push (K : L.Stage) (c : E) :
    ∃ K' : L.Stage, K.1 ≤ K'.1 ∧ ∃ p ∈ L.P, p⁻¹ * c ∈ K'.1 := by
  obtain ⟨K', hK', hle, hc⟩ := L.push_step K.1 K.2 c
  exact ⟨⟨K', hK'⟩, hle, hc⟩

/-- One step of the limit, for one task. -/
noncomputable def step (K : L.Stage) : (E × E) ⊕ E → L.Stage
  | Sum.inl p => Classical.choose (L.exists_simp K p.1 p.2)
  | Sum.inr c => Classical.choose (L.exists_push K c)

theorem le_step (K : L.Stage) (t : (E × E) ⊕ E) : K.1 ≤ (L.step K t).1 := by
  cases t with
  | inl p => exact (Classical.choose_spec (L.exists_simp K p.1 p.2)).1
  | inr c => exact (Classical.choose_spec (L.exists_push K c)).1

theorem step_inl (K : L.Stage) (x y : E) (hx : x ∉ K.1) :
    y ∈ Subgroup.normalClosure {x} ⊔ (L.step K (Sum.inl (x, y))).1 :=
  (Classical.choose_spec (L.exists_simp K x y)).2 hx

theorem step_inr (K : L.Stage) (c : E) :
    ∃ p ∈ L.P, p⁻¹ * c ∈ (L.step K (Sum.inr c)).1 :=
  (Classical.choose_spec (L.exists_push K c)).2

variable [Countable E]

/-- The stages of the limit. -/
noncomputable def seq : ℕ → L.Stage
  | 0 => ⟨⊥, L.adm_bot⟩
  | n + 1 => L.step (seq n) (enum E n)

theorem seq_succ (n : ℕ) : L.seq (n + 1) = L.step (L.seq n) (enum E n) := rfl

theorem seq_mono : Monotone fun n => (L.seq n).1 := by
  refine monotone_nat_of_le_succ fun n => ?_
  show (L.seq n).1 ≤ (L.seq (n + 1)).1
  rw [L.seq_succ n]
  exact L.le_step _ _

/-- The limit kernel. -/
noncomputable def limit : Subgroup E := ⨆ n, (L.seq n).1

theorem mem_limit {z : E} : z ∈ L.limit ↔ ∃ n, z ∈ (L.seq n).1 :=
  Subgroup.mem_iSup_of_directed L.seq_mono.directed_le

theorem le_limit (n : ℕ) : (L.seq n).1 ≤ L.limit :=
  le_iSup (fun n => (L.seq n).1) n

theorem limit_normal : L.limit.Normal := by
  refine ⟨fun z hz g => ?_⟩
  obtain ⟨n, hn⟩ := L.mem_limit.1 hz
  exact L.le_limit n ((L.normal _ (L.seq n).2).conj_mem z hn g)

theorem limit_simp {x : E} (hx : x ∉ L.limit) (y : E) :
    y ∈ Subgroup.normalClosure {x} ⊔ L.limit := by
  obtain ⟨n, hn⟩ := enum_surjective E (Sum.inl (x, y))
  have hxn : x ∉ (L.seq n).1 := fun h => hx (L.le_limit n h)
  have h' : y ∈ Subgroup.normalClosure {x} ⊔ (L.seq (n + 1)).1 := by
    rw [L.seq_succ n, hn]
    exact L.step_inl (L.seq n) x y hxn
  exact sup_le_sup_left (L.le_limit (n + 1)) (Subgroup.normalClosure {x}) h'

theorem limit_push (c : E) : ∃ p ∈ L.P, p⁻¹ * c ∈ L.limit := by
  obtain ⟨n, hn⟩ := enum_surjective E (Sum.inr c)
  have h' : ∃ p ∈ L.P, p⁻¹ * c ∈ (L.seq (n + 1)).1 := by
    rw [L.seq_succ n, hn]
    exact L.step_inr (L.seq n) c
  obtain ⟨p, hp, hpc⟩ := h'
  exact ⟨p, hp, L.le_limit (n + 1) hpc⟩

/-- **The limit lemma.** A countable group with a `LimitScheme` has a normal subgroup
with simple quotient, onto which `P` surjects, all of whose elements are killed by an
admissible kernel. -/
theorem exists_simple_quotient :
    ∃ (K : Subgroup E) (_ : K.Normal), IsSimpleGroup (E ⧸ K) ∧
      (∀ c : E, ∃ p ∈ L.P, p⁻¹ * c ∈ K) ∧ ∀ z ∈ K, ∃ K', L.Adm K' ∧ z ∈ K' := by
  haveI : L.limit.Normal := L.limit_normal
  obtain ⟨e, he⟩ := L.proper
  have heK : e ∉ L.limit := by
    intro h
    obtain ⟨n, hn⟩ := L.mem_limit.1 h
    exact he _ (L.seq n).2 hn
  refine ⟨L.limit, L.limit_normal, isSimpleGroup_quotient L.limit heK
    (fun x hx y => L.limit_simp hx y), L.limit_push, fun z hz => ?_⟩
  obtain ⟨n, hn⟩ := L.mem_limit.1 hz
  exact ⟨(L.seq n).1, (L.seq n).2, hn⟩

end LimitScheme

end HyperbolicKazhdanHost
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.LimitScheme.exists_simple_quotient
