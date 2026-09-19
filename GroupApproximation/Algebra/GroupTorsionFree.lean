import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Ordinary torsion-freeness for groups

Mathlib's `IsMulTorsionFree` expresses injectivity of every positive power
map.  For noncommutative groups that is stronger than the usual assertion
that the identity is the only finite-order element.  The constructions in
this project require the usual notion, recorded here in power form.
-/

namespace GroupApproximation

universe u v

/-- Ordinary group torsion-freeness: a positive power can equal the identity
only for the identity element. -/
def IsPowerTorsionFree (G : Type u) [Group G] : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1

namespace IsPowerTorsionFree

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Mathlib's stronger unique-root property implies ordinary
torsion-freeness. -/
theorem of_isMulTorsionFree [IsMulTorsionFree G] : IsPowerTorsionFree G := by
  intro g n hn hpow
  exact (pow_eq_one_iff_left (Nat.ne_of_gt hn)).mp hpow

/-- A nonidentity element of an ordinarily torsion-free group does not have
finite order. -/
theorem not_isOfFinOrder (hG : IsPowerTorsionFree G) {g : G} (hg : g ≠ 1) :
    ¬ IsOfFinOrder g := by
  intro hfinite
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfinite
  exact hg (hG g n hn hpow)

/-- Ordinary torsion-freeness pulls back through an injective homomorphism. -/
theorem comap (hH : IsPowerTorsionFree H) (f : G →* H)
    (hf : Function.Injective f) : IsPowerTorsionFree G := by
  intro g n hn hpow
  apply hf
  rw [map_one]
  apply hH (f g) n hn
  simpa using congrArg f hpow

/-- A direct product of ordinarily torsion-free groups is torsion-free. -/
theorem prod (hG : IsPowerTorsionFree G) (hH : IsPowerTorsionFree H) :
    IsPowerTorsionFree (G × H) := by
  intro g n hn hpow
  apply Prod.ext
  · apply hG g.1 n hn
    simpa using congrArg Prod.fst hpow
  · apply hH g.2 n hn
    simpa using congrArg Prod.snd hpow

section DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
variable {K : ι → Type*} [∀ i, Group (K i)]
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (K i) (K j)]
variable [∀ i j (h : i ≤ j), MonoidHomClass (T h) (K i) (K j)]
variable [DirectedSystem K (f · · ·)]

/-- Countability is preserved by a directed colimit of a countable family
of countable groups. -/
noncomputable instance directLimit_countable [Countable ι]
    [∀ i, Countable (K i)] : Countable (DirectLimit K f) :=
  Quotient.mk''_surjective.countable

/-- The canonical homomorphism from one stage into a directed group
colimit. -/
def directLimitOf (i : ι) :=
  letI : Nonempty ι := ⟨i⟩
  ({ toFun := fun g => ⟦⟨i, g⟩⟧
     map_one' := (DirectLimit.one_def i).symm
     map_mul' := fun x y => (DirectLimit.mul_def i x y).symm } :
    K i →* DirectLimit K f)

/-- If every transition map is injective, every canonical stage map into
the directed colimit is injective. -/
theorem directLimitOf_injective
    (hf : ∀ i j (h : i ≤ j), Function.Injective (f i j h)) (i : ι) :
    Function.Injective (directLimitOf (f := f) i) := by
  letI : Nonempty ι := ⟨i⟩
  exact DirectLimit.mk_injective f hf i

/-- A directed colimit of ordinarily torsion-free groups is torsion-free.
No injectivity of the transition maps is needed: an equality to one in the
colimit already holds at a common later stage. -/
theorem directLimit (i₀ : ι) (hK : ∀ i, IsPowerTorsionFree (K i)) :
    letI : Nonempty ι := ⟨i₀⟩
    IsPowerTorsionFree (DirectLimit K f) := by
  letI : Nonempty ι := ⟨i₀⟩
  show IsPowerTorsionFree (DirectLimit K f)
  intro x n hn hpow
  induction x using DirectLimit.induction with
  | _ i g =>
      apply (DirectLimit.exists_eq_one (f := f) ⟨i, g⟩).2
      rw [DirectLimit.npow_def] at hpow
      obtain ⟨j, hij, hgj⟩ :=
        (DirectLimit.exists_eq_one (f := f) ⟨i, g ^ n⟩).1 hpow
      refine ⟨j, hij, hK j (f i j hij g) n hn ?_⟩
      simpa using hgj

end DirectLimit

end IsPowerTorsionFree

end GroupApproximation
