import GroupApproximation.GGT.HullSCRelatorSeparation2WindowExact

/-!
# Finite avoidance for windows crossing the base letter

The ordinary window design controls a block letter followed by a bounded pure
run.  A short span of a cyclic relator may instead cross its unique base letter,
so its value has the form

`a_s^n * L * t * R`,

where `L` and `R` are bounded alternating tails and `t` is the fixed base
letter.  There are only finitely many bad exponents for every such pair of
tails.  The proof is the two-sided finite-power lemma
`finite_mul_pow_mul_mem_fam`; the two tail sets and `Bool` are finite.
-/

namespace GroupApproximation
namespace HullSC

universe u

section ThroughBase

variable {G : Type u} [Group G]

/-- Powers which let two bounded block tails close through the fixed base
letter into the opposite peripheral subgroup. -/
def throughBaseBadPow (D : GGT.RelGenSet G Bool) (a : Bool → G) (h₀ h₁ : G)
    (ms : List ℕ) (W : ℕ) (t : G) : Set G :=
  ⋃ s : Bool,
    (fun n : ℕ => a s ^ n) ''
      {n : ℕ | ∃ L ∈ tailSet h₀ h₁ ms W, ∃ R ∈ tailSet h₀ h₁ ms W,
        a s ^ n * L * t * R ∈ D.fam (!s)}

/-- **Only finitely many powers close a bounded window through the base
letter.** -/
theorem finite_throughBaseBadPow {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hmem : ∀ s : Bool, a s ∈ D.fam s) (h₀ h₁ : G) (ms : List ℕ)
    (W : ℕ) (t : G) :
    (throughBaseBadPow D a h₀ h₁ ms W t).Finite := by
  refine Set.finite_iUnion fun s => Set.Finite.image _ ?_
  have hne : s ≠ !s := by cases s <;> simp
  have hpow : ∀ n : ℕ, a s ^ n ∈ D.fam s := fun n => pow_mem (hmem s) n
  have hsub :
      {n : ℕ | ∃ L ∈ tailSet h₀ h₁ ms W, ∃ R ∈ tailSet h₀ h₁ ms W,
        a s ^ n * L * t * R ∈ D.fam (!s)} ⊆
        ⋃ L ∈ tailSet h₀ h₁ ms W,
          ⋃ R ∈ tailSet h₀ h₁ ms W,
            {n : ℕ | (1 : G) * a s ^ n * (L * t * R) ∈ D.fam (!s)} := by
    rintro n ⟨L, hL, R, hR, hn⟩
    refine Set.mem_biUnion hL (Set.mem_biUnion hR ?_)
    change (1 : G) * a s ^ n * (L * t * R) ∈ D.fam (!s)
    simpa only [one_mul, mul_assoc] using hn
  refine Set.Finite.subset ?_ hsub
  refine (finite_tailSet h₀ h₁ ms W).biUnion ?_
  intro L _
  refine (finite_tailSet h₀ h₁ ms W).biUnion ?_
  intro R _
  exact finite_mul_pow_mul_mem_fam hemb
    (fun hsame => hne hsame.1) (hinj s) hpow

/-- Avoiding `throughBaseBadPow` gives the pointwise exclusion used by the
greedy exponent construction. -/
theorem notMem_throughBaseBad_of_notMem
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {h₀ h₁ : G}
    {ms : List ℕ} {W m : ℕ} {t : G}
    (h : ∀ s : Bool, a s ^ m ∉ throughBaseBadPow D a h₀ h₁ ms W t)
    (s : Bool) {r₀ r₁ : ℕ} (hr₀ : r₀ ≤ W) (hr₁ : r₁ ≤ W)
    (b₀ b₁ : Bool) :
    a s ^ m *
        GGT.RelLetter.listVal (blockWord h₀ h₁ b₀ (ms.take r₀)) * t *
        GGT.RelLetter.listVal (blockWord h₀ h₁ b₁ (ms.take r₁))
      ∉ D.fam (!s) := by
  intro hc
  refine h s ?_
  refine Set.mem_iUnion.mpr ⟨s, ?_⟩
  exact ⟨m, ⟨_, mem_tailSet h₀ h₁ ms hr₀ b₀, _,
    mem_tailSet h₀ h₁ ms hr₁ b₁, hc⟩, rfl⟩

end ThroughBase

end HullSC
end GroupApproximation
