import GroupApproximation.GGT.HullSCRelatorSeparation2PowFam

/-!
# The tails a window can close against, and the exponents they forbid

The same-side exclusion has to be discharged for component starts of one index at
every even distance up to the window `1 + b`, and
`GGT/HullSCRelatorSeparation2Cross.lean` covers only distance two.  At larger
distances the element joining two starts of index `λ` is an alternating product;
stripping its first letter, which is in `H_λ`, leaves a product whose leftmost
letter is a power of the OTHER element followed by a tail of older letters.  So
the question at each greedy step is which exponents `n` make `a_s^n · G` land in
`H_{¬s}` for a tail `G`, and `GGT/HullSCRelatorSeparation2PowFam.lean` says: only
finitely many, for each tail.

This module assembles the two finiteness facts into the finite set of group
elements the greedy step avoids.

* `tailSet` -- the tails: what a prefix of the exponents already chosen spells,
  at either starting index, up to the window length.  Finite because it is
  indexed by a Boolean and a bounded natural.
* `windowBadPow` -- the powers at the forbidden exponents, over both indices, so
  that "the window closes" becomes membership in a finite set of group elements,
  which is what the greedy step already knows how to avoid.

**Both indices, not one.**  `blockWord` flips its starting index on each cons, so
prepending an exponent flips the index of every exponent already chosen: an
exponent picked while its letter has index `false` may carry index `true` in the
finished relator.  The bad set therefore ranges over both indices.  A
construction that guarded only the index the letter has at the moment of choice
would be wrong, and the error would not surface until the window argument was
assembled.
-/

namespace GroupApproximation
namespace HullSC

universe u

section Tails

variable {G : Type u} [Group G]

/-- **The tails**: what a bounded prefix of the exponents already chosen spells,
read from either starting index. -/
def tailSet (h₀ h₁ : G) (ms : List ℕ) (W : ℕ) : Set G :=
  (fun q : Bool × ℕ =>
      GGT.RelLetter.listVal (blockWord h₀ h₁ q.1 (ms.take q.2))) ''
    (Set.univ ×ˢ Set.Iic W)

theorem finite_tailSet (h₀ h₁ : G) (ms : List ℕ) (W : ℕ) :
    (tailSet h₀ h₁ ms W).Finite :=
  Set.Finite.image _ (Set.finite_univ.prod (Set.finite_Iic W))

theorem mem_tailSet (h₀ h₁ : G) (ms : List ℕ) {W r : ℕ} (hr : r ≤ W)
    (s : Bool) :
    GGT.RelLetter.listVal (blockWord h₀ h₁ s (ms.take r))
      ∈ tailSet h₀ h₁ ms W :=
  ⟨(s, r), ⟨Set.mem_univ s, hr⟩, rfl⟩

/-- **The powers a new exponent must miss** for no window to close against a
tail, at either index. -/
def windowBadPow (D : GGT.RelGenSet G Bool) (a : Bool → G) (h₀ h₁ : G)
    (ms : List ℕ) (W : ℕ) : Set G :=
  ⋃ s : Bool,
    (fun n : ℕ => a s ^ n) ''
      {n : ℕ | ∃ G₀ ∈ tailSet h₀ h₁ ms W, a s ^ n * G₀ ∈ D.fam (!s)}

/-- **It is finite.**  For each index and each tail, `HullSC.finite_pow_mul_mem_fam`
bounds the exponents; the tails are finitely many and the indices are two. -/
theorem finite_windowBadPow {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hmem : ∀ s : Bool, a s ∈ D.fam s) (h₀ h₁ : G) (ms : List ℕ) (W : ℕ) :
    (windowBadPow D a h₀ h₁ ms W).Finite := by
  refine Set.finite_iUnion fun s => Set.Finite.image _ ?_
  have hne : s ≠ !s := by cases s <;> simp
  have hpow : ∀ n : ℕ, a s ^ n ∈ D.fam s := fun n => pow_mem (hmem s) n
  have hfin : {d : ℕ | a s ^ d ∈ D.fam (!s)}.Finite :=
    finite_pow_mem_fam hemb hne (hinj s) hpow
  have hsub : {n : ℕ | ∃ G₀ ∈ tailSet h₀ h₁ ms W, a s ^ n * G₀ ∈ D.fam (!s)}
      ⊆ ⋃ G₀ ∈ tailSet h₀ h₁ ms W, {n : ℕ | a s ^ n * G₀ ∈ D.fam (!s)} := by
    rintro n ⟨G₀, hG₀, hn⟩
    exact Set.mem_biUnion hG₀ hn
  refine Set.Finite.subset ?_ hsub
  refine (finite_tailSet h₀ h₁ ms W).biUnion ?_
  intro G₀ _
  exact finite_pow_mul_mem_fam hfin

/-- **Missing the powers is missing the exponents.** -/
theorem notMem_windowBad_of_notMem {D : GGT.RelGenSet G Bool} {a : Bool → G}
    (_hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    {h₀ h₁ : G} {ms : List ℕ} {W m : ℕ}
    (h : ∀ s : Bool, a s ^ m ∉ windowBadPow D a h₀ h₁ ms W) (s : Bool)
    {r : ℕ} (hr : r ≤ W) (t : Bool) :
    a s ^ m * GGT.RelLetter.listVal (blockWord h₀ h₁ t (ms.take r))
      ∉ D.fam (!s) := by
  intro hc
  refine h s ?_
  refine Set.mem_iUnion.mpr ⟨s, ?_⟩
  exact ⟨m, ⟨_, mem_tailSet h₀ h₁ ms hr t, hc⟩, rfl⟩

end Tails

end HullSC
end GroupApproximation
