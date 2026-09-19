import GroupApproximation.Kazhdan.OrbitAverageSpectralGap

/-!
# The positive control for the orbit-average criterion

`Kazhdan/OrbitAverageSpectralGap.lean` proves that a uniform norm gap for the
orbit average is exactly property `(T)`.  A criterion that is never satisfiable
proves nothing, so this module checks the criterion against the one class of
groups whose property `(T)` is not in doubt.

The answer is sharp: averaging over the *whole* of a finite group produces a
vector fixed by every element, so in a representation without invariant vectors
the average is not merely short --- it is `0`.  The gap constant is therefore
`0`, the criterion returns property `(T)` at tolerance one, and no appeal to
the almost-invariant-vector definition is made anywhere in the derivation.

The control is deliberately kept out of `OrbitAverageSpectralGap.lean`: the
criterion is the load-bearing statement and should not import a witness.
-/

namespace GroupApproximation
namespace SpectralGap

universe u v

variable {G : Type u} [Group G]

/-- **A finite group has the sharpest possible gap.**  Averaging over the whole
of a finite group produces a vector fixed by every element, because left
translation permutes the group; so in a representation with no invariant vector
the average is not merely short, it is zero, and the gap constant is `0`.

This is the positive control for `isKazhdanPair_of_orbitAverageGap`: fed through
that theorem it returns property `(T)` for every finite group, at tolerance one,
which is the correct answer and is obtained here without any appeal to the
almost-invariant-vector definition. -/
theorem orbitAverageGap_univ_of_fintype [Fintype G] :
    OrbitAverageGap.{u, v} G (Finset.univ : Finset G) 0 := by
  classical
  intro E _ _ _ ρ hno x
  have hstep : ∀ h g : G, ρ h (ρ g x) = ρ (h * g) x := by
    intro h g
    simp [map_mul]
  have hinv : ∀ h : G,
      ρ h (IsKazhdanPair.orbitAverage (Finset.univ : Finset G) ρ x)
        = IsKazhdanPair.orbitAverage (Finset.univ : Finset G) ρ x := by
    intro h
    have hsum : ∑ g : G, ρ h (ρ g x) = ∑ g : G, ρ g x := by
      calc ∑ g : G, ρ h (ρ g x) = ∑ g : G, ρ (h * g) x :=
            Finset.sum_congr rfl fun g _ ↦ hstep h g
        _ = ∑ g : G, ρ g x :=
            Function.Bijective.sum_comp (Group.mulLeft_bijective h) fun g ↦ ρ g x
    rw [IsKazhdanPair.orbitAverage, map_smul, map_sum, hsum]
  have hzero : IsKazhdanPair.orbitAverage (Finset.univ : Finset G) ρ x = 0 :=
    hno _ hinv
  simp [hzero]

/-- **Every finite group has property `(T)`, through the spectral criterion.**
The tolerance is one: in a finite group no representation without invariant
vectors admits a unit vector moved by less than one by every element, because
the whole-group average of such a vector would be a nonzero invariant one. -/
theorem hasKazhdanPropertyT_of_fintype [Fintype G] :
    HasKazhdanPropertyT.{u, v} G :=
  hasKazhdanPropertyT_of_orbitAverageGap (S := (Finset.univ : Finset G))
    ⟨1, Finset.mem_univ 1⟩ (lam := 0) zero_lt_one orbitAverageGap_univ_of_fintype

end SpectralGap
end GroupApproximation
