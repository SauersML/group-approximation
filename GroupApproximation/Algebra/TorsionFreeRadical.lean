import GroupApproximation.Algebra.GroupTorsionFree
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The torsion-free radical

Chiodo, *On torsion in finitely presented groups* (arXiv:1107.1489v4), §3,
studies the smallest normal subgroup of a group with torsion-free quotient.
He introduces it twice: once transfinitely, as the union `Tor_∞(G)` of an
increasing tower of normal closures (Definition 3.1, formalized in
`Algebra.TorsionFreeRadicalTower`), and once by its universal property, as
the *torsion-free radical* `ρ(G)`.  Proposition 3.3 says the two agree.

This file is the second description, and it is the one the rest of the
development runs on, because it is the description that proves things.  The
key observation, which is what keeps the whole file short, is that the
property "`G ⧸ N` is torsion-free" is an *internal* property of `N`:

    ∀ g n, 0 < n → g ^ n ∈ N → g ∈ N,

called `IsIsolated` here.  Isolatedness is manifestly preserved by arbitrary
intersections --- if every `N` in a family absorbs `g` because it absorbs
`g ^ n`, so does the intersection --- whereas "has torsion-free quotient" is
a statement about a quotient type and says nothing about intersections on its
face.  So `torsionFreeRadical G`, defined as the infimum of the normal
isolated subgroups, is itself normal and isolated, and therefore *is* one of
the subgroups it is the infimum of.  Chiodo's Corollary 3.4 --- `G ⧸ ρ(G)` is
torsion-free and every homomorphism to a torsion-free group factors through
it --- is then two lines each, and the transfinite tower is not needed for
any of it.

## Contents

* `IsIsolated` --- the internal form of "the quotient is torsion-free".
* `isPowerTorsionFree_quotient_iff` --- that the internal form is correct.
* `torsionFreeRadical` --- Chiodo's `ρ(G)`.
* `isIsolated_torsionFreeRadical`, `torsionFreeRadical_normal` --- the radical
  is one of the subgroups it is an infimum of.  This is the whole content.
* `torsionFreeRadical_le_ker` --- Corollary 3.4's factorization, in the form
  every later file uses: a homomorphism to a torsion-free group kills the
  radical.
* `torsionFreeRadical_eq_bot_iff` --- the radical is trivial exactly for
  torsion-free groups, so `ρ` is idempotent in the only sense needed.
* `torsionFreeRadical_le_comap`, `map_torsionFreeRadical_le` --- functoriality.

Nothing here is conditional on anything: the file has no hypotheses beyond
`Group`, and imports only `Algebra.GroupTorsionFree` and Mathlib's quotient
groups.
-/

namespace GroupApproximation
namespace Chiodo

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-! ## 1.  Isolated subgroups -/

/-- **A subgroup is isolated when it absorbs every root of its elements.**

For a normal `N` this is exactly the statement that `G ⧸ N` is torsion-free
(`isPowerTorsionFree_quotient_iff`), but written without mentioning the
quotient, which is what makes it stable under intersections. -/
def IsIsolated (N : Subgroup G) : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n ∈ N → g ∈ N

/-- The trivial subgroup is normal.  Proved here in three lines rather than
cited, so that the file does not depend on the spelling of Mathlib's
instance. -/
theorem normal_bot : (⊥ : Subgroup G).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_bot] at hn ⊢
  rw [hn]
  simp

/-- The trivial subgroup is isolated exactly when the group is
torsion-free. -/
theorem isIsolated_bot_iff : IsIsolated (⊥ : Subgroup G) ↔ IsPowerTorsionFree G := by
  constructor
  · intro h g n hn hpow
    exact Subgroup.mem_bot.mp (h g n hn (Subgroup.mem_bot.mpr hpow))
  · intro h g n hn hpow
    exact Subgroup.mem_bot.mpr (h g n hn (Subgroup.mem_bot.mp hpow))

/-- The kernel of a homomorphism into a torsion-free group is isolated. -/
theorem isIsolated_ker (f : G →* H) (hH : IsPowerTorsionFree H) :
    IsIsolated (MonoidHom.ker f) := by
  intro g n hn hpow
  rw [MonoidHom.mem_ker] at hpow ⊢
  refine hH (f g) n hn ?_
  rw [← map_pow]
  exact hpow

/-- Isolatedness is preserved by preimages. -/
theorem isIsolated_comap {N : Subgroup H} (hN : IsIsolated N) (f : G →* H) :
    IsIsolated (N.comap f) := by
  intro g n hn hpow
  rw [Subgroup.mem_comap] at hpow ⊢
  rw [map_pow] at hpow
  exact hN (f g) n hn hpow

/-- **Isolatedness is preserved by arbitrary intersections.**  This is the
property the torsion-free radical is built on, and the reason the transfinite
tower of Chiodo's Definition 3.1 can be avoided. -/
theorem isIsolated_sInf {S : Set (Subgroup G)} (h : ∀ N ∈ S, IsIsolated N) :
    IsIsolated (sInf S) := by
  intro g n hn hpow
  rw [Subgroup.mem_sInf] at hpow ⊢
  intro N hN
  exact h N hN g n hn (hpow N hN)

/-- **Isolatedness is the internal form of a torsion-free quotient.** -/
theorem isPowerTorsionFree_quotient_iff (N : Subgroup G) [N.Normal] :
    IsPowerTorsionFree (G ⧸ N) ↔ IsIsolated N := by
  constructor
  · intro h
    have hker : IsIsolated (MonoidHom.ker (QuotientGroup.mk' N)) :=
      isIsolated_ker (QuotientGroup.mk' N) h
    rwa [QuotientGroup.ker_mk'] at hker
  · intro h x n hn hpow
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hmap : QuotientGroup.mk' N (g ^ n) = 1 := by
      rw [map_pow]
      exact hpow
    have hmem : g ^ n ∈ N := by
      have hker : g ^ n ∈ MonoidHom.ker (QuotientGroup.mk' N) :=
        MonoidHom.mem_ker.mpr hmap
      rwa [QuotientGroup.ker_mk'] at hker
    have hg : g ∈ N := h g n hn hmem
    have hgk : g ∈ MonoidHom.ker (QuotientGroup.mk' N) := by
      rwa [QuotientGroup.ker_mk']
    exact MonoidHom.mem_ker.mp hgk

/-! ## 2.  The radical -/

/-- **Chiodo's torsion-free radical `ρ(G)`**: the smallest normal subgroup
with torsion-free quotient, taken as the infimum of all of them.

That the infimum is again one of them is `torsionFreeRadical_normal` together
with `isIsolated_torsionFreeRadical`, and that pair is the whole content of
Chiodo's Corollary 3.4. -/
def torsionFreeRadical (G : Type u) [Group G] : Subgroup G :=
  sInf {N : Subgroup G | N.Normal ∧ IsIsolated N}

/-- Membership in the radical, unfolded. -/
theorem mem_torsionFreeRadical_iff {g : G} :
    g ∈ torsionFreeRadical G ↔
      ∀ N : Subgroup G, N.Normal → IsIsolated N → g ∈ N := by
  unfold torsionFreeRadical
  rw [Subgroup.mem_sInf]
  constructor
  · intro h N hnormal hiso
    exact h N ⟨hnormal, hiso⟩
  · rintro h N ⟨hnormal, hiso⟩
    exact h N hnormal hiso

/-- The radical is contained in every normal isolated subgroup. -/
theorem torsionFreeRadical_le {N : Subgroup G} (hnormal : N.Normal)
    (hiso : IsIsolated N) : torsionFreeRadical G ≤ N :=
  fun _ hg => mem_torsionFreeRadical_iff.mp hg N hnormal hiso

/-- The radical is normal, being an intersection of normal subgroups. -/
instance torsionFreeRadical_normal : (torsionFreeRadical G).Normal := by
  constructor
  intro n hn g
  rw [mem_torsionFreeRadical_iff] at hn ⊢
  intro N hnormal hiso
  exact hnormal.conj_mem n (hn N hnormal hiso) g

/-- The radical is isolated, being an intersection of isolated subgroups. -/
theorem isIsolated_torsionFreeRadical : IsIsolated (torsionFreeRadical G) := by
  unfold torsionFreeRadical
  refine isIsolated_sInf ?_
  rintro N ⟨-, hiso⟩
  exact hiso

/-- **Corollary 3.4, first half.**  The quotient by the radical is
torsion-free. -/
theorem isPowerTorsionFree_quotient_torsionFreeRadical :
    IsPowerTorsionFree (G ⧸ torsionFreeRadical G) :=
  (isPowerTorsionFree_quotient_iff _).mpr isIsolated_torsionFreeRadical

/-- **Corollary 3.4, second half.**  Every homomorphism into a torsion-free
group kills the radical.  Every use of the universal property in this
development is an instance of this one line. -/
theorem torsionFreeRadical_le_ker (f : G →* H) (hH : IsPowerTorsionFree H) :
    torsionFreeRadical G ≤ MonoidHom.ker f :=
  torsionFreeRadical_le (MonoidHom.normal_ker f) (isIsolated_ker f hH)

/-- The value form of `torsionFreeRadical_le_ker`. -/
theorem map_eq_one_of_mem_torsionFreeRadical (f : G →* H)
    (hH : IsPowerTorsionFree H) {g : G} (hg : g ∈ torsionFreeRadical G) :
    f g = 1 :=
  MonoidHom.mem_ker.mp (torsionFreeRadical_le_ker f hH hg)

/-- **The radical is trivial exactly for torsion-free groups.** -/
theorem torsionFreeRadical_eq_bot_iff :
    torsionFreeRadical G = ⊥ ↔ IsPowerTorsionFree G := by
  constructor
  · intro h
    rw [← isIsolated_bot_iff, ← h]
    exact isIsolated_torsionFreeRadical
  · intro h
    exact le_bot_iff.mp
      (torsionFreeRadical_le normal_bot (isIsolated_bot_iff.mpr h))

/-- Functoriality, in preimage form. -/
theorem torsionFreeRadical_le_comap (f : G →* H) :
    torsionFreeRadical G ≤ (torsionFreeRadical H).comap f :=
  torsionFreeRadical_le (Subgroup.Normal.comap inferInstance f)
    (isIsolated_comap isIsolated_torsionFreeRadical f)

/-- Functoriality, in image form: `ρ` is a subfunctor of the identity. -/
theorem map_torsionFreeRadical_le (f : G →* H) :
    (torsionFreeRadical G).map f ≤ torsionFreeRadical H :=
  Subgroup.map_le_iff_le_comap.mpr (torsionFreeRadical_le_comap f)

/-- The radical lands in the radical: the elementwise form of
`map_torsionFreeRadical_le`. -/
theorem mem_torsionFreeRadical_map (f : G →* H) {g : G}
    (hg : g ∈ torsionFreeRadical G) : f g ∈ torsionFreeRadical H :=
  Subgroup.mem_comap.mp (torsionFreeRadical_le_comap f hg)

end Chiodo
end GroupApproximation
