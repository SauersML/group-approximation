import GroupApproximation.GGT.OsinTheorem54SepLemma58

/-!
# The finite-code conclusion of Osin's Lemma 5.11

The geometric part of Osin's proof chooses a separating coset shared by a
geodesic from `1` to `z` and its translate by `k`.  If `u` and `v` are the two
entrance points, the proof obtains

`k = u * (u⁻¹ * v) * (k⁻¹ * v)⁻¹`,

where both outer factors are entrance points of the fixed geodesic and the
middle factor lies in a relative ball of radius `3Dc`.  There are at most
`3R` choices for each entrance point when `|z| = R`, and the union of those
relative balls is finite because the family is finite and hyperbolically
embedded.

This module proves that final counting paragraph.  The remaining input is
`Lemma511EntranceEncoding`: exactly the geometric assertion that every element
with the two displacement bounds has such a code.  No finiteness or cardinal
bound is left in that input.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The elements simultaneously moving `1` and `z` by at most `m`, in the
basepoint form used by Lemma 5.11. -/
def ConjDisplacement (Y : RelGenSet G Λ) (m : ℕ) (z : G) : Set G :=
  {k : G | wordDist Y.alphabet.carrier 1 k ≤ m ∧
    wordDist Y.alphabet.carrier 1 (z⁻¹ * k * z) ≤ m}

/-- **The geometric residue of Osin's Lemma 5.11.**

At `R = 18m + 11`, every element of the double-displacement set is encoded by
two indices in a list of at most `3R` entrance points and one element of the
union of the original relative balls of radius `3Dc`.  This is equations
(37)--(38) and the entrance-point paragraph of the published proof, with its
final finite counting removed. -/
def Lemma511EntranceEncoding (D Y : RelGenSet G Λ) (Dc : ℕ) : Prop :=
  ∀ (m : ℕ) (z : G), wordDist Y.alphabet.carrier 1 z = 18 * m + 11 →
    ∃ entrance : Fin (3 * (18 * m + 11)) → G,
      ∀ k ∈ ConjDisplacement Y m z,
        ∃ (i j : Fin (3 * (18 * m + 11))) (a : G),
          a ∈ ⋃ lam : Λ, D.relBall lam (3 * Dc) ∧
            k = entrance i * a * (entrance j)⁻¹

/-- **The entrance encoding implies the exact-distance acylindricity core.**

The bound `N` is the cardinality of the finite code type
`Fin (3R) × (⋃_λ B̂_λ(3Dc)) × Fin (3R)`.  It depends on `m`, `D`, and `Dc`, but
not on `z`, which is precisely the uniformity Lemma 5.11 needs. -/
theorem acylindricalCore_of_entranceEncoding [Fintype Λ]
    (D Y : RelGenSet G Λ) (Dc : ℕ) (hemb : D.IsHyperbolicallyEmbedded)
    (hencode : Lemma511EntranceEncoding D Y Dc) :
    ∀ m : ℕ, ∃ R N : ℕ, 0 < R ∧ ∀ z : G,
      wordDist Y.alphabet.carrier 1 z = R →
        (ConjDisplacement Y m z).Finite ∧
          (ConjDisplacement Y m z).ncard ≤ N := by
  intro m
  let R : ℕ := 18 * m + 11
  let B : Set G := ⋃ lam : Λ, D.relBall lam (3 * Dc)
  have hB : B.Finite := by
    exact Set.finite_iUnion (fun lam : Λ => hemb.locallyFinite lam (3 * Dc))
  letI : Fintype ↥B := hB.fintype
  let Code : Type u := Fin (3 * R) × (↥B × Fin (3 * R))
  let N : ℕ := (Set.univ : Set Code).ncard
  refine ⟨R, N, ?_, ?_⟩
  · simp [R]
  · intro z hz
    obtain ⟨entrance, hentrance⟩ := hencode m z (by simpa [R] using hz)
    let decode : Code → G := fun c =>
      entrance c.1 * (c.2.1 : G) * (entrance c.2.2)⁻¹
    have hsub : ConjDisplacement Y m z ⊆ decode '' (Set.univ : Set Code) := by
      intro k hk
      obtain ⟨i, j, a, ha, hka⟩ := hentrance k hk
      have haB : a ∈ B := by simpa [B] using ha
      refine ⟨(i, ⟨⟨a, haB⟩, j⟩), Set.mem_univ _, ?_⟩
      exact hka.symm
    have huniv : (Set.univ : Set Code).Finite := Set.finite_univ
    have himage : (decode '' (Set.univ : Set Code)).Finite := huniv.image decode
    refine ⟨himage.subset hsub, ?_⟩
    exact le_trans (Set.ncard_le_ncard hsub himage)
      (le_trans (Set.ncard_image_le huniv) le_rfl)

end OsinComponents
end GGT
end GroupApproximation
