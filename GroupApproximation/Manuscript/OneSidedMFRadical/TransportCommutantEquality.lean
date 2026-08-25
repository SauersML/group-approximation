import GroupApproximation.Manuscript.OneSidedMFRadical.TransportAssembly
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceCentralizerCommutatorClosure

/-!
# `thm:transport` in its commutant-equality form

The manuscript states Theorem `thm:transport` as an equality of sets.  Writing
`C₂(V, L)` for the bounded matrix sequences that asymptotically commute with
`V(L)` in normalized Hilbert--Schmidt norm, and `Ad(V(u))` for coordinatewise
conjugation, the printed conclusion is

    Ad(V(u)) (C₂(V, L)) = C₂(V, L).

`OneSidedKazhdanTransportPackage` already carries both halves of the content:
applied to a member of `C₂(V, L)` it returns that *both* the conjugate and the
inverse conjugate are again bounded and again asymptotically central.  What it
does not say is that those two operations are mutually inverse, which is what
turns two containments into the printed equality.  That is
`adjointSequence_coadjointSequence`, and it is pure unitarity: `U (U⋆ x U) U⋆`
telescopes through `U U⋆ = 1`.

The printed proof's last two sentences are the two containments:

> Thus `Ad(V(u))` and its inverse both preserve `C₂(V, L)`, which proves the
> equality.

and the projection step that produces them,

> Lemma `lem:stable-finite` therefore gives `U⋆PU = P`, so `U` commutes with
> `P`.

is `commute_of_star_conjugate_eq`, stated for any monoid with a star: the
passage from a conjugation identity to a commutation is algebra, not analysis,
and separating it keeps the ultraproduct argument out of the step that only
rearranges it.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open KazhdanAsymptoticCommutant
open scoped Matrix.Norms.L2Operator

/-! ## From the projection identity to a commutation -/

/-- **"so `U` commutes with `P`".**  Once stable finiteness has upgraded the
domination `U⋆PU ≤ P` to the identity `U⋆PU = P`, commutation is immediate:
multiply on the left by `U` and use `U U⋆ = 1`.

Stated for an arbitrary monoid with a star operation, because that is all the
step uses.  In the printed proof `U = σ̃(u)` and `P` is the image of the Kazhdan
projection, both in the corona `ℬ`. -/
theorem commute_of_star_conjugate_eq {M : Type*} [Monoid M] [Star M]
    {U P : M} (hUU : U * star U = 1) (h : star U * P * U = P) :
    Commute U P := by
  have hPU : P * U = U * P := by
    calc P * U = (U * star U) * (P * U) := by rw [hUU, one_mul]
      _ = U * (star U * P * U) := by simp [mul_assoc]
      _ = U * P := by rw [h]
  exact (hPU.symm : U * P = P * U)

/-! ## The two conjugations are mutually inverse -/

variable {G : Type} [Group G]

/-- Conjugating by `V_n(u)` and then by `V_n(u)⋆` returns the sequence
unchanged.  This is the only new ingredient the equality needs beyond the
transport package. -/
theorem adjointSequence_coadjointSequence (B : OpAlmostRepresentation G) (g : G)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) :
    adjointSequence B g (coadjointSequence B g x) = x := by
  funext n
  have hU : (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
      (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.mul_star_self_of_mem (B.map n g).2
  simp only [adjointSequence, coadjointSequence]
  calc (B.map n g : Matrix (B.model n) (B.model n) ℂ) *
        ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ)) *
        (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ
      = ((B.map n g : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ) * x n *
          ((B.map n g : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
        noncomm_ring
    _ = x n := by rw [hU, one_mul, mul_one]

/-- Conjugating by `V_n(u)⋆` and then by `V_n(u)` likewise returns the sequence
unchanged. -/
theorem coadjointSequence_adjointSequence (B : OpAlmostRepresentation G) (g : G)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) :
    coadjointSequence B g (adjointSequence B g x) = x := by
  funext n
  have hU : (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ *
      (B.map n g : Matrix (B.model n) (B.model n) ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Unitary.star_mul_self_of_mem (B.map n g).2
  simp only [adjointSequence, coadjointSequence]
  calc (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ *
        ((B.map n g : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
        (B.map n g : Matrix (B.model n) (B.model n) ℂ)
      = ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ)) * x n *
          ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            (B.map n g : Matrix (B.model n) (B.model n) ℂ)) := by
        noncomm_ring
    _ = x n := by rw [hU, one_mul, mul_one]

/-! ## The printed set and the printed equality -/

/-- **The printed `C₂(V, L)`.**  The bounded matrix sequences whose
Hilbert--Schmidt commutators with `V(ℓ)` vanish for every `ℓ ∈ L`. -/
def boundedHSCommutant (B : OpAlmostRepresentation G) (L : Subgroup G) :
    Set (∀ n, Matrix (B.model n) (B.model n) ℂ) :=
  {x | IsUniformlyBounded B x ∧ IsAsymptoticCommutantOf B L.subtype x}

/-- **Theorem `thm:transport`, in the printed form.**  A one-sided compressor
of a property-`(T)` subgroup carries the bounded Hilbert--Schmidt asymptotic
commutant of `V(L)` onto itself. -/
def OneSidedKazhdanTransportCommutantEquality : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} L →
    ∀ (B : OpAlmostRepresentation G) (u : G), u ∈ compressionSet L →
      adjointSequence B u '' boundedHSCommutant B L = boundedHSCommutant B L

/-- Closed proof of the printed equality.

`⊆` is the adjoint half of the transport package.  `⊇` is the coadjoint half
together with mutual inverseness: a member `y` of the commutant is the image of
`Ad(V(u))⁻¹ y`, which the package puts back in the commutant. -/
theorem manuscriptOneSidedKazhdanTransportCommutantEquality :
    OneSidedKazhdanTransportCommutantEquality := by
  intro G _ L hT B u hu
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨x, ⟨hxb, hxc⟩, rfl⟩
    obtain ⟨⟨hb, hc⟩, -⟩ :=
      manuscriptOneSidedKazhdanTransportPackage G L hT B x hxc hxb u hu
    exact ⟨hb, hc⟩
  · intro y hy
    obtain ⟨-, ⟨hb, hc⟩⟩ :=
      manuscriptOneSidedKazhdanTransportPackage G L hT B y hy.2 hy.1 u hu
    exact ⟨coadjointSequence B u y, ⟨hb, hc⟩,
      adjointSequence_coadjointSequence B u y⟩


/-! ## The centralizer sequence is a member of the printed commutant -/

/-- **"If `c ∈ C_G(L)`, then `(V_n(c)) ∈ C₂(V, L)`."**

Boundedness is unitarity.  Membership in the asymptotic commutant is the
printed "asymptotically commutes in operator norm and hence in normalized
Hilbert--Schmidt norm", turned from a commutator into the conjugation
displacement `IsAsymptoticCommutantOf` is stated with, by right-unitary
invariance of `‖·‖₂`: `A V − V A = (A − V A V⋆) V`. -/
theorem centralizerSequence_mem_boundedHSCommutant
    (B : OpAlmostRepresentation G) (L : Subgroup G) (c : G)
    (hc : ∀ ell ∈ L, Commute c ell) :
    (fun n ↦ (B.map n c : Matrix (B.model n) (B.model n) ℂ))
      ∈ boundedHSCommutant B L := by
  refine ⟨⟨1, zero_le_one, fun n ↦ ?_⟩, ?_⟩
  · letI : Nonempty (B.model n) := Fintype.card_pos_iff.mp (B.modelNonempty n)
    exact (CStarRing.norm_of_mem_unitary (B.map n c).2).le
  · intro gamma
    have hcomm := manuscriptSentence148_centralizerSequence B L.subtype c
      (fun g ↦ hc g g.property) gamma
    have hsq : Tendsto
        (fun n ↦ hsNormSq (B.model n)
          ((B.map n c : Matrix (B.model n) (B.model n) ℂ) *
              B.map n (L.subtype gamma) -
            (B.map n (L.subtype gamma) : Matrix (B.model n) (B.model n) ℂ) *
              B.map n c)) atTop (nhds 0) := by
      have := hcomm.2.pow 2
      simpa [Real.sq_sqrt, hsNormSq_nonneg] using this
    intro ε hε
    obtain ⟨N, hN⟩ :=
      (tendsto_order.mp hsq).2 ε hε |>.exists_forall_of_atTop
    refine ⟨N, fun n hn ↦ ?_⟩
    have hkey : hsNormSq (B.model n)
        ((B.map n c : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (L.subtype gamma) : Matrix (B.model n) (B.model n) ℂ) *
            B.map n c *
            (B.map n (L.subtype gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        = hsNormSq (B.model n)
          ((B.map n c : Matrix (B.model n) (B.model n) ℂ) *
              B.map n (L.subtype gamma) -
            (B.map n (L.subtype gamma) : Matrix (B.model n) (B.model n) ℂ) *
              B.map n c) := by
      rw [← hsDistSq_conj_eq_hsNormSq_commutator (B.model n)
        (B.map n (L.subtype gamma)).2
        (B.map n c : Matrix (B.model n) (B.model n) ℂ)]
      rw [hsDistSq]
      rw [← hsNormSq_neg]
      ring_nf
    rw [hkey]
    exact (hN n hn).le

end OneSidedMFRadical
end Manuscript
end GroupApproximation
