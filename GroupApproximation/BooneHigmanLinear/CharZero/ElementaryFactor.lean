import GroupApproximation.BooneHigman.Coordinates.FGSubring
import GroupApproximation.BooneHigman.Coordinates.MatrixEmbedding
import GroupApproximation.BooneHigman.Metabelian.AbsorptionEmbedding
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinTransport
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Leavitt.ElementaryStabilization
import GroupApproximation.Meta.AxiomGuard

/-!
# Elementary coordinates without Suslin's theorem

The linear host of the metabelian chain maps a finitely generated `H ≤ GL_n(K)` to
`GL_M(S)`, `S` a polynomial ring over `ℤ[1/m]` or `F_p`. It then absorbs `GL_M(S)` into the
elementary group `E_N(S)` through `g ↦ diag(g, g⁻ᵀ, 1)`. That step needs `SL_N(S) = E_N(S)`,
which is Suslin's theorem over polynomial rings (`Absorption.PolynomialSuslinStatement`, and on
route A the owed input `S1`).

This file shows that absorption over `S` is not needed. The rank bookkeeping is the only change.
Put the elementary factorizations in first, over the field, and choose the coefficient ring only
afterwards.

1. Over a field, `SL_N(K) = E_N(K)` by Gaussian elimination
   (`Absorption.specialLinearInElementary_of_field`). So for a finitely generated `G` and an
   injective `ρ : G →* GL_n(K)`, the injective homomorphism
   `g ↦ diag(ρ g, (ρ g)⁻ᵀ, 1) : G →* GL_{2n+2}(K)` takes values in `E_{2n+2}(K)`.
2. Each value on a generator is a finite product of elementary matrices `x_{ij}(c)`, `c ∈ K`
   (`exists_finset_elementary`, by induction on the subgroup closure). So there is a finite set
   `s ⊆ K`: the matrix entries, plus the coefficients `c` of these factorizations. For every
   subring `B ⊇ s` the homomorphism factors through `E_{2n+2}(B)`
   (`exists_finset_factor_elementary`, `exists_finset_elementary_embedding`).
3. A matrix embedding `B ↪ M_d(P)` of the coefficient ring carries `E_N(B)` injectively into
   `E_{N·d}(P)`: apply it entrywise, flatten the blocks (`elementaryBlockEquiv`), and reindex. It
   then stabilizes to `E_{N·d+r}(P)` for any `r` (`exists_elementary_transport`).

Steps 1–3 hold in every characteristic. The coordinate lemmas of the chain
(`CharZeroHost.fgSubringCoordinates`, and the char-`p` ring embedding) accept any finite set of
entries, so the finite set `s` of step 2 can be handed to them. The characteristic-zero and
characteristic-`p` hosts built on this are in `CharZero/ElementaryHost.lean` and
`CharZero/CharPElementaryHost.lean`.

No new input: every step uses proved lemmas of the corpus (`Leavitt/ElementaryGroup`,
`Leavitt/ElementaryStabilization`, `Coordinates/FGSubring`, `Metabelian/AbsorptionEmbedding`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace NoSuslin

open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.Metabelian

section Subring

variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Finite coefficient support.** An elementary matrix over `K` is elementary over every subring
containing a certain finite set of coefficients. -/
theorem exists_finset_elementary {x : (Matrix ι ι K)ˣ} (hx : x ∈ elementaryGroup ι K) :
    ∃ s : Finset K, ∀ B : Subring K, (↑s : Set K) ⊆ B →
      x ∈ (elementaryGroup ι B).map (elementaryMatrixUnitMap B.subtype) := by
  classical
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      refine ⟨{a}, fun B hB => ?_⟩
      have ha : a ∈ B := hB (Finset.mem_coe.2 (Finset.mem_singleton_self a))
      exact ⟨elementaryUnit i j hij ⟨a, ha⟩, elementaryUnit_mem i j hij _,
        elementaryMatrixUnitMap_elementaryUnit B.subtype i j hij ⟨a, ha⟩⟩
  | one => exact ⟨∅, fun B _ => one_mem _⟩
  | mul x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨s', hs'⟩ := hy
      refine ⟨s ∪ s', fun B hB => mul_mem (hs B fun z hz => hB ?_) (hs' B fun z hz => hB ?_)⟩
      · exact Finset.mem_coe.2 (Finset.mem_union.2 (Or.inl (Finset.mem_coe.1 hz)))
      · exact Finset.mem_coe.2 (Finset.mem_union.2 (Or.inr (Finset.mem_coe.1 hz)))
  | inv x _ hx =>
      obtain ⟨s, hs⟩ := hx
      exact ⟨s, fun B hB => inv_mem (hs B hB)⟩

#audit_axioms exists_finset_elementary

/-- `E_ι(B) → E_ι(K)` is injective for a subring `B ⊆ K`, already on the level of units. -/
theorem elementaryMatrixUnitMap_subtype_injective (B : Subring K) :
    Function.Injective (elementaryMatrixUnitMap (ι := ι) B.subtype) :=
  Units.map_injective (f := (B.subtype.mapMatrix (m := ι)).toMonoidHom)
    (Matrix.map_injective Subtype.val_injective)

#audit_axioms elementaryMatrixUnitMap_subtype_injective

/-- **Elementary factorization through a subring.** A homomorphism from a finitely generated group
to `GL_ι(K)` with values in `E_ι(K)` factors through `E_ι(B)` for every subring `B` containing a
certain finite set. -/
theorem exists_finset_factor_elementary {G : Type*} [Group G] [hG : Group.FG G]
    (φ : G →* (Matrix ι ι K)ˣ) (hφ : ∀ g, φ g ∈ elementaryGroup ι K) :
    ∃ s : Finset K, ∀ B : Subring K, (↑s : Set K) ⊆ B →
      ∃ φ' : G →* elementaryGroup ι B,
        ∀ g, elementaryMatrixUnitMap B.subtype (φ' g : (Matrix ι ι B)ˣ) = φ g := by
  classical
  obtain ⟨T, hT⟩ := hG.out
  obtain ⟨s₀, hs₀⟩ := Coordinates.exists_finset_factor (n := ι) φ
  choose s hs using fun t : G => exists_finset_elementary (hφ t)
  refine ⟨s₀ ∪ T.biUnion s, fun B hB => ?_⟩
  obtain ⟨ρ, hρ⟩ := hs₀ B fun z hz =>
    hB (Finset.mem_coe.2 (Finset.mem_union.2 (Or.inl (Finset.mem_coe.1 hz))))
  have hρg : ∀ g, elementaryMatrixUnitMap B.subtype (ρ g) = φ g := fun g =>
    DFunLike.congr_fun hρ g
  have hgen : ∀ t ∈ T, ρ t ∈ elementaryGroup ι B := by
    intro t ht
    obtain ⟨y, hy, hyt⟩ := hs t B fun z hz =>
      hB (Finset.mem_coe.2 (Finset.mem_union.2
        (Or.inr (Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_coe.1 hz⟩))))
    have hyρ : y = ρ t :=
      elementaryMatrixUnitMap_subtype_injective B (hyt.trans (hρg t).symm)
    rw [← hyρ]
    exact hy
  have hle : Subgroup.closure (T : Set G) ≤ (elementaryGroup ι B).comap ρ := by
    rw [Subgroup.closure_le]
    intro t ht
    exact hgen t ht
  have hall : ∀ g, ρ g ∈ elementaryGroup ι B := fun g =>
    hle (hT ▸ Subgroup.mem_top g : g ∈ Subgroup.closure (T : Set G))
  exact ⟨ρ.codRestrict (elementaryGroup ι B) hall, fun g => hρg g⟩

#audit_axioms exists_finset_factor_elementary

end Subring

/-- **Elementary coordinates over a field.** For a finitely generated group `G` and an injective
`ρ : G →* GL_n(K)`, `K` a field, some finite `s ⊆ K` has the following property. For every
subring `B ⊇ s`, `G` embeds in `E_{2n+2}(B)`, through `g ↦ diag(ρ g, (ρ g)⁻ᵀ, 1, 1)`. -/
theorem exists_finset_elementary_embedding {K : Type*} [Field K] {G : Type*} [Group G]
    [Group.FG G] {n : ℕ} (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ) (hρ : Function.Injective ρ) :
    ∃ s : Finset K, ∀ B : Subring K, (↑s : Set K) ⊆ B →
      ∃ φ : G →* elementaryGroup (Fin (2 * n + 2)) B, Function.Injective φ := by
  have h2 : 2 * n ≤ 2 * n + 2 := by omega
  have hinj :
      Function.Injective ((Absorption.absorptionUnits (R := K) n (2 * n + 2) h2).comp ρ) :=
    (Absorption.absorptionUnits_injective (R := K) n (2 * n + 2) h2).comp hρ
  obtain ⟨s, hs⟩ := exists_finset_factor_elementary
    ((Absorption.absorptionUnits (R := K) n (2 * n + 2) h2).comp ρ) fun g =>
      Absorption.specialLinearInElementary_of_field K (by omega) _
        (Absorption.absorptionUnits_det n (2 * n + 2) h2 (ρ g))
  refine ⟨s, fun B hB => ?_⟩
  obtain ⟨φ, hφ⟩ := hs B hB
  refine ⟨φ, fun x y hxy => hinj ?_⟩
  rw [← hφ x, ← hφ y, hxy]

#audit_axioms exists_finset_elementary_embedding

/-- A coefficient homomorphism that is injective induces an injective map of elementary groups. -/
theorem elementaryGroupMap_injective {ι R S : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    [Ring S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (elementaryGroupMap (ι := ι) f) := by
  intro x y h
  have h' : elementaryMatrixUnitMap f (x : (Matrix ι ι R)ˣ) =
      elementaryMatrixUnitMap f (y : (Matrix ι ι R)ˣ) :=
    congrArg Subtype.val h
  exact Subtype.ext
    (Units.map_injective (f := (f.mapMatrix (m := ι)).toMonoidHom) (Matrix.map_injective hf) h')

#audit_axioms elementaryGroupMap_injective

/-- **Transport along a matrix embedding of the coefficient ring.** An injective ring homomorphism
`B →+* M_d(P)` carries `E_N(B)`, `N ≥ 2`, injectively into `E_{N·d+r}(P)` for every `r`: apply it
entrywise, flatten the blocks, reindex, and stabilize. -/
theorem exists_elementary_transport {B P : Type*} [Ring B] [CommRing P] {N d : ℕ} (hN : 2 ≤ N)
    (Φ : B →+* Matrix (Fin d) (Fin d) P) (hΦ : Function.Injective Φ) (r : ℕ) :
    ∃ f : elementaryGroup (Fin N) B →* elementaryGroup (Fin (N * d + r)) P,
      Function.Injective f := by
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  let e₁ : Fin N × Fin d ≃ Fin (N * d) := finProdFinEquiv
  let e₂ : Fin (N * d) ⊕ Fin r ≃ Fin (N * d + r) := finSumFinEquiv
  refine ⟨(elementaryReindexEquiv (R := P) e₂).toMonoidHom.comp
      ((elementaryStabilization (ι := Fin (N * d)) (κ := Fin r) (R := P)).comp
        ((elementaryReindexEquiv (R := P) e₁).toMonoidHom.comp
          ((elementaryBlockEquiv (ι := Fin N) (κ := Fin d) (R := P)).toMonoidHom.comp
            (elementaryGroupMap (ι := Fin N) Φ)))), ?_⟩
  exact (elementaryReindexEquiv (R := P) e₂).injective.comp
    ((elementaryStabilization_injective (ι := Fin (N * d)) (κ := Fin r) (R := P)).comp
      ((elementaryReindexEquiv (R := P) e₁).injective.comp
        ((elementaryBlockEquiv (ι := Fin N) (κ := Fin d) (R := P)).injective.comp
          (elementaryGroupMap_injective hΦ))))

#audit_axioms exists_elementary_transport

end NoSuslin
end BooneHigmanLinear
end GroupApproximation
