import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplit

/-!
# Splitting through the corona of the ideal

Lane `TWWSchafhauser-3d4`, work order `WO-TWWSchafhauser-3d-4`. G. A. Elliott and D. Kucerovsky,
*An abstract Voiculescu–Brown–Douglas–Fillmore absorption theorem*, Pacific J. Math. 198 (2001),
§1–2; C. Schafhauser, *A new proof of the Tikuisis–White–Winter theorem*, J. reine angew. Math.
759 (2020), §5.

For an extension `0 → J → E → Q → 0`, absorption and vanishing classes live in the corona
`C = M(J)/J`, where a Cuntz pair exists once `J` is stable. They do not live in `Q` itself: a
quotient with a faithful trace has no Cuntz pair (3c, `ExtensionFiniteTrace`). Here the extension
is presented by its *corona square*:

* `ι : E → M` injective (`E ⊆ M(J)`), `π : E → Q`, `π' : M → C`, and `κ : Q → C` injective, with
  `π' ∘ ι = κ ∘ π`;
* `hpull`: `π' m ∈ κ(Q)` forces `m ∈ ι(E)` (so `E` is the pullback `π'⁻¹(κ(Q))`, because `J ⊆ E`).

* `busbyRestrict`: corestriction of a `⋆`-homomorphism into `M` with values in `ι(E)`.
* `isTrivialBusby_of_corona`: if the Busby map `κ ∘ θ` is strongly absorbing and strongly stably
  trivial in `C`, then `θ` has a genuine lift `ψ : S → E` with `π ∘ ψ = θ`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

section Corona

variable {R : Type*} [CommSemiring R]
variable {S : Type*} [Semiring S] [Algebra R S] [Star S]
variable {E : Type*} [Ring E] [StarRing E] [Algebra R E]
variable {M : Type*} [Ring M] [StarRing M] [Algebra R M]

/-- Corestriction of a `⋆`-homomorphism `ψ : S → M` whose values lie in the image of an injective
`⋆`-homomorphism `ι : E → M`. -/
noncomputable def busbyRestrict (ι : E →⋆ₐ[R] M) (hι : Function.Injective ι) (ψ : S →⋆ₐ[R] M)
    (hψ : ∀ s, ∃ e, ι e = ψ s) : S →⋆ₐ[R] E where
  toFun s := Classical.choose (hψ s)
  map_one' := hι (by
    show ι (Classical.choose (hψ 1)) = ι 1
    rw [Classical.choose_spec (hψ 1), map_one ψ, map_one ι])
  map_mul' x y := hι (by
    show ι (Classical.choose (hψ (x * y))) = ι (Classical.choose (hψ x) * Classical.choose (hψ y))
    rw [map_mul ι, Classical.choose_spec (hψ (x * y)), Classical.choose_spec (hψ x),
      Classical.choose_spec (hψ y), map_mul ψ x y])
  map_zero' := hι (by
    show ι (Classical.choose (hψ 0)) = ι 0
    rw [Classical.choose_spec (hψ 0), map_zero ψ, map_zero ι])
  map_add' x y := hι (by
    show ι (Classical.choose (hψ (x + y))) = ι (Classical.choose (hψ x) + Classical.choose (hψ y))
    rw [map_add ι, Classical.choose_spec (hψ (x + y)), Classical.choose_spec (hψ x),
      Classical.choose_spec (hψ y), map_add ψ x y])
  commutes' r := hι (by
    show ι (Classical.choose (hψ (algebraMap R S r))) = ι (algebraMap R E r)
    rw [Classical.choose_spec (hψ (algebraMap R S r)), AlgHomClass.commutes ψ r,
      AlgHomClass.commutes ι r])
  map_star' x := hι (by
    show ι (Classical.choose (hψ (star x))) = ι (star (Classical.choose (hψ x)))
    rw [map_star ι, Classical.choose_spec (hψ (star x)), Classical.choose_spec (hψ x),
      map_star ψ x])

theorem busbyRestrict_apply (ι : E →⋆ₐ[R] M) (hι : Function.Injective ι) (ψ : S →⋆ₐ[R] M)
    (hψ : ∀ s, ∃ e, ι e = ψ s) (s : S) : ι (busbyRestrict ι hι ψ hψ s) = ψ s :=
  Classical.choose_spec (hψ s)

variable {Q : Type*} [Ring Q] [StarRing Q] [Algebra R Q]
variable {C : Type*} [Ring C] [StarRing C] [Algebra R C]

/-- **Absorbing plus stably trivial in the corona implies split** (Elliott–Kucerovsky 2001, §2;
Schafhauser 2020, §5). Take an extension `E → Q` presented by its corona square
`π' ∘ ι = κ ∘ π` into `C = M(J)/J`. If the Busby map `κ ∘ θ` strongly absorbs `𝒯` and is
strongly stably trivial, then `θ` lifts to a `⋆`-homomorphism `ψ : S → E`. -/
theorem isTrivialBusby_of_corona {ι : E →⋆ₐ[R] M} {π : E →⋆ₐ[R] Q} {π' : M →⋆ₐ[R] C}
    {κ : Q →⋆ₐ[R] C} (hι : Function.Injective ι) (hκ : Function.Injective κ)
    (hcomm : ∀ e, π' (ι e) = κ (π e)) (hpull : ∀ m q, π' m = κ q → ∃ e, ι e = m)
    {P : BusbyCuntzPair C} {𝒯 : Set (S →⋆ₐ[R] M)} {θ : S →⋆ₐ[R] Q}
    (habs : IsStronglyAbsorbingBusby π' P 𝒯 (κ.comp θ))
    (hst : IsStronglyStablyTrivialBusby π' P 𝒯 (κ.comp θ)) : IsTrivialBusby π θ := by
  obtain ⟨ψ, hψ⟩ := isTrivialBusby_of_isStronglyAbsorbingBusby_of_isStablyTrivialBusby habs hst
  have hψE : ∀ s, ∃ e, ι e = ψ s := fun s => hpull (ψ s) (θ s) (hψ s)
  refine ⟨busbyRestrict ι hι ψ hψE, fun s => hκ ?_⟩
  rw [← hcomm (busbyRestrict ι hι ψ hψE s), busbyRestrict_apply ι hι ψ hψE s, hψ s,
    StarAlgHom.comp_apply]

end Corona

end GroupApproximation.Full.TWWSchafhauser
