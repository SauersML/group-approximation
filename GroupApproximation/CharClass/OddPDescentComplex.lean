import GroupApproximation.CharClass.OddPDescentClifford

/-!
# `E^{⊗p}` is a complex, and the one-slot contraction is a full one

Deliverable (1) of the lane.  The differential is `eD = Σ_a eWedge a` — left multiplication
by `σ = ξ_0 + ⋯ + ξ_{p−1}` in the exterior reading, which is the Koszul tensor differential
"replace one `f` by `δf = g`, with the prefix sign" — and the contraction is
`eH = ePart 0`, the operator `h ⊗ 1^{⊗(p−1)}` of the program note, `h(g) = f`, `h(f) = 0`
applied in slot `0`.

```text
    eD ∘ eD = 0            eD ∘ eH + eH ∘ eD = 1
```

The second holds **on the nose, with no `ηε` residual**.  That is `sp-design`'s observation
that made the descent cheap: `E` is exact (`δ : E⁰ → E¹` is an isomorphism), so there is
nothing in the bottom degree for a residual to leak into and the ONE-slot contraction
suffices.  On singular chains the same one-slot recipe fails and the full
`Σ_l (ηε)^{⊗(l−1)} ⊗ s ⊗ 1^{⊗(p−l)}` is needed — the trap recorded in `sp-design`'s Φ
construction — but nothing in this lane ever leaves `E^{⊗p}`.

Both proofs are three lines on top of `OddPDescentClifford.lean`: the square is the
anticommutation summed over an involution of the index pairs, and the contraction identity
is the CAR relation summed over `b`, where every `b ≠ 0` contributes `0`.
-/

namespace GroupApproximation.CharClass

variable {p : ℕ} (K : Type) [CommRing K]

/-- **The differential of `E^{⊗p}`**: replace one `f` by `g`, in every slot in turn, with
the Koszul prefix sign.  Left multiplication by `σ = Σ_a ξ_a`. -/
noncomputable def eD : EMod K p →ₗ[K] EMod K p := ∑ a : Fin p, eWedge K a

/-- **The one-slot contraction** `h ⊗ 1^{⊗(p−1)}`. -/
noncomputable def eH [NeZero p] : EMod K p →ₗ[K] EMod K p := ePart K (0 : Fin p)

theorem eD_apply (x : EMod K p) : eD K x = ∑ a : Fin p, eWedge K a x := by
  rw [eD, LinearMap.sum_apply]

theorem eH_apply [NeZero p] (x : EMod K p) : eH K x = ePart K (0 : Fin p) x := rfl

/-- **`D ∘ D = 0`.**  The double sum is killed by the involution swapping the two indices:
off the diagonal the anticommutation pairs the two terms, and on the diagonal each term is
already `0`. -/
theorem eD_eD (x : EMod K p) : eD K (eD K x) = 0 := by
  have hpair : eD K (eD K x)
      = ∑ y : Fin p × Fin p, eWedge K y.1 (eWedge K y.2 x) := by
    rw [Fintype.sum_prod_type, eD_apply, eD_apply]
    exact Finset.sum_congr rfl fun a _ => map_sum (eWedge K a) _ _
  rw [hpair]
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) (fun _ => rfl)
  · intro y
    have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f x) (eWedge_anticomm K y.1 y.2)
    simpa using h
  · intro y hy hswap
    apply hy
    have h12 : y.1 = y.2 := by
      have := congrArg Prod.fst hswap
      simpa using this.symm
    rw [h12]
    have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f x) (eWedge_eWedge_self K y.2)
    simpa using h

theorem eD_comp_eD : (eD K).comp (eD K) = (0 : EMod K p →ₗ[K] EMod K p) := by
  refine eMod_ext K fun w => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  exact eD_eD K _

/-- **`D H + H D = 1`.**  Only the slot-`0` summand of `D` survives, and there the CAR
relation is the identity. -/
theorem eD_eH_add [NeZero p] (x : EMod K p) : eD K (eH K x) + eH K (eD K x) = x := by
  have hsum : eD K (eH K x) + eH K (eD K x)
      = ∑ b : Fin p, (eWedge K b (ePart K (0 : Fin p) x)
          + ePart K (0 : Fin p) (eWedge K b x)) := by
    simp only [eD_apply, eH, map_sum]
    rw [Finset.sum_add_distrib]
  rw [hsum, Finset.sum_eq_single (0 : Fin p)]
  · have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f x)
      (ePart_eWedge_self K (0 : Fin p))
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
    rw [add_comm]
    exact h
  · intro b _ hb
    have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f x)
      (ePart_eWedge_of_ne K (0 : Fin p) b (Ne.symm hb))
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h
    rw [add_comm]
    exact h
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eD_comp_eH_add [NeZero p] :
    (eD K).comp (eH K) + (eH K).comp (eD K) = (LinearMap.id : EMod K p →ₗ[K] EMod K p) := by
  refine eMod_ext K fun w => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
  exact eD_eH_add K _

end GroupApproximation.CharClass
