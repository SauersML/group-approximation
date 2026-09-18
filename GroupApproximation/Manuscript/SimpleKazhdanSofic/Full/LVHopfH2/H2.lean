import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopfH2.ChainsLowDegree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopfH2.Surjective
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopfH2.Injective

/-!
# Hopf formula: the Hopf multiplier is `groupHomology.H2` (lane LVHopfH2)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Hopf formula; Brown II.5 Thm 5.3).
For a surjection `f : F → G` from a free group, restricting the factor-set map `Φ` to Mathlib's
2-cycles gives a surjection `Ψ : Z₂(G, ℤ) → (R ∩ [F,F]) ⧸ [F,R]` (`Surjective.lean`) with kernel
`B₂(G, ℤ)` (`Injective.lean`).  The quotient map `Z₂ → H₂(G, ℤ)` has the same kernel, so the first
isomorphism theorem gives `hopfMultiplierAddEquivH2`.

* `hopfPsi hf : Z₂ →+ Additive (hopfMultiplier f)` and `hopfPsi_surjective`.
* `hopfPsi_ker_eq`: `ker Ψ = ker (Z₂ → H₂)`.
* `hopfMultiplierAddEquivH2 f hf : Additive (hopfMultiplier f) ≃+ H₂(G, ℤ)`.
-/

namespace GroupApproximation.Full.LVHopf

section H2

variable {G : Type} [Group G] {α : Type} {f : FreeGroup α →* G}

/-- `Ψ : Z₂(G, ℤ) → (R ∩ [F,F]) ⧸ [F,R]`, the factor set `Φ` on Mathlib's 2-cycles. -/
noncomputable def hopfPsi (hf : Function.Surjective f) :
    ↥(groupHomology.cycles₂ (Rep.trivial ℤ G ℤ)) →+ Additive ↥(hopfMultiplier f) :=
  AddMonoidHom.mk'
    (fun x => Additive.ofMul
      ⟨((Additive.toMul (hopfChainPhi hf x.1) : HopfExtK f) : HopfExt f),
        hopfChainPhi_mem_hopfMultiplier hf (hopfChainD_cycles₂ x)⟩)
    fun x y => Additive.ext (Subtype.ext
      (congrArg (fun z : Additive (HopfExtK f) => ((Additive.toMul z : HopfExtK f) : HopfExt f))
        (map_add (hopfChainPhi hf) x.1 y.1)))

theorem hopfPsi_val (hf : Function.Surjective f)
    (x : ↥(groupHomology.cycles₂ (Rep.trivial ℤ G ℤ))) :
    ((Additive.toMul (hopfPsi hf x) : ↥(hopfMultiplier f)) : HopfExt f) =
      ((Additive.toMul (hopfChainPhi hf x.1) : HopfExtK f) : HopfExt f) :=
  rfl

/-- `Ψ` is onto (Hopf formula, l.733-735). -/
theorem hopfPsi_surjective (hf : Function.Surjective f) : Function.Surjective (hopfPsi hf) := by
  intro m
  obtain ⟨hK, hC⟩ := (mem_hopfMultiplier_iff_ext
    ((Additive.toMul m : ↥(hopfMultiplier f)) : HopfExt f)).mp (Additive.toMul m).2
  obtain ⟨c, hc, hΦ⟩ := hopfChainPhi_exists_of_mem hf hK hC
  refine ⟨⟨c, hopfChain_mem_cycles₂ hc⟩, Additive.ext (Subtype.ext ?_)⟩
  exact (hopfPsi_val hf ⟨c, hopfChain_mem_cycles₂ hc⟩).trans
    (congrArg (fun z : Additive (HopfExtK f) => ((Additive.toMul z : HopfExtK f) : HopfExt f)) hΦ)

variable (G) in
/-- The quotient map `Z₂(G, ℤ) → H₂(G, ℤ)`, as an additive map. -/
noncomputable def hopfH2Pi :
    ↥(groupHomology.cycles₂ (Rep.trivial ℤ G ℤ)) →+ ↑(groupHomology.H2 (Rep.trivial ℤ G ℤ)) :=
  LinearMap.toAddMonoidHom (groupHomology.H2π (Rep.trivial ℤ G ℤ)).hom

theorem hopfH2Pi_surjective : Function.Surjective (hopfH2Pi G) := by
  intro y
  induction y using groupHomology.H2_induction_on with
  | @h x => exact ⟨x, rfl⟩

/-- `ker Ψ = B₂ = ker (Z₂ → H₂)` (Hopf formula, l.733-735). -/
theorem hopfPsi_ker_eq (hf : Function.Surjective f) : (hopfPsi hf).ker = (hopfH2Pi G).ker := by
  ext x
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  constructor
  · intro h
    have hΦ : hopfChainPhi hf x.1 = 0 := Additive.ext (Subtype.ext
      ((hopfPsi_val hf x).symm.trans
        (congrArg (fun m : Additive ↥(hopfMultiplier f) =>
          ((Additive.toMul m : ↥(hopfMultiplier f)) : HopfExt f)) h)))
    exact (groupHomology.H2π_eq_zero_iff x).mpr ((hopfChain_mem_boundaries₂_iff x.1).mpr
      (hopfChain_mem_range_of_phi_eq_zero hf (hopfChainD_cycles₂ x) hΦ))
  · intro h
    have hb := (hopfChain_mem_boundaries₂_iff x.1).mp ((groupHomology.H2π_eq_zero_iff x).mp h)
    exact Additive.ext (Subtype.ext ((hopfPsi_val hf x).trans
      (congrArg (fun z : Additive (HopfExtK f) => ((Additive.toMul z : HopfExtK f) : HopfExt f))
        (hopfChainPhi_of_mem_range hf hb))))

variable (f) in
/-- Hopf formula (`sec:questions`, l.733-735; Brown II.5 Thm 5.3): for a surjection `f` from a free
group onto `G`, the Hopf multiplier `(R ∩ [F,F]) ⧸ [F,R]` is additively isomorphic to
`H₂(G, ℤ) = groupHomology.H2 (Rep.trivial ℤ G ℤ)`. -/
noncomputable def hopfMultiplierAddEquivH2 (hf : Function.Surjective f) :
    Additive ↥(hopfMultiplier f) ≃+ ↑(groupHomology.H2 (Rep.trivial ℤ G ℤ)) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective (hopfPsi hf) (hopfPsi_surjective hf)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (hopfPsi_ker_eq hf)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective (hopfH2Pi G) hopfH2Pi_surjective))

end H2

end GroupApproximation.Full.LVHopf
