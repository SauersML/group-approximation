import GroupApproximation.Algebra.PermutationalWreathSimple
import GroupApproximation.Sofic.TorsionSpectralCollapse

/-!
# The Fourier partition of unity and the wreath generator count

Two statements of the multi-mover dossier which the rest of the development
does not need and therefore does not prove, both independent of the concrete
affine family.

`Sofic/TorsionSpectralCollapse` builds the Fourier idempotents
`m⁻¹ • ∑_t ζ^{jt} • v^t` of an element with `v ^ m = 1`, proves each of them
self-adjoint and idempotent, and recovers `v` from them.  Section 36.2 of the
dossier says more: the idempotents form a partition of the identity.  Distinct
ones annihilate each other, because reindexing the double sum by its outer
variable turns the cross character into the character of the difference of the
two indices, and a nontrivial character of a cyclic group sums to zero.  The
same character sum, read in the other variable, collapses their total to the
constant term of the expansion, whose coefficient cancels the normalization.

`Algebra/PermutationalWreathSimple` proves that over a transitive site action
the generators of the acting group together with the generators of a single
lamp copy generate the whole permutational wreath product.  Section 43.3 of the
dossier records the resulting bound on the number of generators, which for an
ascending HNN extension over an `r`-generated base with a `q`-generated lamp is
the displayed `r + 1 + q`.
-/

namespace GroupApproximation
namespace DossierAuditAddenda

open TorsionSpectralCollapse

/-! ## The Fourier idempotents partition the identity -/

section Fourier

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable {M : ℕ} [NeZero M] {ζ : ℂ} {v : A}

/-- Characters multiply in the index as well as in the argument: the exponent
`ZMod.val a * ZMod.val t` is symmetric, so the additivity already available in
the second slot transfers to the first. -/
theorem char_mul_left (hζM : ζ ^ M = 1) (a b t : ZMod M) :
    ζ ^ (ZMod.val a * ZMod.val t) * ζ ^ (ZMod.val b * ZMod.val t)
      = ζ ^ (ZMod.val (a + b) * ZMod.val t) := by
  have h := fourier_char_mul hζM t a b
  rw [Nat.mul_comm (ZMod.val t) (ZMod.val a),
    Nat.mul_comm (ZMod.val t) (ZMod.val b),
    Nat.mul_comm (ZMod.val t) (ZMod.val (a + b))] at h
  exact h

/-- **Section 36.2, orthogonality.**  Fourier idempotents attached to distinct
indices annihilate each other.  After reindexing the inner summation by the
outer variable the cross character becomes the character of the difference of
the two indices, and that character is nontrivial, so it sums to zero. -/
theorem fourierIdem_mul_of_ne (hζM : ζ ^ M = 1)
    (hζne : ∀ i : ℕ, 0 < i → i < M → ζ ^ i ≠ 1) (hvM : v ^ M = 1)
    {j l : ZMod M} (hjl : j ≠ l) :
    fourierIdem ζ M v j * fourierIdem ζ M v l = 0 := by
  classical
  have hshift : ∀ t : ZMod M,
      ζ ^ (ZMod.val (j - l) * ZMod.val t) * ζ ^ (ZMod.val l * ZMod.val t)
        = ζ ^ (ZMod.val j * ZMod.val t) := by
    intro t
    have hsum : j - l + l = j := by ring
    rw [char_mul_left hζM (j - l) l t, hsum]
  have hterm : ∀ t u : ZMod M,
      (ζ ^ (ZMod.val j * ZMod.val t) • v ^ ZMod.val t) *
          (ζ ^ (ZMod.val l * ZMod.val u) • v ^ ZMod.val u)
        = (ζ ^ (ZMod.val j * ZMod.val t) * ζ ^ (ZMod.val l * ZMod.val u)) •
            v ^ ZMod.val (t + u) := by
    intro t u
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, fourier_pow_mul hvM]
  have hinner : ∀ t : ZMod M,
      (∑ u : ZMod M,
        (ζ ^ (ZMod.val j * ZMod.val t) * ζ ^ (ZMod.val l * ZMod.val u)) •
          v ^ ZMod.val (t + u))
        = ζ ^ (ZMod.val (j - l) * ZMod.val t) •
            ∑ w : ZMod M, ζ ^ (ZMod.val l * ZMod.val w) • v ^ ZMod.val w := by
    intro t
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft t) _ _ fun u ↦ ?_
    rw [Equiv.coe_addLeft, smul_smul, ← fourier_char_mul hζM l t u,
      ← mul_assoc (ζ ^ (ZMod.val (j - l) * ZMod.val t)), hshift t]
  have hchar : (∑ t : ZMod M, ζ ^ (ZMod.val (j - l) * ZMod.val t)) = 0 := by
    have h := char_sum M hζM hζne (j - l)
    rw [if_neg (sub_ne_zero_of_ne hjl)] at h
    calc (∑ t : ZMod M, ζ ^ (ZMod.val (j - l) * ZMod.val t))
        = ∑ t : ZMod M, ζ ^ (ZMod.val t * ZMod.val (j - l)) :=
          Finset.sum_congr rfl fun t _ ↦ by rw [Nat.mul_comm]
      _ = 0 := h
  unfold fourierIdem
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun u _ ↦ hterm t u]
  rw [Finset.sum_congr rfl fun t _ ↦ hinner t, ← Finset.sum_smul, hchar,
    zero_smul, smul_zero]

/-- **Section 36.2, completeness.**  The Fourier idempotents of a finite-order
element sum to the identity: summing over the index leaves only the constant
term of the expansion, and its coefficient cancels the normalization. -/
theorem sum_fourierIdem (hζM : ζ ^ M = 1)
    (hζne : ∀ i : ℕ, 0 < i → i < M → ζ ^ i ≠ 1) :
    (∑ j : ZMod M, fourierIdem ζ M v j) = 1 := by
  classical
  have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  unfold fourierIdem
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hinner : ∀ t : ZMod M,
      (∑ j : ZMod M, ζ ^ (ZMod.val j * ZMod.val t) • v ^ ZMod.val t)
        = (if t = 0 then (M : ℂ) else 0) • v ^ ZMod.val t := by
    intro t
    rw [← Finset.sum_smul, char_sum M hζM hζne t]
  rw [Finset.sum_congr rfl fun t _ ↦ hinner t,
    Finset.sum_eq_single (0 : ZMod M)]
  · rw [if_pos rfl, ZMod.val_zero, pow_zero, smul_smul, inv_mul_cancel₀ hM0,
      one_smul]
  · intro t _ ht
    rw [if_neg ht, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Fourier

/-! ## The generator count of a permutational wreath product -/

universe u v w

/-- **Section 43.3.**  Over a transitive site action a generating set of the
acting group together with a generating set of one lamp copy assembles into a
generating set of the permutational wreath product whose size is the sum of the
two given sizes.  For the ascending HNN extension of an `r`-generated base the
acting group is generated by `r + 1` elements, which turns this bound into the
`r + 1 + q` of the dossier. -/
theorem exists_generating_finset_card_le {K : Type u} [Group K] {G : Type w}
    [Group G] {X : Type v} [MulAction G X] [DecidableEq X] (x₀ : X)
    (htrans : ∀ x : X, ∃ g : G, g • x₀ = x)
    (SG : Finset G) (hSG : Subgroup.closure (SG : Set G) = ⊤)
    (SK : Finset K) (hSK : Subgroup.closure (SK : Set K) = ⊤) :
    ∃ T : Finset (Wreath K G X), T.card ≤ SG.card + SK.card ∧
      Subgroup.closure (T : Set (Wreath K G X)) = ⊤ := by
  classical
  refine ⟨SG.image (SemidirectProduct.inr : G →* Wreath K G X) ∪
    SK.image (fun k ↦ (SemidirectProduct.inl (Lamp.single x₀ k) :
      Wreath K G X)), ?_, ?_⟩
  · exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  · rw [Finset.coe_union, Finset.coe_image, Finset.coe_image]
    exact wreath_eq_closure x₀ htrans hSG hSK

end DossierAuditAddenda
end GroupApproximation
