import GroupApproximation.BooneHigman.Metabelian.ElemFPNK2CoreMaps
import GroupApproximation.Meta.AxiomGuard

/-!
# The `NK₂` cone residual, cut down to the slice `s_{n+1} = 1`

Lane `bh-met-90o`.  Lane `bh-met-90g` isolated `czNK2_ConeOverStatement A`: for a cube element
`v ∈ K₂(n + 5, A[s_0..s_n])` (killed by every `π_i`), its cone image
`w = ψ_{n+1}(j(ι v)) ∈ K₂(n + 6, B[t])`, `B = A[s_1..s_{n+1}]`, and **every** maximal `𝔪 ∋ p` of
`B`, some `s ∉ 𝔪` makes `v_s(w)` die after padding.

* `nk2Core_SliceOverStatement A`: the same demand, but only at the maximal ideals `𝔪` on the
  hyperplane `s_{n+1} = 1` (i.e. `X (Fin.last n) - 1 ∈ 𝔪` in `B = A[s_1..s_{n+1}]`, indexed
  from `0`).  **The isolated residual.**
* `nk2Core_pad_dies_of_sliceOver`: the slice residual kills `ι v`.  Let `Q = Q(w)` be the Quillen
  ideal.  If `Q + (s_{n+1} - 1) ≠ B`, a maximal `𝔪` contains it; `𝔪` contains a prime (`hres`)
  and `s_{n+1} - 1`, so the slice residual puts some `s ∈ Q` outside `𝔪`, which is absurd.  So
  `a + c (s_{n+1} - 1) = 1` with `a ∈ Q`.  Apply the slice retraction `ε : s_{n+1} ↦ 1`
  (`nk2Core_sliceRetract`): `ε a = 1`, and by naturality (`nk2Core_K2Map_quillenDiff`) and
  `ε[t] ∘ ψ_{n+1} ∘ j = ψ_n` (`nk2Core_sliceRetract_comp_cone`) the death of `v_a(w)` becomes the
  death of `v_1(ψ_n(ι v))`.  Since `π_0 (ι v) = 1`, the collapse gives the death of `ψ_n(ι v)`,
  hence of `ι v`.
* `nk2Core_coneOver_of_sliceOver`: hence the cone residual, with `s = 1` at every `𝔪`.
* `nk2Core_sliceOver_of_coneOver`: the converse (drop the extra hypothesis).

## LOUD: strength

`nk2Core_SliceOverStatement A` is **logically equivalent** to `czNK2_ConeOverStatement A` (given
`hres`, which holds for `ℤ[1/m]` and `F_p`); both directions are proved.  It is **not** strictly
weaker logically.  It is **strictly smaller in proof content**: the local condition is demanded
only at the maximal ideals of the hyperplane `s_{n+1} = 1`, not at all maximal ideals.  In
particular the ideals with `s_{n+1} ∈ 𝔪` (where the cone `s_0 ↦ s_0 s_{n+1}` degenerates) and all
other ideals off the slice are handled here, by the Krull argument above and the retraction `ε`.
The proof content removed is: Krull (`Ideal.exists_le_maximal`), the retraction `ε`, the
naturality of `v_a` under base change, the identity `ε[t] ∘ ψ_{n+1} ∘ j = ψ_n`, the collapse
`1 ∈ Q ⇒` death, and the passage back through `ψ_n`.

Honest remark: on the slice, `ε` identifies `w` with `ψ_n(ι v)` one variable down, so per instance
the residual is the old minimal-rank local condition at `k = n` base variables, restricted to
`𝔪 ∋ s_{n+1} - 1`.  The cone detour of lane `bh-met-90g` adds no content beyond that.

## Why the target is not closed (and a truth check of what cannot be done)

The cone residual is Quillen's `NK₂ = 0` for the regular rings `ℤ[1/m][s_1..s_k]`,
`F_p[s_1..s_k]` in local unstable form.  No slice of it follows from arguments valid over every
commutative ring `A` (Steinberg homotopies, `y ↦ λ y` endomorphisms, vanishing on the two
hyperplanes `s_0 = 0`, `s_{n+1} = 0`): over `A = F_p[ε]/(ε²)`, `p` odd, van der Kallen's
`K₂(R[ε], ε) ≅ Ω¹_R` gives a cube element whose cone image corresponds to the form
`f(t y) d(t y)`, which survives every localization, so the local condition fails at every
maximal ideal.  Regularity of `A` must enter, which needs Quillen's localization and dévissage.
No hypothesis `Prop` stands for a cited theorem and no literature input is used.

## Truth check

The residual is true: it is implied by (converse proved) `czNK2_ConeOverStatement A`, which is
true over `ℤ[1/m]` and `F_p` by Quillen's `NK₂ = 0` (see module `ElemFPCharZeroNK2Cone`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Over

variable (A : Type*) [CommRing A]

/-- **The slice residual over `A`.**  The cone residual `czNK2_ConeOverStatement A`, demanded only
at the maximal ideals `𝔪 ∋ p` of `B = A[s_1..s_{n+1}]` with `s_{n+1} - 1 ∈ 𝔪`. -/
def nk2Core_SliceOverStatement : Prop :=
  ∀ n N : ℕ, N = n + 5 →
    ∀ v : K2n N (MvPolynomial (Fin (n + 1)) A),
      (∀ i : Fin (n + 1), K2Map (cubeKill A i) v = 1) →
        ∀ p : ℕ, p.Prime →
          ∀ P : Ideal (MvPolynomial (Fin (n + 1)) A), P.IsMaximal →
            (p : MvPolynomial (Fin (n + 1)) A) ∈ P →
              (MvPolynomial.X (Fin.last n) - 1 : MvPolynomial (Fin (n + 1)) A) ∈ P →
                ∃ s : MvPolynomial (Fin (n + 1)) A, s ∉ P ∧
                  K2DiesAfterPadding
                    (quillenDiff
                      (K2Map (MvPolynomial.finSuccEquiv A (n + 1)).toRingEquiv.toRingHom
                        (K2Map (czCubeResFieldCone A n)
                          (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v))) s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_SliceOverStatement

/-- **Death from the slice residual.**  If every maximal ideal of every `A[s_1..s_k]` contains a
prime, the slice residual makes the padded cube element `ι v` die after padding. -/
theorem nk2Core_pad_dies_of_sliceOver
    (hres : ∀ k : ℕ, ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
      ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) A) ∈ P)
    (h : nk2Core_SliceOverStatement A) {n N : ℕ} (hN : N = n + 5)
    (v : K2n N (MvPolynomial (Fin (n + 1)) A))
    (hv : ∀ i : Fin (n + 1), K2Map (cubeKill A i) v = 1) :
    K2DiesAfterPadding (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v) := by
  have htop : quillenIdeal
      (K2Map (MvPolynomial.finSuccEquiv A (n + 1)).toRingEquiv.toRingHom
        (K2Map (czCubeResFieldCone A n)
          (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v))) ⊔
      Ideal.span {(MvPolynomial.X (Fin.last n) - 1 : MvPolynomial (Fin (n + 1)) A)} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hp, hpM⟩ := hres (n + 1) M hM
    obtain ⟨s, hsM, hs⟩ := h n N hN v hv p hp M hM hpM
      (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact hsM (hle (Ideal.mem_sup_left ((mem_quillenIdeal _ s).mpr hs)))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp htop)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have hεa : nk2Core_sliceRetract A n a = 1 := by
    have h1 := congrArg (nk2Core_sliceRetract A n) hab
    rwa [map_add, map_mul, map_sub, map_one, nk2Core_sliceRetract_X_last, sub_self, mul_zero,
      add_zero] at h1
  have hd := diesAfterPadding_K2Map
    (Polynomial.mapRingHom (Polynomial.mapRingHom (nk2Core_sliceRetract A n)))
    ((mem_quillenIdeal _ a).mp ha)
  rw [nk2Core_K2Map_quillenDiff, hεa,
    K2Map_K2Map (MvPolynomial.finSuccEquiv A (n + 1)).toRingEquiv.toRingHom
      (czCubeResFieldCone A n),
    K2Map_K2Map (Polynomial.mapRingHom (nk2Core_sliceRetract A n)),
    nk2Core_sliceRetract_comp_cone] at hd
  have hev : K2Map (Polynomial.evalRingHom 0 :
      Polynomial (MvPolynomial (Fin n) A) →+* MvPolynomial (Fin n) A)
        (K2Map (MvPolynomial.finSuccEquiv A n).toRingEquiv.toRingHom
          (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v)) = 1 := by
    rw [K2Map_K2Map, ← evalZero_finSuccEquiv_comp_cubeKill_zero (R := A) n, ← K2Map_K2Map,
      czNK2_cubeKill_pad A hv 0, map_one]
  have hdu := diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv A n).toRingEquiv.symm.toRingHom
    (diesAfterPadding_of_one_mem_quillenIdeal hev ((mem_quillenIdeal _ 1).mpr hd))
  rwa [K2Map_K2Map_of_comp_eq_id _ _
    (MvPolynomial.finSuccEquiv A n).toRingEquiv.symm_toRingHom_comp_toRingHom] at hdu

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_pad_dies_of_sliceOver

/-- **The reduction over `A`.**  The slice residual gives the cone residual: `ι v` dies, hence so
do `w = ψ_{n+1}(j(ι v))` and `v_1(w)`, and `s = 1 ∉ 𝔪` works at every `𝔪`. -/
theorem nk2Core_coneOver_of_sliceOver
    (hres : ∀ k : ℕ, ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
      ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) A) ∈ P)
    (h : nk2Core_SliceOverStatement A) : czNK2_ConeOverStatement A := by
  intro n N hN v hv _ _ P hP _
  refine ⟨1, (Ideal.ne_top_iff_one _).mp hP.ne_top, ?_⟩
  exact diesAfterPadding_quillenDiff_of_diesAfterPadding
    (diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv A (n + 1)).toRingEquiv.toRingHom
      (diesAfterPadding_K2Map (czCubeResFieldCone A n)
        (nk2Core_pad_dies_of_sliceOver A hres h hN v hv))) 1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_coneOver_of_sliceOver

/-- Conversely, the cone residual gives the slice residual (drop `s_{n+1} - 1 ∈ 𝔪`). -/
theorem nk2Core_sliceOver_of_coneOver (h : czNK2_ConeOverStatement A) :
    nk2Core_SliceOverStatement A :=
  fun n N hN v hv p hp P hP hpP _ ↦ h n N hN v hv p hp P hP hpP

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_sliceOver_of_coneOver

end Over

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
