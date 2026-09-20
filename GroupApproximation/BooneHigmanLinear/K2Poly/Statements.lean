import GroupApproximation.BooneHigmanLinear.PolyFpK2Core
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2RingEquiv
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyFieldConst
import Mathlib.RingTheory.Localization.AtPrime.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The K₂ program for T2/T3: statements and wiring (lane bh-pal-wire)

The dependency tree, its owners and the sources are in the swarm board `k2-poly.md`. The primary
route is now unstable 𝔸¹-invariance, Lavrenov–Sinchuk–Voronetsky arXiv:2110.11087 (section `LSV`:
`UnstableNKPolyFpStatement` gives `TulenbaevPolyFpK2Statement` and `P1` directly). The char-`p`
input `P1` of route A is `ONEVAR ∧ DIAG`:

* ONEVAR is `ElemFP.PolyK2OneVarNilStatementOver (ZMod p)`, stable `NK₂(F_p[s₁..s_k]) = 0`;
* DIAG is `ElemFP.PolyK2StabRangeDiagStatementOver (ZMod p) 4`.

This module does three things.

* **DIAG from Tulenbaev's injective stability.** `stabRangeDiag_of_injStab` derives DIAG from
  `TulenbaevInjStabFpStatement` (Tulenbaev, Math. USSR Sb. 45 (1983), Thm 5.3(a), elementary).
  `gapOver_of_oneVar_of_injStab` and `polyFpK2VanishingGeTwo_of_oneVar_of_injStab` then reduce
  `P1`, and the owed input `hV`, to ONEVAR together with that stability statement.
* **The local case.** It states the case over one ring `B`, generically, so that no
  `Localization` instance diamond arises at the call site:
  - `LocalNKAt B r`: stable `NK₂` vanishing at rank `r` over `B`;
  - `HorrocksMonicAt A r`: Tulenbaev's Cor 5.2(a). An element of `St_r(A[X])` that dies in every
    ring where a monic `f` becomes a unit is trivial;
  - `MonicKillAt B r`: a `NK₂` element dies after inverting some monic polynomial. This is the
    deep core, where Quillen's homotopy invariance lives.
* **One wiring step for the local case.** `localNKAt_of_horrocks_of_monicKill` shows that
  `LocalNKAt` follows from the Horrocks and monic-kill statements.
  - `LocalNKFpStatement` is the local case at the maximal localizations of `F_p[s₁..s_k]`.

The monic-kill and Horrocks statements quantify over every ring `S` in which `f` becomes a unit,
instead of naming `A[X]_f`. By the universal property of localization this is equivalent. It
also keeps `Localization.Away f` out of the statements, whose semiring instance paths do not unify
under instance search.
-/

namespace GroupApproximation
namespace BooneHigmanLinear

open GroupApproximation.BooneHigman

section Stability

/-- One stabilization killing `u` means `u` dies after padding. -/
theorem k2DiesAfterPadding_of_K2Stab {R : Type*} [Ring R] {N : ℕ}
    {u : SteinbergBasic.K2n N R} (h : SteinbergBasic.K2Stab N R u = 1) :
    Metabelian.ElemFP.K2DiesAfterPadding u := by
  refine ⟨N + 1, Nat.le_succ N, ?_⟩
  have hemb : (Fin.castLEEmb (Nat.le_succ N) : Fin N ↪ Fin (N + 1)) = Fin.castSuccEmb :=
    Function.Embedding.ext fun _ => Fin.ext rfl
  rw [hemb]
  exact h

#audit_axioms GroupApproximation.BooneHigmanLinear.k2DiesAfterPadding_of_K2Stab

/-- **DIAG from Tulenbaev's injective stability.** -/
theorem stabRangeDiag_of_injStab (h : TulenbaevInjStabFpStatement) (p : ℕ) (hp : p.Prime) :
    Metabelian.ElemFP.PolyK2StabRangeDiagStatementOver (ZMod p) 4 := by
  intro k _ u _ hstab
  exact h p hp k (k + 4) (by omega) u (k2DiesAfterPadding_of_K2Stab hstab)

#audit_axioms GroupApproximation.BooneHigmanLinear.stabRangeDiag_of_injStab

/-- **`P1` from ONEVAR and Tulenbaev's injective stability.** -/
theorem gapOver_of_oneVar_of_injStab
    (hone : ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2OneVarNilStatementOver (ZMod p))
    (hinj : TulenbaevInjStabFpStatement) :
    ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4 :=
  fun p hp => ⟨hone p hp, stabRangeDiag_of_injStab hinj p hp⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.gapOver_of_oneVar_of_injStab

/-- The owed char-`p` input `hV` from ONEVAR and Tulenbaev's injective stability. -/
theorem polyFpK2VanishingGeTwo_of_oneVar_of_injStab
    (hone : ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2OneVarNilStatementOver (ZMod p))
    (hinj : TulenbaevInjStabFpStatement) : PolyFpK2VanishingGeTwoStatement :=
  polyFpK2VanishingGeTwo_of_gapOver (gapOver_of_oneVar_of_injStab hone hinj)

#audit_axioms GroupApproximation.BooneHigmanLinear.polyFpK2VanishingGeTwo_of_oneVar_of_injStab

end Stability

section Local

/-- **Stable `NK₂` vanishing over `B` at rank `r`**: an element of `K₂(r, B[X])` killed by
`X ↦ 0` dies after padding. -/
def LocalNKAt (B : Type) [CommRing B] (r : ℕ) : Prop :=
  ∀ u : SteinbergBasic.K2 (Fin r) (Polynomial B),
    SteinbergBasic.K2Map (Polynomial.evalRingHom 0 : Polynomial B →+* B) u = 1 →
      Metabelian.ElemFP.K2DiesAfterPadding u

#audit_axioms GroupApproximation.BooneHigmanLinear.LocalNKAt

/-- **Horrocks for `St_r`, monic form** (Tulenbaev Cor 5.2(a); board piece H.b, owner pal-q111).
If `f ∈ A[X]` is monic and `α ∈ St_r(A[X])` becomes trivial in every commutative ring where `f`
becomes a unit, then `α = 1`. -/
def HorrocksMonicAt (A : Type) [CommRing A] (r : ℕ) : Prop :=
  ∀ f : Polynomial A, f.Monic → ∀ α : SteinbergBasic.St r (Polynomial A),
    (∀ (S : Type) [CommRing S] (φ : Polynomial A →+* S), IsUnit (φ f) →
      SteinbergGroup.ringMap φ α = 1) → α = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.HorrocksMonicAt

/-- **Monic kill** (board piece MK, the deep core, owner bh-pal-wire).  Every element of
`K₂(r, B[X])` killed by `X ↦ 0` becomes trivial, after padding to some rank `M`, in every
commutative ring where some monic `f` becomes a unit. -/
def MonicKillAt (B : Type) [CommRing B] (r : ℕ) : Prop :=
  ∀ u : SteinbergBasic.K2 (Fin r) (Polynomial B),
    SteinbergBasic.K2Map (Polynomial.evalRingHom 0 : Polynomial B →+* B) u = 1 →
      ∃ f : Polynomial B, f.Monic ∧ ∃ M : ℕ, ∃ hrM : r ≤ M,
        ∀ (S : Type) [CommRing S] (φ : Polynomial B →+* S), IsUnit (φ f) →
          SteinbergGroup.ringMap φ
            (SteinbergGroup.indexMap (Fin.castLEEmb hrM)
              (u : SteinbergBasic.St r (Polynomial B))) = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.MonicKillAt

/-- **LOCAL from Horrocks and monic kill.** -/
theorem localNKAt_of_horrocks_of_monicKill {B : Type} [CommRing B] {r : ℕ}
    (hH : ∀ M : ℕ, HorrocksMonicAt B M) (hMK : MonicKillAt B r) : LocalNKAt B r := by
  intro u hu
  obtain ⟨f, hf, M, hrM, hkill⟩ := hMK u hu
  exact ⟨M, hrM, Subtype.ext (hH M f hf _ hkill)⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.localNKAt_of_horrocks_of_monicKill

/-- **The local case of ONEVAR** (board piece LOCAL): stable `NK₂` vanishes at every rank
`r ≥ 5` over the localization of `F_p[s₁..s_k]` at any maximal ideal. -/
def LocalNKFpStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, ∀ (𝔪 : Ideal (MvPolynomial (Fin k) (ZMod p))) [𝔪.IsMaximal],
    ∀ r : ℕ, 5 ≤ r → LocalNKAt (Localization.AtPrime 𝔪) r

#audit_axioms GroupApproximation.BooneHigmanLinear.LocalNKFpStatement

end Local


section LSV

/-- **Unstable `NK₂` vanishing over `B` at rank `r`** (the conclusion of Lavrenov–Sinchuk–
Voronetsky, arXiv:2110.11087, Thm 1.1, for `K₂(A_{r-1}, B)`): an element of `K₂(r, B[X])` killed
by `X ↦ 0` is trivial. -/
def UnstableNKAt (B : Type) [CommRing B] (r : ℕ) : Prop :=
  ∀ u : SteinbergBasic.K2 (Fin r) (Polynomial B),
    SteinbergBasic.K2Map (Polynomial.evalRingHom 0 : Polynomial B →+* B) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.UnstableNKAt

/-- Unstable vanishing implies stable vanishing. -/
theorem localNKAt_of_unstableNKAt {B : Type} [CommRing B] {r : ℕ} (h : UnstableNKAt B r) :
    LocalNKAt B r := fun u hu => ⟨r, le_rfl, by
  rw [h u hu, map_one]⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.localNKAt_of_unstableNKAt

/-- **The LSV target over `F_p`**: unstable `𝔸¹`-invariance of `K₂(r, -)` for `r ≥ 5` on every
polynomial ring `F_p[s₁..s_k]`, which is smooth over `F_p`. -/
def UnstableNKPolyFpStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k r : ℕ, 5 ≤ r → UnstableNKAt (MvPolynomial (Fin k) (ZMod p)) r

#audit_axioms GroupApproximation.BooneHigmanLinear.UnstableNKPolyFpStatement

/-- **Unstable `𝔸¹`-invariance gives `K₂(r, F_p[s₁..s_k]) = ⊥` for `r ≥ 5`**, by induction on `k`
through `MvPolynomial.finSuccEquiv`, starting from `K₂(r, F_p) = ⊥`. -/
theorem tulenbaevPolyFpK2_of_unstableNK (h : UnstableNKPolyFpStatement) :
    TulenbaevPolyFpK2Statement := by
  intro p hp k N hN
  induction k with
  | zero =>
    exact Metabelian.ElemFP.bhNagaoWire_K2_bot_of_ringEquiv
      (MvPolynomial.isEmptyRingEquiv (ZMod p) (Fin 0))
      (Metabelian.ElemFP.vdkRowExt_fieldK2Vanishing p hp N hN)
  | succ k ih =>
    refine Metabelian.ElemFP.bhNagaoWire_K2_bot_of_ringEquiv
      (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv ?_
    refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
    have h0 : SteinbergBasic.K2Map
        (Polynomial.evalRingHom 0 :
          Polynomial (MvPolynomial (Fin k) (ZMod p)) →+* MvPolynomial (Fin k) (ZMod p))
        (⟨g, hg⟩ : SteinbergBasic.K2 (Fin N) (Polynomial (MvPolynomial (Fin k) (ZMod p)))) = 1 :=
      Metabelian.ElemFP.eq_one_of_K2_eq_bot ih _
    exact congrArg Subtype.val (h p hp k N hN _ h0)

#audit_axioms GroupApproximation.BooneHigmanLinear.tulenbaevPolyFpK2_of_unstableNK

/-- **`P1` from the LSV target.** -/
theorem gapOver_of_unstableNK (h : UnstableNKPolyFpStatement) :
    ∀ p : ℕ, p.Prime → Metabelian.ElemFP.PolyK2NilGapStatementOver (ZMod p) 4 :=
  gapOver_of_oneVar_of_injStab
    (fun p hp k N hN u hu => localNKAt_of_unstableNKAt (h p hp k N (by omega)) u hu)
    (fun p hp k N hN u _ => Metabelian.ElemFP.eq_one_of_K2_eq_bot
      (tulenbaevPolyFpK2_of_unstableNK h p hp k N hN) u)

#audit_axioms GroupApproximation.BooneHigmanLinear.gapOver_of_unstableNK

/-- **(A5) from the field constant statement.**  If every element of `K₂(r, F[X])` is the image
of some element of `St(r, F)` under `C` (`ElemFP.k2PolyField_ConstStatement`, lane bh-met-90u;
Rehmann/Nagao for a field `F`), then unstable `NK₂(r, F) = 1`. -/
theorem unstableNKAt_of_fieldConst {F : Type} [CommRing F] {r : ℕ}
    (h : Metabelian.ElemFP.k2PolyField_ConstStatement F r) : UnstableNKAt F r := by
  intro u hu
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (h (u : SteinbergBasic.St r (Polynomial F)) u.2)
  have hev : SteinbergGroup.ringMap (Polynomial.evalRingHom 0 : Polynomial F →+* F)
      (u : SteinbergBasic.St r (Polynomial F)) = 1 := congrArg Subtype.val hu
  have hy1 : y = 1 := by
    rw [← hy, SteinbergBasic.ringMap_ringMap, Metabelian.ElemFP.evalRingHom_zero_comp_C,
      SteinbergBasic.ringMap_id] at hev
    exact hev
  apply Subtype.ext
  show (u : SteinbergBasic.St r (Polynomial F)) = 1
  rw [← hy, hy1, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.unstableNKAt_of_fieldConst

/-- **(A5) for all fields**, the named target of board piece A5 (owner bh-pal-wire). -/
def FieldNKStatement : Prop :=
  ∀ (F : Type) [Field F] (r : ℕ), 5 ≤ r → Metabelian.ElemFP.k2PolyField_ConstStatement F r

#audit_axioms GroupApproximation.BooneHigmanLinear.FieldNKStatement

end LSV

end BooneHigmanLinear
end GroupApproximation
