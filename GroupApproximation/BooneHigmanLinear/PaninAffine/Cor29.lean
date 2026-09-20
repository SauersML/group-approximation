import GroupApproximation.BooneHigmanLinear.PaninAffine.Geometry
import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Statements
import GroupApproximation.Meta.AxiomGuard
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# LSV Corollary 2.9 for polynomial rings over a field (lane k2-panin)

Lavrenov–Sinchuk–Voronetsky (arXiv:2110.11087), Cor 2.9 with `m = 1`, for `R = K[s₀..sₙ]` and a
maximal ideal `M`. Put `B = R_M` and `E = Frac R`. An element `α ∈ St_r(B[X])` that dies in
`St_r(E[X])` is trivial. This is the input `hCor29` of `K2Poly.LSVForm.unstableNKPoly_of_LSV`, in
the form `K2Poly.NKFieldInjAt B r` with `ι = fracMap M`. That wrapper is `PaninAffine.Cor29Wire`,
so this module does not import `LSVForm`.

**The argument** (artifact `gq-k2-panin-affine-presentation.md`, §4). Panin's theorem, LSV
Lemma 2.6 in its Nisnevich form, étale neighborhoods and Popescu are all replaced by
`AffineMonicFibreStatement`.
1. *Finitary* (`Cor29FinitaryAt`, from T Lemma 2.2 = F.5). `α` comes from `α₁ ∈ St_r(R_g[X])` with
   `g ∉ M`, and `α₁` dies once some `h ≠ 0` is inverted. If `h ∉ M`, then `α = 1` at once.
2. *Coprime part* (`exists_isRelPrime_factor`). Write `h = f₀ q` with `q ∣ g^N` and
   `IsRelPrime f₀ g`, so that `f₀ ∈ M`. Inverting `f₀ g` inverts `h`.
3. *Geometry* (`AffineMonicFibreStatement`). After a shear `φ`, `c f₀` is monic in `s₀` over
   `C = K[s₁..sₙ]`. It is coprime to `g` on the fibre over `𝔭 = ker (C → R/M)`.
4. *Nakayama* (`isCoprime_of_isCoprime_map`, via the resultant). `c f₀` and `g` are coprime in
   `C_𝔭[s₀]`.
5. *Zariski excision* (`StZariskiExcisionAt`, T Prop 1.4(b) = F.4) in `C_𝔭[X][s₀]` glues `1` on the
   `f₀`-chart with `α₁` on the `g`-chart.
6. *Monic injectivity* (`TulenbaevHorrocks.StMonicInjAt` over `C_𝔭[X]`, T Cor 5.2(a)) kills the
   glued element. Its image `α` in `St_r(B[X])` is therefore trivial.

The residue fields of `C_𝔭[X]` are infinite when `K` is. So step 6 needs the non-FR form of H.b.

Inputs are named Props. Not root-wired.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open GroupApproximation.BooneHigman GroupApproximation.SteinbergGroup

section Nakayama

/-- **Nakayama for a monic polynomial.** Let `ψ : A → L` be a ring map to a nontrivial ring such
that every element with nonzero image is a unit, e.g. the residue map of a local ring. If `p` is
monic and `p, q` become coprime over `L`, then they are coprime over `A`. The proof goes through
the resultant. -/
theorem isCoprime_of_isCoprime_map {A L : Type*} [CommRing A] [CommRing L] [Nontrivial L]
    (ψ : A →+* L) (hψ : ∀ a, ψ a ≠ 0 → IsUnit a) {p q : Polynomial A} (hp : p.Monic)
    (h : IsCoprime (p.map ψ) (q.map ψ)) : IsCoprime p q := by
  rw [← Polynomial.isUnit_resultant_iff_isCoprime hp]
  apply hψ
  have hP : (p.map ψ).Monic := hp.map ψ
  have hdeg : (p.map ψ).natDegree = p.natDegree := hp.natDegree_map ψ
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Polynomial.natDegree_map_le (f := ψ) (p := q))
  have hres : ψ (Polynomial.resultant p q) = Polynomial.resultant (p.map ψ) (q.map ψ) := by
    rw [← Polynomial.resultant_map_map, hk,
      Polynomial.resultant_add_right_deg (p.map ψ) (q.map ψ) p.natDegree _ k le_rfl, ← hdeg,
      hP.coeff_natDegree, one_pow, one_mul]
  rw [hres]
  exact ((Polynomial.isUnit_resultant_iff_isCoprime hP).2 h).ne_zero

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.isCoprime_of_isCoprime_map

end Nakayama

section Factor

/-- **The part of `h` coprime to `g`.** In a UFD, a nonzero `h` is `f₀ * q` with `f₀` coprime to
`g` and `q ∣ g ^ N`. -/
theorem exists_isRelPrime_factor {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (g : R) {h : R} (hh : h ≠ 0) :
    ∃ f₀ q : R, h = f₀ * q ∧ IsRelPrime f₀ g ∧ ∃ N : ℕ, q ∣ g ^ N := by
  revert hh
  induction h using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h0 => absurd rfl h0
  | h₂ x hx => exact fun _ => ⟨x, 1, (mul_one x).symm, hx.isRelPrime_left, 0, one_dvd _⟩
  | h₃ a p ha hp ih =>
    intro _
    obtain ⟨f₀, q, rfl, hrel, N, hq⟩ := ih ha
    by_cases hpg : p ∣ g
    · exact ⟨f₀, p * q, by ring, hrel, N + 1, by rw [pow_succ']; exact mul_dvd_mul hpg hq⟩
    · exact ⟨p * f₀, q, by ring, ((hp.irreducible.isRelPrime_iff_not_dvd).mpr hpg).mul_left hrel,
        N, hq⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.exists_isRelPrime_factor

/-- In `K[∅] = K` a nonzero element lies in no proper ideal. -/
theorem notMem_of_ne_zero_fin_zero {K : Type} [Field K] {M : Ideal (MvPolynomial (Fin 0) K)}
    (hM : M ≠ ⊤) {p : MvPolynomial (Fin 0) K} (hp : p ≠ 0) : p ∉ M := by
  intro hpM
  have hc : p.coeff 0 ≠ 0 := fun h0 =>
    hp (by rw [MvPolynomial.eq_C_of_isEmpty p, h0, map_zero])
  have hu : IsUnit p := by
    rw [MvPolynomial.eq_C_of_isEmpty p]
    exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  exact hM (Ideal.eq_top_of_isUnit_mem (I := M) hpM hu)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.notMem_of_ne_zero_fin_zero

end Factor

section Props

/-- The canonical map `R_P → Frac R`. -/
noncomputable def fracMap {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) [P.IsPrime] :
    Localization.AtPrime P →+* FractionRing R :=
  IsLocalization.lift (M := P.primeCompl) (g := algebraMap R (FractionRing R)) fun s =>
    IsUnit.mk0 _ (((IsFractionRing.injective R (FractionRing R)).ne_iff' (map_zero _)).mpr
      fun h0 => (show (s : R) ∉ P from s.2) (by rw [h0]; exact P.zero_mem))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.fracMap

/-- The canonical map `R_s → R_P` for `s ∉ P`. -/
noncomputable def awayToAtPrime {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] {s : R}
    (hs : s ∉ P) : Localization.Away s →+* Localization.AtPrime P :=
  IsLocalization.Away.lift s
    (IsLocalization.map_units (Localization.AtPrime P) (⟨s, hs⟩ : P.primeCompl))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.awayToAtPrime

/-- **Zariski excision for `St_N` at one ring** (F.4: Tulenbaev, Prop 1.4(b), for the trivial
element on `A_a`; LSV Lemma 2.6 in Zariski form). Let `a, b ∈ A` be comaximal non-zero-divisors.
Suppose an element of `St_N(A_b)` dies in `St_N(A_{ab})`. Then it comes from an element of
`St_N(A)` that dies in `St_N(A_a)`. Owner: bh-pal-linear-char0 (F.4). -/
def StZariskiExcisionAt (A : Type) [CommRing A] (N : ℕ) : Prop :=
  ∀ a b : A, a ∈ nonZeroDivisors A → b ∈ nonZeroDivisors A → IsCoprime a b →
    ∀ β : SteinbergGroup (Fin N) (Localization.Away b),
      ringMap (IsLocalization.Away.awayToAwayLeft b a :
          Localization.Away b →+* Localization.Away (a * b)) β = 1 →
        ∃ γ : SteinbergGroup (Fin N) A,
          ringMap (algebraMap A (Localization.Away a)) γ = 1 ∧
            ringMap (algebraMap A (Localization.Away b)) γ = β

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.StZariskiExcisionAt

/-- **The finitary step of Cor 2.9** (F.5: Tulenbaev, Lemma 2.2, for `R_P[X] = colim R_g[X]` and
`Frac(R)[X] = colim (R_g)_h[X]`). Let `α ∈ St_N(R_P[X])` die in `St_N(Frac(R)[X])`. Then `α` comes
from some `α₁ ∈ St_N(R_g[X])` with `g ∉ P`, and `α₁` dies once some `h ≠ 0` is inverted. -/
def Cor29FinitaryAt (R : Type) [CommRing R] [IsDomain R] (P : Ideal R) [P.IsPrime] (N : ℕ) :
    Prop :=
  ∀ α : SteinbergGroup (Fin N) (Polynomial (Localization.AtPrime P)),
    ringMap (Polynomial.mapRingHom (fracMap P)) α = 1 →
      ∃ (g : R) (hg : g ∉ P) (h : R), h ≠ 0 ∧
        ∃ α₁ : SteinbergGroup (Fin N) (Polynomial (Localization.Away g)),
          ringMap (S := Polynomial (Localization.AtPrime P))
            (Polynomial.mapRingHom (awayToAtPrime P hg)) α₁ = α ∧
            ringMap (S := Polynomial (Localization.Away (algebraMap R (Localization.Away g) h)))
              (Polynomial.mapRingHom (algebraMap (Localization.Away g)
                (Localization.Away (algebraMap R (Localization.Away g) h)))) α₁ = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29FinitaryAt

end Props

section Death

/-- **Death after inverting `s` is universal.** Let `α ∈ St_N(S[X])` die in `St_N(S_s[X])`. Then
`α` dies along every ring map `S[X] → T` that makes `s` a unit. -/
theorem ringMap_eq_one_of_isUnit {S T : Type} [CommRing S] [CommRing T] {N : ℕ} {s : S}
    {α : SteinbergGroup (Fin N) (Polynomial S)}
    (hα : ringMap (Polynomial.mapRingHom (algebraMap S (Localization.Away s))) α = 1)
    (ρ : Polynomial S →+* T) (hρ : IsUnit (ρ (Polynomial.C s))) : ringMap ρ α = 1 := by
  have hfac : (Polynomial.eval₂RingHom
      (IsLocalization.Away.lift s (g := ρ.comp Polynomial.C) hρ : Localization.Away s →+* T)
      (ρ Polynomial.X)).comp (Polynomial.mapRingHom (algebraMap S (Localization.Away s))) = ρ := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, IsLocalization.Away.lift_eq,
        RingHom.comp_apply]
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [← hfac, ← SteinbergBasic.ringMap_ringMap, hα, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.ringMap_eq_one_of_isUnit

/-- **Excision, then monic injectivity.** In `A'[s₀]`, let `a` be monic and `b ≠ 0` with
`(a, b) = 1`. Then an element of `St_N(A'[s₀]_b)` that dies in `St_N(A'[s₀]_{ab})` is trivial. -/
theorem eq_one_of_excision {A' : Type} [CommRing A'] [IsDomain A'] {N : ℕ}
    (hExc : StZariskiExcisionAt (Polynomial A') N)
    (hMon : TulenbaevHorrocks.StMonicInjAt A' N)
    {a b : Polynomial A'} (ha : a.Monic) (hb : b ≠ 0) (hab : IsCoprime a b)
    (β : SteinbergGroup (Fin N) (Localization.Away b))
    (hβ : ringMap (IsLocalization.Away.awayToAwayLeft b a :
        Localization.Away b →+* Localization.Away (a * b)) β = 1) :
    β = 1 := by
  obtain ⟨γ, hγa, hγb⟩ := hExc a b (mem_nonZeroDivisors_of_ne_zero ha.ne_zero)
    (mem_nonZeroDivisors_of_ne_zero hb) hab β hβ
  rw [← hγb, hMon a ha γ hγa, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.eq_one_of_excision

end Death

section Coordinates

variable {K : Type} [Field K] {n : ℕ} (M : Ideal (MvPolynomial (Fin (n + 1)) K)) [M.IsMaximal]
  (φ : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K)

theorem finSuccEquiv_C_C (c : K) :
    MvPolynomial.finSuccEquiv K n (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.finSuccEquiv_C_C

/-- `𝔭 = ker (C → R/M)`: the prime of `C = K[s₁..sₙ]` below `M` in the coordinates `φ`. -/
noncomputable abbrev fibrePrime : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (fibreMap M φ)

instance fibrePrime_isPrime : (fibrePrime M φ).IsPrime := RingHom.ker_isPrime _

/-- The residue map `C_𝔭 → R/M`. -/
noncomputable def resMap :
    Localization.AtPrime (fibrePrime M φ) →+* MvPolynomial (Fin (n + 1)) K ⧸ M :=
  letI := Ideal.Quotient.field M
  IsLocalization.lift (M := (fibrePrime M φ).primeCompl) (g := fibreMap M φ) fun s =>
    IsUnit.mk0 _ fun h =>
      (show (s : MvPolynomial (Fin n) K) ∉ fibrePrime M φ from s.2) (RingHom.mem_ker.mpr h)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.resMap

theorem resMap_algebraMap (c : MvPolynomial (Fin n) K) :
    resMap M φ (algebraMap _ (Localization.AtPrime (fibrePrime M φ)) c) = fibreMap M φ c :=
  IsLocalization.lift_eq _ _

theorem resMap_comp :
    (resMap M φ).comp (algebraMap _ (Localization.AtPrime (fibrePrime M φ))) = fibreMap M φ :=
  IsLocalization.lift_comp _

/-- `C_𝔭` is local with residue field inside `R/M`: nonzero residue means unit. -/
theorem isUnit_of_resMap_ne_zero (x : Localization.AtPrime (fibrePrime M φ))
    (hx : resMap M φ x ≠ 0) : IsUnit x := by
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj (fibrePrime M φ).primeCompl x
  change x * algebraMap _ _ (s : MvPolynomial (Fin n) K) = algebraMap _ _ c at hcs
  have hc : c ∉ fibrePrime M φ := by
    intro hc0
    have h := congrArg (resMap M φ) hcs
    rw [map_mul, resMap_algebraMap, resMap_algebraMap, RingHom.mem_ker.mp hc0] at h
    exact hx ((mul_eq_zero.mp h).resolve_right fun h0 =>
      (show (s : MvPolynomial (Fin n) K) ∉ fibrePrime M φ from s.2) (RingHom.mem_ker.mpr h0))
  have hu : IsUnit (x * algebraMap _ (Localization.AtPrime (fibrePrime M φ))
      (s : MvPolynomial (Fin n) K)) := by
    rw [hcs]
    exact IsLocalization.map_units _ (⟨c, hc⟩ : (fibrePrime M φ).primeCompl)
  exact isUnit_of_mul_isUnit_left hu

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.isUnit_of_resMap_ne_zero

/-- `C → R`, `c ↦ φ⁻¹ (c(s₁..sₙ))`. So `fibreMap M φ = mk M ∘ baseMap φ`. -/
noncomputable def baseMap : MvPolynomial (Fin n) K →+* MvPolynomial (Fin (n + 1)) K :=
  (φ.symm : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K).toRingHom.comp
    (MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1))).toRingHom

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.baseMap

/-- `C_𝔭 → B = R_M`. -/
noncomputable def toB : Localization.AtPrime (fibrePrime M φ) →+* Localization.AtPrime M :=
  IsLocalization.lift (M := (fibrePrime M φ).primeCompl)
    (g := (algebraMap _ (Localization.AtPrime M)).comp (baseMap φ)) fun s =>
      IsLocalization.map_units (Localization.AtPrime M)
        (⟨baseMap φ s, fun h => (show (s : MvPolynomial (Fin n) K) ∉ fibrePrime M φ from s.2)
          (RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr h))⟩ : M.primeCompl)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.toB

theorem toB_algebraMap (c : MvPolynomial (Fin n) K) :
    toB M φ (algebraMap _ (Localization.AtPrime (fibrePrime M φ)) c) =
      algebraMap _ (Localization.AtPrime M) (baseMap φ c) :=
  IsLocalization.lift_eq _ _

/-- The coordinates `R → C_𝔭[s₀]`, `p ↦ φ p` read as a polynomial in `s₀`. -/
noncomputable def coord :
    MvPolynomial (Fin (n + 1)) K →+* Polynomial (Localization.AtPrime (fibrePrime M φ)) :=
  (Polynomial.mapRingHom
      (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime (fibrePrime M φ)))).comp
    ((MvPolynomial.finSuccEquiv K n).toAlgHom.comp
      (φ : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K)).toRingHom

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.coord

theorem coord_apply (p : MvPolynomial (Fin (n + 1)) K) :
    coord M φ p = (MvPolynomial.finSuccEquiv K n (φ p)).map
      (algebraMap _ (Localization.AtPrime (fibrePrime M φ))) := rfl

theorem coord_injective : Function.Injective (coord M φ) := by
  intro p q h
  rw [coord_apply, coord_apply] at h
  exact φ.injective ((MvPolynomial.finSuccEquiv K n).injective
    (Polynomial.map_injective _ (IsLocalization.injective
      (S := Localization.AtPrime (fibrePrime M φ)) (M := (fibrePrime M φ).primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors _)) h))

theorem map_coord_resMap (p : MvPolynomial (Fin (n + 1)) K) :
    (coord M φ p).map (resMap M φ) =
      (MvPolynomial.finSuccEquiv K n (φ p)).map (fibreMap M φ) := by
  rw [coord_apply, Polynomial.map_map, resMap_comp]

/-- `C_𝔭[s₀] → B`, `s₀ ↦ φ⁻¹ s₀`. -/
noncomputable def polyToB :
    Polynomial (Localization.AtPrime (fibrePrime M φ)) →+* Localization.AtPrime M :=
  Polynomial.eval₂RingHom (toB M φ) (algebraMap _ _ (φ.symm (MvPolynomial.X 0)))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.polyToB

theorem polyToB_X (i : Fin (n + 1)) :
    polyToB M φ ((MvPolynomial.finSuccEquiv K n (MvPolynomial.X i)).map
        (algebraMap _ (Localization.AtPrime (fibrePrime M φ)))) =
      algebraMap _ (Localization.AtPrime M) (φ.symm (MvPolynomial.X i)) := by
  induction i using Fin.cases with
  | zero =>
    rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, polyToB,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  | succ j =>
    rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, polyToB,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, toB_algebraMap]
    show algebraMap _ _ (φ.symm (MvPolynomial.rename Fin.succ (MvPolynomial.X j))) = _
    rw [MvPolynomial.rename_X]

theorem polyToB_finSuccEquiv (p : MvPolynomial (Fin (n + 1)) K) :
    polyToB M φ ((MvPolynomial.finSuccEquiv K n p).map
        (algebraMap _ (Localization.AtPrime (fibrePrime M φ)))) =
      algebraMap _ (Localization.AtPrime M) (φ.symm p) := by
  induction p using MvPolynomial.induction_on with
  | C k =>
    rw [finSuccEquiv_C_C, Polynomial.map_C, polyToB, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, toB_algebraMap]
    show algebraMap _ _ (φ.symm (MvPolynomial.rename Fin.succ (MvPolynomial.C k))) = _
    rw [MvPolynomial.rename_C]
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, Polynomial.map_mul, hp, polyToB_X]

/-- `B = R_M` receives `C_𝔭[s₀]` compatibly with `R`. -/
theorem polyToB_coord (p : MvPolynomial (Fin (n + 1)) K) :
    polyToB M φ (coord M φ p) = algebraMap _ (Localization.AtPrime M) p := by
  rw [coord_apply, polyToB_finSuccEquiv, AlgEquiv.symm_apply_apply]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.polyToB_coord

/-- `R → C_𝔭[X][s₀]`: the coordinates, with coefficients moved into `C_𝔭[X]`. -/
noncomputable def liftHom : MvPolynomial (Fin (n + 1)) K →+*
    Polynomial (Polynomial (Localization.AtPrime (fibrePrime M φ))) :=
  (Polynomial.mapRingHom Polynomial.C).comp (coord M φ)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.liftHom

theorem liftHom_apply (p : MvPolynomial (Fin (n + 1)) K) :
    liftHom M φ p = (coord M φ p).map Polynomial.C := rfl

/-- `C_𝔭[X][s₀] → B[X]`: `X ↦ X`, `s₀ ↦ φ⁻¹ s₀`. -/
noncomputable def omega0 : Polynomial (Polynomial (Localization.AtPrime (fibrePrime M φ))) →+*
    Polynomial (Localization.AtPrime M) :=
  Polynomial.eval₂RingHom (Polynomial.mapRingHom (toB M φ))
    (Polynomial.C (algebraMap _ (Localization.AtPrime M) (φ.symm (MvPolynomial.X 0))))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.omega0

theorem omega0_liftHom (p : MvPolynomial (Fin (n + 1)) K) :
    omega0 M φ (liftHom M φ p) = Polynomial.C (algebraMap _ (Localization.AtPrime M) p) := by
  have h : (Polynomial.mapRingHom (toB M φ)).comp Polynomial.C = Polynomial.C.comp (toB M φ) :=
    RingHom.ext fun c => Polynomial.map_C _
  rw [liftHom_apply, omega0, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map, h,
    ← Polynomial.hom_eval₂]
  congr 1
  exact polyToB_coord M φ p

variable (w : MvPolynomial (Fin (n + 1)) K)

/-- `R_w → C_𝔭[X][s₀]_w`. -/
noncomputable def kappa0 : Localization.Away w →+* Localization.Away (liftHom M φ w) :=
  IsLocalization.Away.lift w
    (g := (algebraMap (Polynomial (Polynomial (Localization.AtPrime (fibrePrime M φ))))
      (Localization.Away (liftHom M φ w))).comp (liftHom M φ))
    (by
      rw [RingHom.comp_apply]
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (liftHom M φ w))
        (liftHom M φ w))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.kappa0

/-- `R_w[X] → C_𝔭[X][s₀]_w`, `X ↦ X`. -/
noncomputable def kappa : Polynomial (Localization.Away w) →+* Localization.Away (liftHom M φ w) :=
  Polynomial.eval₂RingHom (kappa0 M φ w)
    (algebraMap (Polynomial (Polynomial (Localization.AtPrime (fibrePrime M φ))))
      (Localization.Away (liftHom M φ w)) (Polynomial.C Polynomial.X))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.kappa

/-- `C_𝔭[X][s₀]_w → B[X]` for `w ∉ M`. -/
noncomputable def omega (hw : w ∉ M) :
    Localization.Away (liftHom M φ w) →+* Polynomial (Localization.AtPrime M) :=
  IsLocalization.Away.lift (liftHom M φ w) (g := omega0 M φ) (by
    rw [omega0_liftHom]
    exact Polynomial.isUnit_C.mpr (IsLocalization.map_units _ (⟨w, hw⟩ : M.primeCompl)))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.omega

theorem omega_comp_kappa0 (hw : w ∉ M) :
    (omega M φ w hw).comp (kappa0 M φ w) = Polynomial.C.comp (awayToAtPrime M hw) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers w)
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply]
  rw [kappa0, IsLocalization.Away.lift_eq, RingHom.comp_apply, omega,
    IsLocalization.Away.lift_eq, omega0_liftHom, awayToAtPrime, IsLocalization.Away.lift_eq]

/-- The square `R_w[X] → C_𝔭[X][s₀]_w → B[X]` commutes with `R_w[X] → B[X]`. -/
theorem omega_comp_kappa (hw : w ∉ M) :
    (omega M φ w hw).comp (kappa M φ w) = Polynomial.mapRingHom (awayToAtPrime M hw) := by
  apply Polynomial.ringHom_ext
  · intro c
    rw [RingHom.comp_apply, kappa, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_mapRingHom, Polynomial.map_C]
    exact RingHom.congr_fun (omega_comp_kappa0 M φ w hw) c
  · rw [RingHom.comp_apply, kappa, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, omega,
      IsLocalization.Away.lift_eq, omega0, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_mapRingHom, Polynomial.map_X]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.omega_comp_kappa

end Coordinates

section Core

variable {K : Type} [Field K] {n : ℕ} (M : Ideal (MvPolynomial (Fin (n + 1)) K)) [M.IsMaximal]
  (φ : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K)

/-- **The core of Cor 2.9** (steps 4–6). Let `φ f` be monic in `s₀` and coprime to `φ g` on the
fibre through `M`, with `g ∉ M`. Let `α₁ ∈ St_r(R_g[X])` die wherever `f` becomes a unit. Then
the image of `α₁` in `St_r(R_M[X])` is trivial. -/
theorem eq_one_of_monicFibre {r : ℕ}
    (hExc : ∀ (A : Type) [CommRing A], StZariskiExcisionAt A r)
    (hMon : ∀ (A : Type) [CommRing A], TulenbaevHorrocks.StMonicInjAt A r)
    {f g : MvPolynomial (Fin (n + 1)) K} (hg : g ∉ M)
    (hmon : (MvPolynomial.finSuccEquiv K n (φ f)).Monic)
    (hcop : IsCoprime ((MvPolynomial.finSuccEquiv K n (φ f)).map (fibreMap M φ))
      ((MvPolynomial.finSuccEquiv K n (φ g)).map (fibreMap M φ)))
    (α₁ : SteinbergGroup (Fin r) (Polynomial (Localization.Away g)))
    (hdie : ∀ (T : Type) [CommRing T] (ρ : Polynomial (Localization.Away g) →+* T),
      IsUnit (ρ (Polynomial.C (algebraMap _ _ f))) → ringMap ρ α₁ = 1) :
    ringMap (Polynomial.mapRingHom (awayToAtPrime M hg)) α₁ = 1 := by
  haveI : IsDomain (Localization.AtPrime (fibrePrime M φ)) :=
    IsLocalization.isDomain_of_local_atPrime inferInstance
  have hF : (coord M φ f).Monic := by rw [coord_apply]; exact hmon.map _
  have hG : coord M φ g ≠ 0 := fun h0 =>
    hg (by rw [coord_injective M φ (h0.trans (map_zero (coord M φ)).symm)]; exact M.zero_mem)
  have hFG : IsCoprime (coord M φ f) (coord M φ g) := by
    refine isCoprime_of_isCoprime_map (resMap M φ) (isUnit_of_resMap_ne_zero M φ) hF ?_
    rw [map_coord_resMap, map_coord_resMap]
    exact hcop
  have ha : (liftHom M φ f).Monic := by rw [liftHom_apply]; exact hF.map _
  have hb : liftHom M φ g ≠ 0 := by
    rw [liftHom_apply]
    exact (Polynomial.map_ne_zero_iff Polynomial.C_injective).mpr hG
  have hab : IsCoprime (liftHom M φ f) (liftHom M φ g) := by
    rw [liftHom_apply, liftHom_apply]
    exact hFG.map (Polynomial.mapRingHom Polynomial.C)
  have hunit : IsUnit (((IsLocalization.Away.awayToAwayLeft (liftHom M φ g) (liftHom M φ f) :
      Localization.Away (liftHom M φ g) →+*
        Localization.Away (liftHom M φ f * liftHom M φ g)).comp (kappa M φ g))
      (Polynomial.C (algebraMap _ _ f))) := by
    rw [RingHom.comp_apply, kappa, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, kappa0,
      IsLocalization.Away.lift_eq, RingHom.comp_apply, IsLocalization.Away.awayToAwayLeft_eq]
    have hu := IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (liftHom M φ f * liftHom M φ g)) (liftHom M φ f * liftHom M φ g)
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_left hu
  have hκ : ringMap (kappa M φ g) α₁ = 1 := by
    refine eq_one_of_excision (hExc _) (hMon _) ha hb hab _ ?_
    rw [SteinbergBasic.ringMap_ringMap]
    exact hdie _ _ hunit
  rw [← omega_comp_kappa M φ g hg, ← SteinbergBasic.ringMap_ringMap, hκ, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.eq_one_of_monicFibre

end Core

section Assembly

/-- **LSV Cor 2.9 (`m = 1`) for `K[s₁..s_k]`.** Assume GEO-AFF (`AffineMonicFibreStatement`),
F.4, H.b (non-FR) and the finitary step at `M`. Then an element of `St_r(R_M[X])` that dies in
`St_r(Frac(R)[X])` is trivial. -/
theorem eq_one_of_fracMap {K : Type} [Field K] {k r : ℕ} (hGeo : AffineMonicFibreStatement K)
    (hExc : ∀ (A : Type) [CommRing A], StZariskiExcisionAt A r)
    (hMon : ∀ (A : Type) [CommRing A], TulenbaevHorrocks.StMonicInjAt A r)
    (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal]
    (hFin : Cor29FinitaryAt (MvPolynomial (Fin k) K) M r)
    (α : SteinbergGroup (Fin r) (Polynomial (Localization.AtPrime M)))
    (hα : ringMap (Polynomial.mapRingHom (fracMap M)) α = 1) : α = 1 := by
  obtain ⟨g, hg, h, hh0, α₁, rfl, hdie⟩ := hFin α hα
  have hdieU : ∀ (T : Type) [CommRing T] (ρ : Polynomial (Localization.Away g) →+* T),
      IsUnit (ρ (Polynomial.C (algebraMap _ _ h))) → ringMap ρ α₁ = 1 :=
    fun T _ ρ hρ => ringMap_eq_one_of_isUnit hdie ρ hρ
  by_cases hhM : h ∈ M
  · obtain ⟨f₀, q, rfl, hrel, N, hq⟩ := exists_isRelPrime_factor g hh0
    have hqM : q ∉ M := by
      intro hqM
      obtain ⟨t, ht⟩ := hq
      exact hg ((inferInstance : M.IsPrime).mem_of_pow_mem N
        (by rw [ht]; exact M.mul_mem_right t hqM))
    have hf₀M : f₀ ∈ M := ((inferInstance : M.IsPrime).mem_or_mem hhM).resolve_right hqM
    have hf₀0 : f₀ ≠ 0 := left_ne_zero_of_mul hh0
    cases k with
    | zero =>
      exact absurd hf₀M
        (notMem_of_ne_zero_fin_zero (Ideal.IsMaximal.ne_top inferInstance) hf₀0)
    | succ n =>
      obtain ⟨φ, ⟨c, hc, hmon⟩, hcop⟩ := hGeo n f₀ g M inferInstance hf₀M hg hf₀0 hrel
      have hφC : φ (MvPolynomial.C c) = MvPolynomial.C c := by
        have := φ.commutes c
        rwa [MvPolynomial.algebraMap_eq] at this
      have hφf : φ (MvPolynomial.C c * f₀) = MvPolynomial.C c * φ f₀ := by
        rw [map_mul, hφC]
      refine eq_one_of_monicFibre M φ hExc hMon (f := MvPolynomial.C c * f₀) hg
        (by rw [hφf]; exact hmon) ?_ α₁ ?_
      · have hu : IsUnit (fibreMap M φ (MvPolynomial.C c)) :=
          ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C).map _
        rw [hφf, map_mul, finSuccEquiv_C_C, Polynomial.map_mul, Polynomial.map_C]
        exact (isCoprime_mul_unit_left_left (Polynomial.isUnit_C.mpr hu) _ _).mpr hcop
      · intro T _ ρ hρ
        apply hdieU T ρ
        let χ : MvPolynomial (Fin (n + 1)) K →+* T :=
          (ρ.comp Polynomial.C).comp (algebraMap _ (Localization.Away g))
        have hχ : IsUnit (χ (MvPolynomial.C c) * χ f₀) := by rw [← map_mul]; exact hρ
        have hχg : IsUnit (χ g) :=
          (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map
            (ρ.comp Polynomial.C)
        have hχq : IsUnit (χ q) :=
          isUnit_of_dvd_unit (map_dvd χ hq) (by rw [map_pow]; exact hχg.pow N)
        show IsUnit (χ (f₀ * q))
        rw [map_mul]
        exact (isUnit_of_mul_isUnit_right hχ).mul hχq
  · apply hdieU
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.isUnit_C, awayToAtPrime,
      IsLocalization.Away.lift_eq]
    exact IsLocalization.map_units _ (⟨h, hhM⟩ : M.primeCompl)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.eq_one_of_fracMap

/-- **Cor 2.9 for every maximal ideal**, as `unstableNKPoly_of_LSV` consumes it once wrapped in
`K2Poly.NKFieldInjAt` (`E = FractionRing R`, `ι = fracMap M`). -/
theorem cor29_mvPolynomial {K : Type} [Field K] {k r : ℕ} (hGeo : AffineMonicFibreStatement K)
    (hExc : ∀ (A : Type) [CommRing A], StZariskiExcisionAt A r)
    (hMon : ∀ (A : Type) [CommRing A], TulenbaevHorrocks.StMonicInjAt A r)
    (hFin : ∀ (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal],
      Cor29FinitaryAt (MvPolynomial (Fin k) K) M r)
    (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal]
    (α : SteinbergGroup (Fin r) (Polynomial (Localization.AtPrime M)))
    (hα : ringMap (Polynomial.mapRingHom (fracMap M)) α = 1) : α = 1 :=
  eq_one_of_fracMap hGeo hExc hMon M (hFin M) α hα

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.cor29_mvPolynomial

end Assembly

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
