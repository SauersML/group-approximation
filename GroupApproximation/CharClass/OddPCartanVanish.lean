import GroupApproximation.CharClass.OddPCartanVanishPerm
import GroupApproximation.CharClass.OddPCartanVanishSrc
import GroupApproximation.CharClass.OddPRedPow
import GroupApproximation.CharClass.CupOneComm
import GroupApproximation.Meta.AxiomGuard
import Mathlib.RingTheory.IntegralDomain
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# V: the bad residues of the odd-primary operations vanish

For an odd prime `p`, a cocycle `u` of EVEN degree `q` and a `W`-index `j ≤ pq`, the class of the
cochain operation `D_j(u)` of `OddPCochain.lean` vanishes unless `j ≡ 0` or `j ≡ −1` modulo
`2(p − 1)`, i.e. unless `p − 1` divides `(j + 1) / 2`:

* `oddDClass_eq_zero_of_not_dvd` — **V**, the statement lx-cartan-b and lx-pzero consume;
* `oddDClass_smul_vanMu` — its eigenvalue form, `(1 − r^{⌈j/2⌉}) · [D_j u] = 0` for every `r` prime
  to `p`.

## The argument

Fix `r` prime to `p`.  Two natural chain maps `W ⊗ C(X) → C(X)^{⊗p}`, linear over `F_p[ℤ/p]` with
the generator acting on the target as `T ^ r`, agree in degree `0`:

* `permDiag p r hr = σ_r ∘ Φ`, the diagonal followed by the signed slot permutation
  `σ_r = tupPerm (mulPerm p r hr)⁻¹` (`OddPCartanVanishPerm.lean`);
* `vanSrc p r hr = Φ ∘ (A_r ⊗ 1)`, with `A_r(e_{2m}) = r^m e_{2m}` and
  `A_r(e_{2m+1}) = r^m (1 + ⋯ + T^{r−1}) e_{2m+1}` (`OddPCartanVanishSrc.lean`).

The source is free and the target acyclic on the standard simplices, so the acyclic-models theorem
gives a natural homotopy `vanHomotopy` between them.  Evaluate the homotopy identity on a generator
`e_j ⊗ σ` against `u^{⊗p}`:

* `σ_r` is invisible to `u^{⊗p}` because `q` is even (`tupEval_tupPerm_const`), so the first map
  gives `D_j(u)(σ)`;
* the second gives `r^{⌈j/2⌉} D_j(u)(σ)` (`tupEval_galAlgHomP_vanCoef`);
* boundaries of the target evaluate to `0` against a cocycle;
* the resolution half of `d(e_j ⊗ σ)` dies, because the homotopy is linear over the group ring
  and a constant tuple does not see `T` (`van_eval_W`);
* the simplicial half evaluates as a coboundary (`addHom_oddDiffS_succ_formula`).

So `(1 − r^{⌈j/2⌉}) D_j(u)` is a coboundary (`van_core`).  Taking `r` a generator of `(ZMod p)ˣ`,
`r^{⌈j/2⌉} = 1` exactly when `p − 1` divides `⌈j/2⌉ = (j + 1) / 2`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace OddPCartanVanish

variable (p : ℕ) [NeZero p] [Fact p.Prime]

/-! ## 1. The eigenvalue -/

/-- The scalar by which `A_r` acts on `e_i` against a constant tuple: `r^m` on `e_{2m}`, `r^{m+1}` on
`e_{2m+1}`. -/
def vanMu (r i : ℕ) : ZMod p := (r : ZMod p) ^ (i / 2) * (if Even i then 1 else (r : ZMod p))

omit [NeZero p] [Fact p.Prime] in
theorem vanMu_zero (r : ℕ) : vanMu p r 0 = 1 := by
  rw [vanMu, Nat.zero_div, pow_zero, if_pos (⟨0, rfl⟩ : Even 0), mul_one]

omit [NeZero p] [Fact p.Prime] in
theorem vanMu_eq_pow (r i : ℕ) : vanMu p r i = (r : ZMod p) ^ ((i + 1) / 2) := by
  rw [vanMu]
  rcases Nat.even_or_odd i with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [if_pos ⟨m, rfl⟩, mul_one, show (m + m) / 2 = m by omega,
      show (m + m + 1) / 2 = m by omega]
  · have ho : ¬ Even (2 * m + 1) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨m, rfl⟩
    rw [if_neg ho, show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
      pow_succ]

/-- **The coefficient of `A_r`, against a constant tuple of single-degree cochains**, is the scalar
`vanMu p r i`. -/
theorem tupEval_galAlgHomP_vanCoef (r : ℕ) (hp : Odd p) {X : TopCat.{0}} (q : ℕ)
    (u : singularCochainGroup (ZMod p) X q) (k i : ℕ) (y : tupMod (ZMod p) X p k) :
    tupEval (ZMod p) X p k (fun _ => Pi.single q u)
        (galAlgHomP (tupT (ZMod p) X p k ^ 1) (tupT_pow_pow p X p k 1 (dvd_mul_left p 1))
          (vanCoef p r i) y)
      = vanMu p r i * tupEval (ZMod p) X p k (fun _ => Pi.single q u) y := by
  have hq : ∀ n, n ≠ q → (Pi.single q u : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) n = 0 :=
    fun n hn => by rw [Pi.single_eq_of_ne hn]
  rw [vanCoef, vanMu, map_mul, map_pow, map_natCast, Module.End.mul_apply, ← Nat.cast_pow,
    Module.End.natCast_apply, map_nsmul, nsmul_eq_mul, Nat.cast_pow, mul_assoc]
  by_cases he : Even i
  · rw [if_pos he, if_pos he, map_one, Module.End.one_apply, one_mul]
  · rw [if_neg he, if_neg he, grNr, map_sum, LinearMap.sum_apply, map_sum]
    simp only [map_pow, galAlgHomP_grGen (Fact.out : p.Prime).one_lt, pow_one]
    rw [Finset.sum_congr rfl fun l _ => tupEval_tupT_pow_const (ZMod p) hp _ q hq k l y,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## 2. The two maps and the homotopy -/

/-- `σ_r ∘ Φ` in degree `k`, linear over the group ring acting on the target through `T ^ r`. -/
def permDiagLin (r : ℕ) (hr : Nat.Coprime r p) (X : TopCat.{0}) (k : ℕ) :
    @LinearMap (GroupRingZMod p) (GroupRingZMod p) _ _ (RingHom.id (GroupRingZMod p))
      (OddWTensor p k X) (tupMod (ZMod p) X p k) _ _ _ (tupModule p X p k r (dvd_mul_left p r)) :=
  letI := tupModule p X p k r (dvd_mul_left p r)
  { toFun := fun x => tupPerm (ZMod p) X p k (mulPerm p r hr)⁻¹ (oddDiagApp p X k x)
    map_add' := fun x y => by simp only [oddDiagApp_add, map_add]
    map_smul' := fun c x => by
      show tupPerm (ZMod p) X p k (mulPerm p r hr)⁻¹ (oddDiagApp p X k (c • x))
        = galAlgHomP (tupT (ZMod p) X p k ^ r) (tupT_pow_pow p X p k r (dvd_mul_left p r)) c
            (tupPerm (ZMod p) X p k (mulPerm p r hr)⁻¹ (oddDiagApp p X k x))
      rw [oddDiagApp_smul]
      exact galAlgHomP_comm p (tupT (ZMod p) X p k ^ 1)
        (tupT_pow_pow p X p k 1 (dvd_mul_left p 1)) (tupT (ZMod p) X p k ^ r)
        (tupT_pow_pow p X p k r (dvd_mul_left p r)) (tupPerm (ZMod p) X p k (mulPerm p r hr)⁻¹)
        (fun v => by rw [pow_one]; exact tupPerm_mulPerm_inv_tupT p r hr X k v) c _ }

/-- The degree-`k` component of `σ_r ∘ Φ`, as a morphism over the group ring. -/
def permDiagHom (r : ℕ) (hr : Nat.Coprime r p) (X : TopCat.{0}) (k : ℕ) :
    ((oddSrc p (oddSingularBoundary p)).obj X).X k
      ⟶ ((oddTgt p p r (dvd_mul_left p r)).obj X).X k :=
  letI := tupModule p X p k r (dvd_mul_left p r)
  ModuleCat.ofHom (permDiagLin p r hr X k)

/-- `σ_r ∘ Φ` at one space, as a map of complexes. -/
def permDiagCx (r : ℕ) (hr : Nat.Coprime r p) (X : TopCat.{0}) :
    (oddSrc p (oddSingularBoundary p)).obj X ⟶ (oddTgt p p r (dvd_mul_left p r)).obj X where
  f k := permDiagHom p r hr X k
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    rw [oddSrc_obj_d, oddTgt_obj_d]
    letI := tupModule p X p (j + 1) r (dvd_mul_left p r)
    letI := tupModule p X p j r (dvd_mul_left p r)
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro q
    apply LinearMap.ext_ring
    show tupD (ZMod p) X p j (tupPerm (ZMod p) X p (j + 1) (mulPerm p r hr)⁻¹
        (oddDiagApp p X (j + 1) (Finsupp.single q 1)))
      = tupPerm (ZMod p) X p j (mulPerm p r hr)⁻¹
          (oddDiagApp p X j (oddDiff p (oddSingularBoundary p) X j (Finsupp.single q 1)))
    rw [← tupPerm_tupD, oddDiagApp_d]

/-- **`σ_r ∘ Φ`**, into the target on which the generator acts as `T ^ r`. -/
def permDiag (r : ℕ) (hr : Nat.Coprime r p) :
    oddSrc p (oddSingularBoundary p) ⟶ oddTgt p p r (dvd_mul_left p r) where
  app X := permDiagCx p r hr X
  naturality X Y f := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    letI := tupModule p X p k r (dvd_mul_left p r)
    letI := tupModule p Y p k r (dvd_mul_left p r)
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro q
    apply LinearMap.ext_ring
    show tupPerm (ZMod p) Y p k (mulPerm p r hr)⁻¹
        (oddDiagApp p Y k ((((oddSrc p (oddSingularBoundary p)).map f).f k).hom
          (Finsupp.single q 1)))
      = tupMap (ZMod p) f p k (tupPerm (ZMod p) X p k (mulPerm p r hr)⁻¹
          (oddDiagApp p X k (Finsupp.single q 1)))
    rw [tupMap_tupPerm, oddDiagApp_natural]
    rfl

theorem permDiag_app_f_apply (r : ℕ) (hr : Nat.Coprime r p) (X : TopCat.{0}) (k : ℕ)
    (x : OddWTensor p k X) :
    (((permDiag p r hr).app X).f k).hom x
      = tupPerm (ZMod p) X p k (mulPerm p r hr)⁻¹ (oddDiagApp p X k x) :=
  rfl

/-- **The two maps agree in degree `0`**: both send `e_0 ⊗ x` to the constant tuple `(x, …, x)`, which
a slot permutation fixes with sign `+1`. -/
theorem permDiag_vanSrc_zero (r : ℕ) (hr : Nat.Coprime r p) (X : TopCat.{0}) :
    ((permDiag p r hr).app X).f 0 = ((vanSrc p r hr).app X).f 0 := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro q
  apply LinearMap.ext_ring
  show tupPerm (ZMod p) X p 0 (mulPerm p r hr)⁻¹ (oddDiagApp p X 0 (Finsupp.single q 1))
    = (((vanSrc p r hr).app X).f 0).hom (Finsupp.single q 1)
  rw [vanSrc_app_f_zero]
  obtain ⟨n, x⟩ := q
  obtain rfl : n = 0 := Fin.fin_one_eq_zero n
  have hexp : permExp X (mulPerm p r hr)⁻¹ (diagPt X p x).1 = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      split_ifs <;> rfl
  have hperm : permTupIdx X (mulPerm p r hr)⁻¹ (diagPt X p x) = diagPt X p x :=
    Subtype.ext (funext fun _ => rfl)
  rw [oddDiagApp_zero, tupPerm_single, hexp, hperm, pow_zero, one_smul]

/-- **The natural homotopy** `σ_r ∘ Φ ≃ Φ ∘ (A_r ⊗ 1)`, from the acyclic-models theorem. -/
def vanHomotopy (r : ℕ) (hr : Nat.Coprime r p) :
    NaturalHomotopy (oddSrc p (oddSingularBoundary p)) (oddTgt p p r (dvd_mul_left p r))
      (permDiag p r hr) (vanSrc p r hr) :=
  acyclicModelsHomotopy (oddSrcFree p (oddSingularBoundary p))
    (oddTgt_acyclicOnModels p p r (dvd_mul_left p r)) (permDiag p r hr) (vanSrc p r hr)
    (permDiag_vanSrc_zero p r hr)

/-! ## 3. Evaluating the homotopy identity -/

/-- The resolution half of the differential evaluates to zero through the homotopy. -/
theorem van_eval_W (r : ℕ) (hr : Nat.Coprime r p) (hp : Odd p) {X : TopCat.{0}} (q : ℕ)
    (u : singularCochainGroup (ZMod p) X q) (k : ℕ) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    tupEval (ZMod p) X p (k + 1) (fun _ => Pi.single q u)
        (((vanHomotopy p r hr).s k X).hom (oddDiffW p X k n σ)) = 0 := by
  have hq : ∀ n, n ≠ q → (Pi.single q u : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) n = 0 :=
    fun n hn => by rw [Pi.single_eq_of_ne hn]
  revert σ
  induction n using Fin.lastCases with
  | last =>
    intro σ
    rw [oddDiffW_last, map_zero, map_zero]
  | cast j =>
    intro σ
    have hs : ((vanHomotopy p r hr).s k X).hom (altCoeff (grS p) (grNorm p) (k - j.val) •
          Finsupp.single (⟨j, σ⟩ : WSIndex k X) (1 : GroupRingZMod p))
        = galAlgHomP (tupT (ZMod p) X p (k + 1) ^ r)
            (tupT_pow_pow p X p (k + 1) r (dvd_mul_left p r))
            (altCoeff (grS p) (grNorm p) (k - j.val))
            (((vanHomotopy p r hr).s k X).hom (Finsupp.single (⟨j, σ⟩ : WSIndex k X) 1)) :=
      LinearMap.map_smul ((vanHomotopy p r hr).s k X).hom _ _
    rw [oddDiffW_castSucc, hs]
    by_cases he : Even (k - j.val)
    · rw [altCoeff_even _ _ he, grS, map_sub, map_one,
        galAlgHomP_grGen (Fact.out : p.Prime).one_lt, LinearMap.sub_apply, Module.End.one_apply,
        map_sub, tupEval_tupT_pow_const (ZMod p) hp _ q hq, sub_self]
    · rw [altCoeff_odd _ _ he, grNorm, map_sum, LinearMap.sum_apply, map_sum]
      simp only [map_pow, galAlgHomP_grGen (Fact.out : p.Prime).one_lt, ← pow_mul]
      rw [Finset.sum_congr rfl fun l _ =>
          tupEval_tupT_pow_const (ZMod p) hp _ q hq (k + 1) (r * l) _,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

omit [NeZero p] [Fact p.Prime] in
/-- **The simplicial half of the differential, through an additive functional**: the Koszul sign
times the alternating sum over the faces. -/
theorem addHom_oddDiffS_succ_formula {X : TopCat.{0}} (k : ℕ) (m : Fin (k + 1))
    (F : OddWTensor p k X →+ ZMod p) (σ : singularSimplices X (m.val + 1)) :
    F (oddDiffS p (oddSingularBoundary p) X k (Fin.succ m) (simplexEquiv X (m.val + 1) σ))
      = (-1 : ZMod p) ^ (k - m.val) * ∑ i : Fin (m.val + 2), (-1 : ZMod p) ^ (i : ℕ) *
          F (Finsupp.single
            (⟨m, simplexEquiv X m.val (faceSimplex X m.val i σ)⟩ : WSIndex k X) 1) := by
  have hb : (oddSingularBoundary p).bd X m.val
        (Finsupp.single (simplexEquiv X (m.val + 1) σ) (1 : GroupRingZMod p))
      = Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (simplexEquiv X m.val)
          ((((singFreeR (GroupRingZMod p)).obj X).d (m.val + 1) m.val).hom
            (Finsupp.single σ 1)) := by
    show bdRHom (GroupRingZMod p) X m.val (Finsupp.single (simplexEquiv X (m.val + 1) σ) 1) = _
    rw [bdRHom_apply, Finsupp.mapDomain_single, Equiv.symm_apply_apply, Finsupp.lmapDomain_apply]
  have hterm : ∀ i : Fin (m.val + 2),
      F (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (fun τ => (⟨m, τ⟩ : WSIndex k X))
          (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (simplexEquiv X m.val)
            (((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (faceSimplex X m.val i σ) (1 : GroupRingZMod p))))
        = (-1 : ZMod p) ^ (i : ℕ) *
            F (Finsupp.single
              (⟨m, simplexEquiv X m.val (faceSimplex X m.val i σ)⟩ : WSIndex k X) 1) := by
    intro i
    rw [map_zsmul, map_zsmul, map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one]
  rw [oddDiffS_succ, hb, singFreeR_d_single]
  rcases Nat.even_or_odd (k - m.val) with he | he
  · rw [he.neg_one_pow, he.neg_one_pow, one_smul, one_mul, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => hterm i
  · rw [he.neg_one_pow, he.neg_one_pow, neg_one_smul, map_neg, neg_one_mul, map_sum, map_sum,
      map_sum]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => hterm i)

/-- **The homotopy identity, evaluated on a generator.** -/
theorem van_homotopy_eval (r : ℕ) (hr : Nat.Coprime r p) (hp : Odd p) {X : TopCat.{0}} (q : ℕ)
    (hqe : Even q) (u : singularCochainGroup (ZMod p) X q)
    (hu : cochainCoboundary (ZMod p) X q u = 0) (k : ℕ) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    tupEval (ZMod p) X p (k + 1) (fun _ => Pi.single q u)
        (oddDiagApp p X (k + 1) (Finsupp.single (⟨n, σ⟩ : WSIndex (k + 1) X) 1))
      - vanMu p r (k + 1 - n.val) * tupEval (ZMod p) X p (k + 1) (fun _ => Pi.single q u)
          (oddDiagApp p X (k + 1) (Finsupp.single (⟨n, σ⟩ : WSIndex (k + 1) X) 1))
      = tupEval (ZMod p) X p (k + 1) (fun _ => Pi.single q u)
          (((vanHomotopy p r hr).s k X).hom (oddDiffS p (oddSingularBoundary p) X k n σ)) := by
  have hq : ∀ n, n ≠ q → (Pi.single q u : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) n = 0 :=
    fun n hn => by rw [Pi.single_eq_of_ne hn]
  have hc := congrArg (fun h => tupEval (ZMod p) X p (k + 1) (fun _ => Pi.single q u)
      (ModuleCat.Hom.hom h (Finsupp.single (⟨n, σ⟩ : WSIndex (k + 1) X) (1 : GroupRingZMod p))))
    ((vanHomotopy p r hr).comm_succ k X)
  simp only [ModuleCat.hom_sub, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.comp_apply, map_sub, map_add] at hc
  rw [permDiag_app_f_apply, tupEval_tupPerm_const (ZMod p) X _ _ q hqe hq, vanSrc_app_f_apply,
    vanSrcLin_single, vanGen, tupEval_galAlgHomP_vanCoef p r hp q u (k + 1), oddSrc_obj_d,
    ModuleCat.hom_ofHom, oddDiff_single, oddDiffGen, map_add, map_add,
    van_eval_W p r hr hp q u k n σ, zero_add, oddTgt_obj_d, tupDHom_hom_apply,
    tupEval_tupD_eq_zero (ZMod p) _ (fun _ => gCoboundary_piSingle_eq_zero (ZMod p) u hu),
    add_zero] at hc
  exact hc

/-! ## 4. The cochain identity -/

/-- The cochain of the diagonal on the generators of simplex degree `n` in total degree `k + 1`. -/
def vanD (k : ℕ) (n : Fin (k + 2)) {X : TopCat.{0}}
    (φ : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) : singularCochainGroup (ZMod p) X n.val :=
  cochainOfFun n.val fun σ => tupEval (ZMod p) X p (k + 1) (fun _ => φ)
    (oddDiagApp p X (k + 1) (Finsupp.single (⟨n, simplexEquiv X n.val σ⟩ : WSIndex (k + 1) X) 1))

theorem vanD_eval (k : ℕ) (n : Fin (k + 2)) {X : TopCat.{0}}
    (φ : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (σ : singularSimplices X n.val) :
    cochainEval n.val (vanD p k n φ) σ
      = tupEval (ZMod p) X p (k + 1) (fun _ => φ)
          (oddDiagApp p X (k + 1)
            (Finsupp.single (⟨n, simplexEquiv X n.val σ⟩ : WSIndex (k + 1) X) 1)) := by
  unfold vanD
  exact cochainEval_cochainOfFun _ _ σ

/-- The homotopy cochain on `m`-simplices. -/
def vanPsi (r : ℕ) (hr : Nat.Coprime r p) (k : ℕ) (m : Fin (k + 1)) {X : TopCat.{0}}
    (φ : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) : singularCochainGroup (ZMod p) X m.val :=
  cochainOfFun m.val fun τ => tupEval (ZMod p) X p (k + 1) (fun _ => φ)
    (((vanHomotopy p r hr).s k X).hom
      (Finsupp.single (⟨m, simplexEquiv X m.val τ⟩ : WSIndex k X) 1))

theorem vanPsi_eval (r : ℕ) (hr : Nat.Coprime r p) (k : ℕ) (m : Fin (k + 1)) {X : TopCat.{0}}
    (φ : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (τ : singularSimplices X m.val) :
    cochainEval m.val (vanPsi p r hr k m φ) τ
      = tupEval (ZMod p) X p (k + 1) (fun _ => φ)
          (((vanHomotopy p r hr).s k X).hom
            (Finsupp.single (⟨m, simplexEquiv X m.val τ⟩ : WSIndex k X) 1)) := by
  unfold vanPsi
  exact cochainEval_cochainOfFun _ _ τ

/-- The right-hand side of the cochain identity: `0` in simplex degree `0`, a coboundary above. -/
def vanRHS (r : ℕ) (hr : Nat.Coprime r p) (k : ℕ) (n : Fin (k + 2)) {X : TopCat.{0}}
    (φ : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) : singularCochainGroup (ZMod p) X n.val :=
  Fin.cases (motive := fun n : Fin (k + 2) => singularCochainGroup (ZMod p) X n.val) 0
    (fun m => cochainCoboundary (ZMod p) X m.val
      (((-1 : ZMod p) ^ (k - m.val)) • vanPsi p r hr k m φ)) n

/-- **The cochain identity**: `(1 − vanMu) · D` is `0` or a coboundary. -/
theorem van_core (r : ℕ) (hr : Nat.Coprime r p) (hp : Odd p) {X : TopCat.{0}} (q : ℕ)
    (hqe : Even q) (u : singularCochainGroup (ZMod p) X q)
    (hu : cochainCoboundary (ZMod p) X q u = 0) (k : ℕ) (n : Fin (k + 2)) (i : ℕ)
    (hi : k + 1 - n.val = i) :
    (1 - vanMu p r i) • vanD p k n (Pi.single q u) = vanRHS p r hr k n (Pi.single q u) := by
  subst hi
  apply cochain_ext
  intro σ
  rw [cochainEval_smul, vanD_eval, sub_mul, one_mul,
    van_homotopy_eval p r hr hp q hqe u hu k n (simplexEquiv X n.val σ)]
  revert σ
  induction n using Fin.cases with
  | zero =>
    intro σ
    rw [oddDiffS_zero, map_zero, map_zero]
    exact (cochainEval_zero _ σ).symm
  | succ m =>
    intro σ
    refine (addHom_oddDiffS_succ_formula p k m
      ((tupEval (ZMod p) X p (k + 1) (fun _ => Pi.single q u)).toAddMonoidHom.comp
        ((vanHomotopy p r hr).s k X).hom.toAddMonoidHom) σ).trans ?_
    show _ = cochainEval (m.val + 1) (cochainCoboundary (ZMod p) X m.val
        (((-1 : ZMod p) ^ (k - m.val)) • vanPsi p r hr k m (Pi.single q u))) σ
    rw [cochainCoboundary_eval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [cochainEval_smul, vanPsi_eval, mul_left_comm]
    rfl

/-- The right-hand side has zero class. -/
theorem vanRHS_class_zero (r : ℕ) (hr : Nat.Coprime r p) {X : TopCat.{0}}
    (φ : ∀ n : ℕ, singularCochainGroup (ZMod p) X n) (k : ℕ) (n : Fin (k + 2))
    (hcoc : cochainCoboundary (ZMod p) X n.val (vanRHS p r hr k n φ) = 0) :
    cocycleClassK (ZMod p) X n.val (vanRHS p r hr k n φ) hcoc = 0 := by
  revert hcoc
  induction n using Fin.cases with
  | zero =>
    intro hcoc
    exact cocycleClassK_zero (ZMod p) X 0 hcoc
  | succ m =>
    intro hcoc
    exact cocycleClassK_coboundary_zero (ZMod p) X m.val _ hcoc

/-! ## 5. V -/

/-- **The eigenvalue form of V**: for every `r` prime to `p`, `(1 − r^{⌈j/2⌉}) · [D_j u] = 0` on
classes of even degree. -/
theorem oddDClass_smul_vanMu (r : ℕ) (hr : Nat.Coprime r p) (hp : Odd p) {X : TopCat.{0}}
    (q j : ℕ) (hqe : Even q) (hj : j ≤ p * q) (x : Hmod (ZMod p) X q) :
    (1 - vanMu p r j) • oddDClass p hp q j hj x = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [vanMu_zero, sub_self, zero_smul]
  obtain ⟨u, hu, rfl⟩ := cocycleClassK_surjective (ZMod p) X q x
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hj
    omega
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).one_lt; omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hsm : cochainCoboundary (ZMod (p' + 1)) X ((p' + 1) * (q' + 1) - j)
      ((1 - vanMu (p' + 1) r j) • oddD (p' + 1) (q' + 1) j u) = 0 := by
    rw [CupOneLocal.cochainCoboundary_smul, oddD_cocycle (p' + 1) hp (q' + 1) j hj u hu, smul_zero]
  rw [oddDClass_mk, ← CupOneLocal.cocycleClassK_smul (ZMod (p' + 1)) X _ _ _ _ hsm]
  have hk : (p' + 1) * (q' + 1) = (p' + 1) * q' + p' + 1 := by ring
  have hlt : (p' + 1) * (q' + 1) - j < (p' + 1) * q' + p' + 2 := by omega
  have hc := van_core (p' + 1) r hr hp (q' + 1) hqe u hu ((p' + 1) * q' + p')
    ⟨(p' + 1) * (q' + 1) - j, hlt⟩ j
    (by show (p' + 1) * q' + p' + 1 - ((p' + 1) * (q' + 1) - j) = j; omega)
  have hEq : (1 - vanMu (p' + 1) r j) • oddD (p' + 1) (q' + 1) j u
      = vanRHS (p' + 1) r hr ((p' + 1) * q' + p') ⟨(p' + 1) * (q' + 1) - j, hlt⟩
          (Pi.single (q' + 1) u) := hc
  have hcoc : cochainCoboundary (ZMod (p' + 1)) X ((p' + 1) * (q' + 1) - j)
      (vanRHS (p' + 1) r hr ((p' + 1) * q' + p') ⟨(p' + 1) * (q' + 1) - j, hlt⟩
        (Pi.single (q' + 1) u)) = 0 := by
    rw [← hEq]
    exact hsm
  rw [cocycleClassK_congr (ZMod (p' + 1)) X _ hEq hsm hcoc]
  exact vanRHS_class_zero (p' + 1) r hr (Pi.single (q' + 1) u) ((p' + 1) * q' + p')
    ⟨(p' + 1) * (q' + 1) - j, hlt⟩ hcoc

/-- V at a single `r`: if `r^{⌈j/2⌉} ≠ 1` then `[D_j u] = 0`. -/
theorem oddDClass_eq_zero_of_vanMu_ne_one (r : ℕ) (hr : Nat.Coprime r p) (hp : Odd p)
    {X : TopCat.{0}} (q j : ℕ) (hqe : Even q) (hj : j ≤ p * q) (hμ : vanMu p r j ≠ 1)
    (x : Hmod (ZMod p) X q) : oddDClass p hp q j hj x = 0 := by
  have h := oddDClass_smul_vanMu p r hr hp q j hqe hj x
  have hne : (1 - vanMu p r j) ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ)
  rw [← inv_smul_smul₀ hne (oddDClass p hp q j hj x), h, smul_zero]

/-- **V.**  On classes of even degree `q`, the class of `D_j` vanishes unless `p − 1` divides
`(j + 1) / 2`, i.e. unless `j ≡ 0` or `j ≡ −1` modulo `2(p − 1)`. -/
theorem oddDClass_eq_zero_of_not_dvd (hp : Odd p) {X : TopCat.{0}} (q j : ℕ) (hqe : Even q)
    (hj : j ≤ p * q) (hbad : ¬ (p - 1) ∣ (j + 1) / 2) (x : Hmod (ZMod p) X q) :
    oddDClass p hp q j hj x = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hcast : (((g : ZMod p).val : ℕ) : ZMod p) = g := ZMod.natCast_zmod_val _
  have hne : (g : ZMod p).val ≠ 0 := by
    intro h0
    apply g.ne_zero
    rw [← hcast, h0, Nat.cast_zero]
  have hr : Nat.Coprime (g : ZMod p).val p :=
    (Nat.coprime_of_lt_prime hne (ZMod.val_lt _) (Fact.out : p.Prime)).symm
  refine oddDClass_eq_zero_of_vanMu_ne_one p _ hr hp q j hqe hj ?_ x
  intro h1
  apply hbad
  rw [vanMu_eq_pow, hcast] at h1
  have h2 : g ^ ((j + 1) / 2) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
  rw [← hcard, ← hg]
  exact orderOf_dvd_iff_pow_eq_one.mpr h2

#audit_axioms permDiag_vanSrc_zero
#audit_axioms van_homotopy_eval
#audit_axioms van_core
#audit_axioms oddDClass_smul_vanMu
#audit_axioms oddDClass_eq_zero_of_not_dvd

end OddPCartanVanish

end

end GroupApproximation.CharClass
