import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWideSigma
import GroupApproximation.Meta.AxiomGuard

/-!
# The wide Nagao step, part 5: the `|K|`-induction and the wiring to `K₂ = ⊥`

Lane `bh-met-93l`.  Notation of `ElemFPK2PolyNagaoWideSigma`; `J = K \ {m}`.

* `k2PolyNagaoWide_stab_of_gens`: a `σ` with `σ(e_L) ∈ Q` passing `k2PolyNagao_Gens` gives
  `Stab(K, L)` (closure over the generators of `G`, then the coset trick).
* `k2PolyNagaoWide_Statement` (**the residual**): the single check of the explicit section
  `k2PolyNagaoWide_sigma` at the one generator `x_mL(1)`, given `Stab(J, m)`.
* `k2PolyNagaoWide_stab_all`: the residual gives `Stab(K, L)` for every nonempty `K`, by strong
  induction on `|K|`: `K = {m}` is the rank-one case (`σ₀` and lane 93d's Weyl check), and for
  `|K| ≥ 2` the inductive hypothesis gives `Stab(J, m)`, so `k2PolyNagaoWide_gens_of_check`.
* `k2PolyNagaoWide_wide_of_statement`: the residual gives `k2PolyNagaoSigma_WideStatement`.
* `k2PolyNagaoWide_K2_bot_of_statement`: the residual gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`.

**LOUD: the residual is NOT proved here.  It is TRUE, and it is logically EQUIVALENT to
`k2PolyNagaoSigma_WideStatement` (both are true), but it is STRICTLY SMALLER IN PROOF
CONTENT and is not a restatement of it.**  The wide statement asks for *some* `σ` and *all*
the checks of `k2PolyNagao_Gens`.  Here `σ` is explicit (Euclidean reduction of the
`J`-coordinates by `S_K`, then lane 93d's pair word on `{m, L}`), and every check is proved
except one: the one at `x_mL(1)`.  The proved parts are:
- the checks at every element of `Q`, including `x_im(1)`, `x_mi(1)`, `x_Lm(1)`, `x_Lm(X)` and
  `x_Lm(X^k)`;
- `σ(e_L) ∈ Q`;
- the termination of the Euclidean reduction;
- the induction on `|K|` that supplies `Stab(J, m)`.

**Truth.**  Take any `v` in the orbit.  Then `σ(v) = q_v σ₀(r_v)` lies in `G`, with
`q_v ∈ Q` and `σ₀(r_v) ∈ G_{mL}`.  Also `σ(v) e_L = q_v r_v = v`.  So the check element
`σ(x v)⁻¹ x_mL(1) σ(v)` lies in `G` and fixes `e_L`.  By `Stab(K, L)` it then lies in `Q`.
`Stab(K, L)` is true (lane 92c's `k2PolyNF_StabStatement`, which holds because
`K₂(N, F_p[X]) = 0`).  That fact is used only to argue truth; it is not an input here.
The matrix shadows were checked by the scratchpad script `bh-met-93l/chk.py`:
- the Euclidean moves strictly decrease `μ` and keep `e_L`-orbits;
- `ν(f mod g) < ν(g)`;
- `σ₀(r) e_L = r` and `σ(v) e_L = v`;
- the conjugation identities;
- the check element at `x_mL(1)` fixes `e_L`.
The runs were `F_2`, `F_3`, `F_5` with `|K| = 2, 3`.

**Why `Stab(J, m)` comes from the induction.**  It does not come from `SL = E`, which is
circular.  It is lane 92c's statement one size down, with `L := m`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_one unitVec
  rootSpan_mono)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- **Coset trick.**  A `σ` with `σ(e_L) ∈ Q` passing `k2PolyNagao_Gens` gives `Stab(K, L)`. -/
theorem k2PolyNagaoWide_stab_of_gens {K : Finset I} {m L : I} (hLK : L ∉ K) (hmL : m ≠ L)
    (hmK : m ∈ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    {σ : (I → Polynomial (ZMod p)) → SteinbergGroup I (Polynomial (ZMod p))}
    (hσ : σ (unitVec L) ∈ k2PolyNF_Q p K L) (hG : k2PolyNagao_Gens p K L σ m hmL) :
    k2PolyNagaoWide_Stab p K L := by
  obtain ⟨hS, hy, h1, hX, hsing⟩ := hG
  obtain ⟨n, hmn, hLn⟩ := hthird m L
  have hm' : m ∈ insert L K := Finset.mem_insert_of_mem hmK
  have hL' : L ∈ insert L K := Finset.mem_insert_self L K
  have hSg : ∀ (i : I) (him : i ≠ m), i ∈ K →
      k2PolyEuclid_Good p K L σ (x i m him (1 : Polynomial (ZMod p))) ∧
        k2PolyEuclid_Good p K L σ (x m i him.symm (1 : Polynomial (ZMod p))) :=
    fun i him hiK =>
      ⟨⟨k2PolyEuclid_x_mem_G him 1 (Finset.mem_insert_of_mem hiK) hm', (hS i him hiK).1⟩,
        ⟨k2PolyEuclid_x_mem_G him.symm 1 hm' (Finset.mem_insert_of_mem hiK),
          (hS i him hiK).2⟩⟩
  have hyg : k2PolyEuclid_Good p K L σ (x m L hmL (1 : Polynomial (ZMod p))) :=
    ⟨k2PolyEuclid_x_mem_G hmL 1 hm' hL', hy⟩
  have h1g : k2PolyEuclid_Good p K L σ (x L m hmL.symm (1 : Polynomial (ZMod p))) :=
    ⟨k2PolyEuclid_x_mem_G hmL.symm 1 hL' hm', h1⟩
  have hXg : k2PolyEuclid_Good p K L σ
      (x L m hmL.symm (Polynomial.X : Polynomial (ZMod p))) :=
    ⟨k2PolyEuclid_x_mem_G hmL.symm _ hL' hm', hX⟩
  have hsg : (∀ i ∈ K, i = m) → ∀ k : ℕ, k2PolyEuclid_Good p K L σ
      (x L m hmL.symm ((Polynomial.X : Polynomial (ZMod p)) ^ k)) :=
    fun hs k => ⟨k2PolyEuclid_x_mem_G hmL.symm _ hL' hm', hsing hs k⟩
  have hLmg : ∀ f : Polynomial (ZMod p), k2PolyEuclid_Good p K L σ (x L m hmL.symm f) :=
    fun f => k2PolyNagao_good_Lm_all hLK hmL hmn hLn hSg hyg h1g hXg hsg f
  have hgen : ∀ (i j : I) (hij : i ≠ j) (a : Polynomial (ZMod p)), i ∈ insert L K →
      j ∈ insert L K → ∀ v : I → Polynomial (ZMod p),
        (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) →
          (σ (act (x i j hij a) v))⁻¹ * x i j hij a * σ v ∈ k2PolyNF_Q p K L :=
    fun i j hij a hi hj v hv =>
      (k2PolyEuclid_good_all hLK hmL hmn hLn hSg hyg hLmg i j hij a hi hj).2 v hv
  intro g hg hfix
  have hc := k2PolyNF_closure σ hgen hg (unitVec L) ⟨1, Subgroup.one_mem _, act_one _⟩
  rw [hfix] at hc
  have e : g = σ (unitVec L) * ((σ (unitVec L))⁻¹ * g * σ (unitVec L)) *
      (σ (unitVec L))⁻¹ := by
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hc) (Subgroup.inv_mem _ hσ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_stab_of_gens

/-- `S_J ≤ S_K`. -/
theorem k2PolyNagaoWide_S_erase_le (K : Finset I) (m : I) :
    k2PolyDeg_S p (K.erase m) ≤ k2PolyDeg_S p K := fun _ hs =>
  rootSpan_mono (p := fun i j => i ∈ K.erase m ∧ j ∈ K.erase m)
    (q := fun i j => i ∈ K ∧ j ∈ K)
    (fun _ _ _ h => ⟨Finset.mem_of_mem_erase h.1, Finset.mem_of_mem_erase h.2⟩) hs

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_S_erase_le

/-- **The residual of lane `bh-met-93l`.**  Given `Stab(J, m)` (`J = K \ {m}` nonempty), the
explicit section `k2PolyNagaoWide_sigma` passes the check at the single generator `x_mL(1)`.
TRUE; LOUD: logically equivalent to `k2PolyNagaoSigma_WideStatement`, strictly smaller in
proof content (one generator check for an explicit `σ`; module docstring). -/
def k2PolyNagaoWide_Statement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (m L : I)
    (hmL : m ≠ L), L ∉ K → m ∈ K → (∃ i ∈ K, i ≠ m) → (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1) →
    (∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1) →
    k2PolyNagaoWide_Stab p (K.erase m) m →
    k2PolyEuclid_Check p K L (k2PolyNagaoWide_sigma p K m L hmL)
      (x m L hmL (1 : Polynomial (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Statement

/-- The step `|K| ≥ 2`: given `Stab(J, m)`, the residual makes `k2PolyNagaoWide_sigma` pass
every check of `k2PolyNagao_Gens`. -/
theorem k2PolyNagaoWide_step_gens (hR : k2PolyNagaoWide_Statement) {K : Finset I} {m L : I}
    (hmL : m ≠ L) (hLK : L ∉ K) (hmK : m ∈ K) (him : ∃ i ∈ K, i ≠ m)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (hSK : ∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1)
    (hJ : k2PolyNagaoWide_Stab p (K.erase m) m) :
    k2PolyNagao_Gens p K L (k2PolyNagaoWide_sigma p K m L hmL) m hmL :=
  k2PolyNagaoWide_gens_of_check hmL hmK hLK hthird hJ
    (hR p K m L hmL hLK hmK him hthird hconst hSK hJ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_step_gens

/-- **The `|K|`-induction.**  The residual gives `Stab(K, L)` for every nonempty `K`. -/
theorem k2PolyNagaoWide_stab_all (hR : k2PolyNagaoWide_Statement) (n : ℕ) :
    ∀ (K : Finset I) (L : I), K.card = n → L ∉ K → K.Nonempty →
      (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
      (∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
        g ∈ K2 I (Polynomial (ZMod p)) → g = 1) →
      (∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1) →
      k2PolyNagaoWide_Stab p K L := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L hn hLK hK hthird hconst hSK
  obtain ⟨m, hmK⟩ := hK
  have hmL : m ≠ L := fun e => hLK (e ▸ hmK)
  by_cases hKm : ∀ i ∈ K, i = m
  · refine k2PolyNagaoWide_stab_of_gens hLK hmL hmK hthird
      (σ := k2PolyNagaoSigma_sigma p m L hmL) ?_
      (k2PolyNagaoSigma_gens_of_weyl hmL hmK hKm hthird
        (k2PolyNagaoWeyl_weylStatement p K m L hmL hmK hKm hthird hconst))
    rw [k2PolyNagaoSigma_sigma_unitVec]
    exact Subgroup.one_mem _
  · push Not at hKm
    obtain ⟨i, hi, him⟩ := hKm
    have hlt : (K.erase m).card < n := by
      rw [← hn]
      exact Finset.card_erase_lt_of_mem hmK
    have hJ : k2PolyNagaoWide_Stab p (K.erase m) m :=
      ih _ hlt (K.erase m) m rfl (Finset.notMem_erase m K)
        ⟨i, Finset.mem_erase.2 ⟨him, hi⟩⟩ hthird hconst
        (fun s hs hs2 => hSK s (k2PolyNagaoWide_S_erase_le K m hs) hs2)
    exact k2PolyNagaoWide_stab_of_gens hLK hmL hmK hthird
      (k2PolyNagaoWide_sigma_unitVec hmL hmK hLK)
      (k2PolyNagaoWide_step_gens hR hmL hLK hmK ⟨i, hi, him⟩ hthird hconst hSK hJ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_stab_all

/-- **Reduction.**  The residual gives `k2PolyNagaoSigma_WideStatement`. -/
theorem k2PolyNagaoWide_wide_of_statement (hR : k2PolyNagaoWide_Statement) :
    k2PolyNagaoSigma_WideStatement := by
  intro p _ I _ _ K L hLK hwide hthird hconst hSK
  obtain ⟨m, hmK, i, hi, hmi⟩ := hwide
  have hmL : m ≠ L := fun e => hLK (e ▸ hmK)
  have him : i ≠ m := fun e => hmi e.symm
  have hJ : k2PolyNagaoWide_Stab p (K.erase m) m :=
    k2PolyNagaoWide_stab_all hR _ (K.erase m) m rfl (Finset.notMem_erase m K)
      ⟨i, Finset.mem_erase.2 ⟨him, hi⟩⟩ hthird hconst
      (fun s hs hs2 => hSK s (k2PolyNagaoWide_S_erase_le K m hs) hs2)
  exact ⟨k2PolyNagaoWide_sigma p K m L hmL, k2PolyNagaoWide_sigma_unitVec hmL hmK hLK, m, hmL,
    hmK, k2PolyNagaoWide_step_gens hR hmL hLK hmK ⟨i, hi, him⟩ hthird hconst hSK hJ⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_wide_of_statement

/-- **Endpoint.**  The residual gives `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyNagaoWide_K2_bot_of_statement (hR : k2PolyNagaoWide_Statement) {p : ℕ}
    (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyNagaoWeyl_K2_bot_of_wide (k2PolyNagaoWide_wide_of_statement hR) hp hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_K2_bot_of_statement

end GroupApproximation.BooneHigman.Metabelian.ElemFP
