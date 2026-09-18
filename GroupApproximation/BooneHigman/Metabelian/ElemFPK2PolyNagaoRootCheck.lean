import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoRootOrbit
import GroupApproximation.Meta.AxiomGuard

/-!
# The root check of the wide section, part 2: the supported case

Lane `bh-met-93v`.  Notation of `ElemFPK2PolyNagaoWideSigma`; `σ₀ = k2PolyNagaoSigma_sigma`,
`σ(v) = q_v σ₀(r_v)` (`k2PolyNagaoWide_sigma`), `y = x_mL(1)`.

* `k2PolyNagaoRoot_Q_mono`: `Q_{{m}} ≤ Q_K` for `m ∈ K`.
* `k2PolyNagaoRoot_rank_one`: `σ₀(y v)⁻¹ y σ₀(v) ∈ Q_K` for every supported `v` of the
  `G_K`-orbit (the rank-one Weyl check of lane 93d at `K = {m}`, via `_orbit_one`).
* `k2PolyNagaoRoot_Q_L`: for `q ∈ Q` and supported `r`, `(q r)_L = r_L + d r_m`.
* `k2PolyNagaoRoot_shift`: if moreover `q r` is supported with `(q r)_m = r_m`, then
  `q r = x_Lm(d) r` and `σ₀(q r)⁻¹ q σ₀(r) ∈ Q` (the `x_Lm` check and the core check).
* `k2PolyNagaoRoot_check_supp`: hence the check of `σ` at `y` holds at every supported orbit
  vector `v` whose representatives `r_v`, `r_{yv}` keep the `m`-coordinate.
* `k2PolyNagaoRoot_m_unit`, `_rep_m`: `(q r)_m = c r_m` with `c` a unit; so when
  `(ZMod p)ˣ` is trivial (`p = 2`), the representatives always keep the `m`-coordinate.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_mul
  act_x_apply unitVec unitVec_apply rootSpan_mono exists_split act_eq_self_of_rootSpan
  act_apply_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- `Q_{{m}} ≤ Q_K` for `m ∈ K`. -/
theorem k2PolyNagaoRoot_Q_mono {K : Finset I} {m L : I} (hmK : m ∈ K)
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyNF_Q p {m} L) :
    g ∈ k2PolyNF_Q p K L := by
  have hpq : ∀ i j : I, i ≠ j → (i ∈ insert L ({m} : Finset I) ∧ j ∈ ({m} : Finset I)) →
      (i ∈ insert L K ∧ j ∈ K) := fun i j _ hij => by
    refine ⟨?_, by rw [Finset.mem_singleton.1 hij.2]; exact hmK⟩
    rcases Finset.mem_insert.1 hij.1 with h | h
    · rw [h]; exact Finset.mem_insert_self L K
    · rw [Finset.mem_singleton.1 h]; exact Finset.mem_insert_of_mem hmK
  exact k2PolyNagaoWide_Qr_le_Q K L (rootSpan_mono
    (p := fun i j => i ∈ insert L ({m} : Finset I) ∧ j ∈ ({m} : Finset I))
    (q := fun i j => i ∈ insert L K ∧ j ∈ K) hpq (k2PolyNagaoWide_Q_le_Qr {m} L hg))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_Q_mono

/-- **The rank-one check.**  `σ₀(y v)⁻¹ y σ₀(v) ∈ Q_K` for every orbit vector `v` supported on
`{m, L}` (lane 93d's rank-one checks at `K = {m}`, transported by `_orbit_one`, `_Q_mono`). -/
theorem k2PolyNagaoRoot_rank_one {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    {v : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L v)
    (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) :
    (k2PolyNagaoSigma_sigma p m L hmL (act (x m L hmL (1 : Polynomial (ZMod p))) v))⁻¹ *
        x m L hmL (1 : Polynomial (ZMod p)) * k2PolyNagaoSigma_sigma p m L hmL v ∈
      k2PolyNF_Q p K L := by
  have hKm : ∀ i ∈ ({m} : Finset I), i = m := fun _ hi => Finset.mem_singleton.1 hi
  have hG := k2PolyNagaoSigma_gens_of_weyl hmL (Finset.mem_singleton_self m) hKm hthird
    (k2PolyNagaoWeyl_weylStatement p ({m} : Finset I) m L hmL (Finset.mem_singleton_self m)
      hKm hthird hconst)
  obtain ⟨-, hxmL, -⟩ := hG
  exact k2PolyNagaoRoot_Q_mono hmK (hxmL v (k2PolyNagaoRoot_orbit_one hmL hr hv))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_rank_one

/-- For `q ∈ Q` and `r` supported on `{m, L}`: `(q r)_L = r_L + d r_m` (write `q = s x_Lm(d) v'`
with `s ∈ S_K` fixing the `L`-row and `v'` fixing `r`). -/
theorem k2PolyNagaoRoot_Q_L {K : Finset I} {m L : I} (hmL : m ≠ L) (hLK : L ∉ K)
    {q : SteinbergGroup I (Polynomial (ZMod p))} (hq : q ∈ k2PolyNF_Q p K L)
    {r : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L r) :
    ∃ d : Polynomial (ZMod p), act q r L = r L + d * r m := by
  have hLe : ∀ j : I, j ∈ K → j ≠ L := fun j hj e => hLK (by rw [← e]; exact hj)
  obtain ⟨s, hs, v, hv, rfl⟩ := k2PolyDeg_SV_decomp hLK hq
  have hsplit : ∀ i j : I, i ≠ j → (i = L ∧ j ∈ K) →
      (i = L ∧ j = m) ∨ (i = L ∧ j ∈ K.erase m) := fun i j _ hij => by
    by_cases hjm : j = m
    · exact Or.inl ⟨hij.1, hjm⟩
    · exact Or.inr ⟨hij.1, Finset.mem_erase.2 ⟨hjm, hij.2⟩⟩
  have hcomm : ∀ (i j : I) (hij : i ≠ j) (a b : Polynomial (ZMod p)),
      (i = L ∧ j ∈ K.erase m) → Commute (x L m hmL.symm b) (x i j hij a) :=
    fun i j hij a b hq => x_commute_of_ne L m i j hmL.symm hij (fun e => hmL (e.trans hq.1))
      (hLe j (Finset.mem_of_mem_erase hq.2)) b a
  obtain ⟨d, v', hv', rfl⟩ := exists_split (p := fun i j => i = L ∧ j ∈ K)
    (q := fun i j => i = L ∧ j ∈ K.erase m) hmL.symm hsplit hcomm hv
  have hv'r : act v' r = r :=
    act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ K.erase m)
      (fun _ j hq => hr j (Finset.ne_of_mem_erase hq.2) (hLe j (Finset.mem_of_mem_erase hq.2)))
      hv'
  have hsL : ∀ u : I → Polynomial (ZMod p), act s u L = u L :=
    act_apply_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (fun i _ hq => hLe i hq.1) hs
  refine ⟨d, ?_⟩
  rw [act_mul, act_mul, hv'r, hsL, act_x_apply, if_pos rfl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_Q_L
