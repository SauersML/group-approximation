import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFWit
import GroupApproximation.Meta.AxiomGuard

/-!
# The double-coset normal form: construction and converse (lane bh-met-77n)

Notation as in `EnvelopeHigmanVCTreeNFWit`.

**Proved here, with no hypotheses.**
* The `E`-double-coset relation `higmanVCTreeNFWit_dc` is an equivalence relation.
* `higmanVCTreeNFWit_tau` is the canonical normal form: `1` on the trivial class `E(U)`, and a
  quotient representative on every other class.
* `higmanVCTreeNFWit_tau_isNF`: it satisfies (0), (i) and (ii).
* `higmanVCTreeNFWit_of_pivot`: pivot closure (iii) of this `τ` alone gives
  `HigmanVCTreeNFWitStatement`.  So **the whole residual content is (iii)**, for one canonical
  map.

**LOUD converse.**
* `higmanVCTreeNFWit_of_ker_le`: (1) gives the Statement.  Under (1), `E` is injective and every
  `τ q * u * t` is `β⁻¹ τ(τ q * u * t) β'⁻¹`.
* `higmanVCTreeNFWit_iff_ker_le` and `higmanVCTreeNFWit_iff_schreier`: the Statement is
  **equivalent to (1), and to `HigmanVCTreeNFSchreierStatement`, as a Prop**.  It is not
  strictly weaker as a Prop; it is smaller in proof content.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

theorem higmanVCTreeNFWit_dc_refl (d : ℕ) (q : higmanVCCommon_Q d) :
    higmanVCTreeNFWit_dc d q q :=
  higmanVCTreeNFWit_dc_iff.mpr ⟨1, (higmanVCTreeNF_U d).one_mem, 1, (higmanVCTreeNF_U d).one_mem,
    by rw [map_one, one_mul, mul_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_dc_refl

theorem higmanVCTreeNFWit_dc_symm {d : ℕ} {q q' : higmanVCCommon_Q d}
    (h : higmanVCTreeNFWit_dc d q q') : higmanVCTreeNFWit_dc d q' q := by
  obtain ⟨β, hβ, β', hβ', e⟩ := higmanVCTreeNFWit_dc_iff.mp h
  refine higmanVCTreeNFWit_dc_iff.mpr
    ⟨β⁻¹, (higmanVCTreeNF_U d).inv_mem hβ, β'⁻¹, (higmanVCTreeNF_U d).inv_mem hβ', ?_⟩
  rw [map_inv, map_inv, e]
  simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_dc_symm

theorem higmanVCTreeNFWit_dc_trans {d : ℕ} {q q' q'' : higmanVCCommon_Q d}
    (h : higmanVCTreeNFWit_dc d q q') (h' : higmanVCTreeNFWit_dc d q' q'') :
    higmanVCTreeNFWit_dc d q q'' := by
  obtain ⟨β, hβ, β', hβ', e⟩ := higmanVCTreeNFWit_dc_iff.mp h
  obtain ⟨γ, hγ, γ', hγ', e'⟩ := higmanVCTreeNFWit_dc_iff.mp h'
  refine higmanVCTreeNFWit_dc_iff.mpr ⟨γ * β, (higmanVCTreeNF_U d).mul_mem hγ hβ, β' * γ',
    (higmanVCTreeNF_U d).mul_mem hβ' hγ', ?_⟩
  rw [e', e]
  simp only [map_mul, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_dc_trans

/-- The `E`-double-coset relation, as a setoid on `Q`. -/
def higmanVCTreeNFWit_setoid (d : ℕ) : Setoid (higmanVCCommon_Q d) where
  r := higmanVCTreeNFWit_dc d
  iseqv := ⟨higmanVCTreeNFWit_dc_refl d, higmanVCTreeNFWit_dc_symm, higmanVCTreeNFWit_dc_trans⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_setoid

/-- `q` lies in the trivial class: `E q ∈ E(U)`. -/
def higmanVCTreeNFWit_triv (d : ℕ) (q : higmanVCCommon_Q d) : Prop :=
  ∃ β ∈ higmanVCTreeNF_U d, higmanVCTreeNF_E d q = higmanVCTreeNF_E d β

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_triv

theorem higmanVCTreeNFWit_triv_iff {d : ℕ} {q : higmanVCCommon_Q d} :
    higmanVCTreeNFWit_triv d q ↔
      ∃ β ∈ higmanVCTreeNF_U d, higmanVCTreeNF_E d q = higmanVCTreeNF_E d β :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_triv_iff

theorem higmanVCTreeNFWit_triv_of_dc {d : ℕ} {q q' : higmanVCCommon_Q d}
    (hq : higmanVCTreeNFWit_triv d q) (h : higmanVCTreeNFWit_dc d q q') :
    higmanVCTreeNFWit_triv d q' := by
  obtain ⟨β₀, hβ₀, e₀⟩ := higmanVCTreeNFWit_triv_iff.mp hq
  obtain ⟨β, hβ, β', hβ', e⟩ := higmanVCTreeNFWit_dc_iff.mp h
  refine higmanVCTreeNFWit_triv_iff.mpr
    ⟨β * β₀ * β', (higmanVCTreeNF_U d).mul_mem ((higmanVCTreeNF_U d).mul_mem hβ hβ₀) hβ', ?_⟩
  rw [e, e₀]
  simp only [map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_triv_of_dc

open Classical in
/-- **The canonical double-coset normal form**: `1` on the trivial class, otherwise the chosen
representative of the `E`-double coset. -/
noncomputable def higmanVCTreeNFWit_tau (d : ℕ) (q : higmanVCCommon_Q d) : higmanVCCommon_Q d :=
  if higmanVCTreeNFWit_triv d q then 1 else (Quotient.mk (higmanVCTreeNFWit_setoid d) q).out

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_tau

/-- (0): `τ` is constant on `E`-double cosets. -/
theorem higmanVCTreeNFWit_tau_const {d : ℕ} {q q' : higmanVCCommon_Q d}
    (h : higmanVCTreeNFWit_dc d q q') : higmanVCTreeNFWit_tau d q' = higmanVCTreeNFWit_tau d q := by
  unfold higmanVCTreeNFWit_tau
  by_cases hq : higmanVCTreeNFWit_triv d q
  · rw [if_pos hq, if_pos (higmanVCTreeNFWit_triv_of_dc hq h)]
  · have hq' : ¬ higmanVCTreeNFWit_triv d q' := fun h' =>
      hq (higmanVCTreeNFWit_triv_of_dc h' (higmanVCTreeNFWit_dc_symm h))
    rw [if_neg hq, if_neg hq']
    have e : Quotient.mk (higmanVCTreeNFWit_setoid d) q' =
        Quotient.mk (higmanVCTreeNFWit_setoid d) q :=
      Quotient.sound (higmanVCTreeNFWit_dc_symm h)
    rw [e]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_tau_const

/-- (i): `τ q` lies in the `E`-double coset of `q`. -/
theorem higmanVCTreeNFWit_tau_dc (d : ℕ) (q : higmanVCCommon_Q d) :
    higmanVCTreeNFWit_dc d q (higmanVCTreeNFWit_tau d q) := by
  unfold higmanVCTreeNFWit_tau
  by_cases hq : higmanVCTreeNFWit_triv d q
  · rw [if_pos hq]
    obtain ⟨β, hβ, e⟩ := higmanVCTreeNFWit_triv_iff.mp hq
    refine higmanVCTreeNFWit_dc_iff.mpr
      ⟨β⁻¹, (higmanVCTreeNF_U d).inv_mem hβ, 1, (higmanVCTreeNF_U d).one_mem, ?_⟩
    rw [map_one, mul_one, e, map_inv, inv_mul_cancel]
  · rw [if_neg hq]
    have h1 : higmanVCTreeNFWit_dc d (Quotient.mk (higmanVCTreeNFWit_setoid d) q).out q :=
      Quotient.mk_out (s := higmanVCTreeNFWit_setoid d) q
    exact higmanVCTreeNFWit_dc_symm h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_tau_dc

/-- (ii): `τ` is `1`, hence in `U`, on the trivial class. -/
theorem higmanVCTreeNFWit_tau_mem {d : ℕ} {q β : higmanVCCommon_Q d}
    (hβ : β ∈ higmanVCTreeNF_U d) (e : higmanVCTreeNF_E d q = higmanVCTreeNF_E d β) :
    higmanVCTreeNFWit_tau d q ∈ higmanVCTreeNF_U d := by
  unfold higmanVCTreeNFWit_tau
  rw [if_pos (higmanVCTreeNFWit_triv_iff.mpr ⟨β, hβ, e⟩)]
  exact (higmanVCTreeNF_U d).one_mem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_tau_mem

/-- **(0)–(ii) hold unconditionally** for the canonical `τ`. -/
theorem higmanVCTreeNFWit_tau_isNF (d : ℕ) :
    higmanVCTreeNFWit_IsNF d (higmanVCTreeNFWit_tau d) := by
  unfold higmanVCTreeNFWit_IsNF
  exact ⟨fun _ _ h => higmanVCTreeNFWit_tau_const h, higmanVCTreeNFWit_tau_dc d,
    fun _ _ hβ e => higmanVCTreeNFWit_tau_mem hβ e⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_tau_isNF

/-- **The residual content is (iii) alone**: pivot closure of the canonical `τ` gives the
Statement. -/
theorem higmanVCTreeNFWit_of_pivot
    (h : ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d),
      a.length = n ∧ b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧
      higmanVCTreeNFWit_PivotClosed d (higmanVCTreeNFWit_tau d)
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))) :
    HigmanVCTreeNFWitStatement := by
  intro d hd N
  obtain ⟨n, hN, a, b, ha, hb, hab, hba, ht⟩ := h d hd N
  exact ⟨n, hN, a, b, ha, hb, hab, hba, higmanVCTreeNFWit_tau d, higmanVCTreeNFWit_tau_isNF d, ht⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_of_pivot

/-- Under (1) at `d`, the canonical `τ` is pivot-closed for every `t`. -/
theorem higmanVCTreeNFWit_pivot_of_ker_le {d : ℕ}
    (h : (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True))
    (t : higmanVCCommon_Q d) :
    higmanVCTreeNFWit_PivotClosed d (higmanVCTreeNFWit_tau d) t := by
  unfold higmanVCTreeNFWit_PivotClosed
  intro q u _
  obtain ⟨β, hβ, β', hβ', e⟩ := higmanVCTreeNFWit_dc_iff.mp
    (higmanVCTreeNFWit_tau_dc d (higmanVCTreeNFWit_tau d q * u * t))
  have e' : higmanVCTreeNFWit_tau d (higmanVCTreeNFWit_tau d q * u * t) =
      β * (higmanVCTreeNFWit_tau d q * u * t) * β' :=
    higmanVCTreeNF_E_injective_of_ker_le h (by rw [e]; simp only [map_mul])
  refine ⟨β⁻¹, (higmanVCTreeNF_U d).inv_mem hβ, higmanVCTreeNFWit_tau d q * u * t, β'⁻¹,
    (higmanVCTreeNF_U d).inv_mem hβ', ?_⟩
  rw [e']
  simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_pivot_of_ker_le

/-- **LOUD converse:** (1) gives the double-coset Statement. -/
theorem higmanVCTreeNFWit_of_ker_le
    (h : ∀ d : ℕ, 1 < d →
      (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True)) :
    HigmanVCTreeNFWitStatement := by
  refine higmanVCTreeNFWit_of_pivot fun d hd N => ?_
  obtain ⟨n, hN, a, b, ha, hb, hab, hba, -⟩ := higmanVCTreeLevel_level_of_ker_le h d hd N
  exact ⟨n, hN, a, b, ha, hb, hab, hba, higmanVCTreeNFWit_pivot_of_ker_le (h d hd) _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_of_ker_le

/-- **LOUD equivalence** with (1). -/
theorem higmanVCTreeNFWit_iff_ker_le :
    HigmanVCTreeNFWitStatement ↔ ∀ d : ℕ, 1 < d →
      (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  ⟨higmanVCTreeNFWit_ker_le_of_dc, higmanVCTreeNFWit_of_ker_le⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_iff_ker_le

/-- **LOUD equivalence** with the Schreier gap of lane bh-met-77l. -/
theorem higmanVCTreeNFWit_iff_schreier :
    HigmanVCTreeNFWitStatement ↔ HigmanVCTreeNFSchreierStatement :=
  ⟨higmanVCTreeNFWit_schreier_of_dc,
    fun h => higmanVCTreeNFWit_of_ker_le (higmanVCTreeNF_ker_le_of_schreier h)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWit_iff_schreier

end GroupApproximation.BooneHigman.Metabelian.Envelope
