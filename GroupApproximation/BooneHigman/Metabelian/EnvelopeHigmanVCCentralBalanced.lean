import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCentralWords
import GroupApproximation.Meta.AxiomGuard

/-!
# All-swaps presentation, Step B: reduction to balanced letters (lane bh-met-77h)

Target of the lane: `HigmanVCCommonCentralStatement` (Step B).  A kernel element `r` of
`higmanVC_evalAll d` that is central modulo `K = normalClosure (higmanVC_rels d fun _ => True)`
is congruent modulo `K` to `higmanVCAll_iota C r'`, for one finite antichain `C`.

**NOT CLOSED.  The suggested combinatorial route is FALSE.**  The suggestion was: split every
letter, then refine all components into one antichain `C` so that each letter becomes a product
of letters of `C × C`.  This fails already for the two letters `(0, 1)` and `(00, 1)`, with
`d = 2`.

* Iterated splitting of `(u, v)` replaces it by `(u t, v t)`, where `t` runs over a finite
  complete prefix code `T`.
* The `v`-sides `1 T₁` and `1 T₂` lie in one antichain.  Since `T₁` and `T₂` are both complete,
  this forces `T₁ = T₂ = T`.
* Let `0ᵃ ∈ T` be the prefix of the stream `000…`.  Then `0 · 0ᵃ` and `00 · 0ᵃ` both lie in `C`.
  The first is a proper prefix of the second.

`scratchpad/bh-met-77h/check.py` confirms this by brute force up to depth 3.  Unbalanced letters
generate Thompson-`F`-like elements, which never preserve a single code.  So any real proof of
Step B needs a groupoid or normal-form argument across codes of different sizes, and this lane
does not supply one.

**Gap: `HigmanVCCentralBalancedStatement`.**  A central kernel element is congruent modulo `K` to
a product of *balanced* letters `(u, v)` with `|u| = |v|`.

* **Reduction (proved):** `higmanVCCentral_central_of_balanced`.  Take `M` at least every length
  in the product.  Each balanced letter splits `M - |u|` times into letters of the antichain of
  all words of length `M` (`EnvelopeHigmanVCCentralWords`).
* **It is equivalent to the target as a Prop, NOT strictly weaker**
  (`higmanVCCentral_balanced_of_ker_le`, with the empty product).  By the argument in
  `EnvelopeHigmanVCAllReduce`, no gap that yields (1) with nothing else supplied can be strictly
  weaker.
* **It is strictly smaller in proof content.**
  * Its conclusion names no antichain at all.
  * The passage from balanced letters to a single uniform antichain is discharged here.
  * What remains is the elimination of unbalanced letters, which is the Thompson-`F`-type part
    of the presentation.
* **Truth.** It is true if and only if (1) is true.  (1) is the standard presentation of `V_d`,
  and this lane believes it but did not verify it.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Gap (balanced form of Step B).**  A central kernel element is congruent modulo the relators
to a product of balanced letters `(u, v)`, `|u| = |v|`.  It is equivalent to the target as a
Prop, and strictly smaller in proof content; see the module docstring. -/
def HigmanVCCentralBalancedStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ r ∈ (higmanVC_evalAll d).ker,
    (∀ z : FreeGroup (List (Fin d) × List (Fin d)),
      r * z * r⁻¹ * z⁻¹ ∈ Subgroup.normalClosure (higmanVC_rels d fun _ => True)) →
    ∃ L : List (List (Fin d) × List (Fin d)), (∀ p ∈ L, p.1.length = p.2.length) ∧
      r * ((L.map FreeGroup.of).prod)⁻¹ ∈
        Subgroup.normalClosure (higmanVC_rels d fun _ => True)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCCentralBalancedStatement

/-- **Step B from the balanced gap.** -/
theorem higmanVCCentral_central_of_balanced (h : HigmanVCCentralBalancedStatement) :
    HigmanVCCommonCentralStatement := by
  intro d hd r hr hc
  obtain ⟨L, hL, hrL⟩ := h d hd r hr hc
  obtain ⟨M, hM⟩ := higmanVCCentral_exists_bound L
  obtain ⟨r', hr'⟩ := MonoidHom.mem_range.mp
    (higmanVCCentral_list_mem (M := M) L fun p hp => ⟨hL p hp, hM p hp⟩)
  refine ⟨higmanVCCentral_words d M, higmanVCCentral_words_antichain d M, r', ?_⟩
  refine higmanVCCommon_mk_eq_one_iff.mp ?_
  have h1 := higmanVCCommon_mk_eq_one_iff.mpr hrL
  rw [map_mul, map_inv, mul_inv_eq_one] at h1 ⊢
  rw [MonoidHom.comp_apply] at hr'
  rw [h1, hr']

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_central_of_balanced

/-- **The antichain gap of lane bh-met-77c from the balanced gap.** -/
theorem higmanVCCentral_antichain_of_balanced (h : HigmanVCCentralBalancedStatement) :
    HigmanVCAllAntichainStatement :=
  higmanVCCommon_antichain_of_central (higmanVCCentral_central_of_balanced h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_antichain_of_balanced

/-- **(1) from the balanced gap**: the standard relators present `V_d` on all ordered pairs. -/
theorem higmanVCCentral_ker_le_of_balanced (h : HigmanVCCentralBalancedStatement) (d : ℕ)
    (hd : 1 < d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  higmanVCCommon_ker_le_of_central (higmanVCCentral_central_of_balanced h) d hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_ker_le_of_balanced

/-- **The balanced gap from (1)** (the empty product): the gap is equivalent to (1), not
weaker. -/
theorem higmanVCCentral_balanced_of_ker_le
    (h : ∀ d : ℕ, 1 < d →
      (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True)) :
    HigmanVCCentralBalancedStatement := by
  intro d hd r hr _
  refine ⟨[], fun p hp => absurd hp List.not_mem_nil, ?_⟩
  rw [List.map_nil, List.prod_nil, inv_one, mul_one]
  exact h d hd hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCentral_balanced_of_ker_le

end GroupApproximation.BooneHigman.Metabelian.Envelope
