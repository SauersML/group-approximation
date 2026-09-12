import GroupApproximation.CharClass.OddPDescentDomino
import GroupApproximation.CharClass.OddPSign
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Nat.Prime.Factorial

/-!
# The descent, and the degree-one normalisation constant `λ₁ = ((p−1)/2)!`

The lane's deliverable.  Starting from the top word `A₀ = (δf)^{⊗p} = g^{⊗p}`, each round of
the descent takes the canonical primitive `H(A)` and multiplies by the differential of the
periodic resolution — by the norm `N` into even `W`-degrees, by `T − 1` into odd ones
(`OddPResolution.altCoeff`).  With `p` odd the starting `W`-index `p − 1` is even, so a
round is

```text
    eRound = (T − 1) ∘ H ∘ N ∘ H ,
```

and there are exactly `m = (p−1)/2` of them, ending at `W`-degree `0` in cochain degree `1`.

## The four statements

* `eD_eA` : every `A_k` is a `D`-cocycle;
* `eD_eY1`, `eD_eY2` : `H(A)` really is a primitive at each half-step;
* `eDescent_value` : **`λ₁ = ((p−1)/2)!`**, the coefficient of `g ⊗ f^{⊗(p−1)}` in the last
  term;
* `eDescent_value_isUnit` : the constant is a unit mod `p`.

## Where the characteristic is used, and where it is not

Only in **one** place: `eN (eA 0) = 0`.  The top word is `T`-invariant (its sign is
`(−1)^{p−1} = 1`, `OddPSign.neg_one_pow_mul_pred`), so `N` acts on it as multiplication by
`p`.  At every later level `A_{k+1}` is already in the image of `T − 1` and `N(T−1) = 0`
kills it over any ring.  **Over `ℤ` the descent's cocycle and primitive assertions are all
false while the value of the composite is the integer `m!` on the nose** — VERIFIED (model)
at `p = 3, 5, 7, 11` — so the two halves are stated separately, and `eDescent_value` carries
**no** characteristic hypothesis at all.

## How the value is computed

Not forwards.  The forward terms have no closed form (`sp-design`'s `p = 13` run has
supports `1, 12, 11, 100, 81, 288, 196, …`).  Instead `OddPDescentPairing.lean` gives the
adjoint of every operator, and against the pairing the descent runs **backwards** into the
sequence `X_k = ξ_0 ∧ ρ^k` of `OddPDescentDomino.lean`, whose top coefficient is `m!` by the
derivation identity `∂_i ρ^k = k ρ^{k−1}(ξ_{i+1} − ξ_{i−1})`.

## The evaluation, and its sign

`λ₁` is the value of the last term of the descent against the `p`-fold Alexander–Whitney
diagonal of the fundamental `1`-simplex, with `f` the barycentric coordinate of the vertex
`1` (so `f(0) = 0`, `f(1) = 1`).  Enumerating the cut sequences shows that diagonal has
exactly **one** term with no vertex-`0` factor, namely `([01], [1], …, [1])` (VERIFIED,
model, `p = 3, 5, 7`), so the evaluation reads off the coefficient of the single word
`g ⊗ f^{⊗(p−1)}` — `eHeadWord` below.  That word has degrees `(1, 0, …, 0)`, so the Koszul
evaluation sign `(−1)^{Σ_{i<j}|u_i||u_j|}` is `(−1)^0 = +1`, and `sp-steenrod`'s contract
("evaluation carries no sign", their §11a item 3) also gives `+1`: the two conventions agree
here and **no sign factor is owed**, `λ₁ = ((p−1)/2)!` exactly.  (The `(−1)^{(p−1)/2}` of
the programme note is `κ(1,1)`, the Cartan coefficient at the top corner, not a sign on
`c₁`; `sp-design`'s own table lists `c₁ = λ₁ = 1, 2, −1, −1, 5` at `p = 3, 5, 7, 11, 13`,
which is `((p−1)/2)!` mod `p` with no sign.)
-/

namespace GroupApproximation.CharClass

-- The `ℕ → Fin p` coercion is a SCOPED instance (`Fin.NatCast`), deliberately not
-- global; without this `open` the ascription `(n : Fin p)` reports a bare type
-- mismatch with no mention of a missing instance.
open Fin.NatCast

variable {p : ℕ} [NeZero p] (K : Type) [CommRing K]

/-! ## 1. The two distinguished words -/

/-- The top word `g^{⊗p} = (δf)^{⊗p}`, where the descent starts. -/
def eTopWord (p : ℕ) : EWord p := fun _ => true

noncomputable def eTop : EMod K p := Finsupp.single (eTopWord p) (1 : K)

/-- The word `g ⊗ f^{⊗(p−1)}`: the only one the Alexander–Whitney evaluation sees. -/
def eHeadWord (p : ℕ) [NeZero p] : EWord p := Function.update (eBotWord p) (0 : Fin p) true

omit [NeZero p] in
theorem eDeg_eTopWord : eDeg (eTopWord p) = p := by
  rw [eDeg]
  simp only [eTopWord, eLetterDeg_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

omit [NeZero p] in
theorem eD_eTop : eD K (eTop K) = (0 : EMod K p) := by
  rw [eTop, eD_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [eWedge_single, eWedgeGen_of_true K (show eTopWord p a = true from rfl)]

theorem eT_eTop (hodd : Odd p) : eT K (eTop K) = (eTop K : EMod K p) := by
  rw [eTop, eT_single]
  have hrot : eRot (eTopWord p) = eTopWord p := rfl
  have hsgn : eSgn K (eTopWord p) = (1 : K) := by
    rw [eSgn, eDeg_eTopWord]
    simp only [eTopWord, eLetterDeg_true, one_mul]
    rw [show p - 1 = 1 * (p - 1) from (one_mul _).symm]
    exact neg_one_pow_mul_pred hodd 1
  rw [hrot, hsgn, one_smul]

theorem eN_eTop (hodd : Odd p) (hchar : (p : K) = 0) : eN K (eTop K) = (0 : EMod K p) := by
  have hpow : ∀ k ∈ Finset.range p, ((eT K) ^ k) (eTop K) = (eTop K : EMod K p) :=
    fun k _ => eT_pow_apply_of_inv K k (eT_eTop K hodd)
  rw [eN, LinearMap.sum_apply, Finset.sum_congr rfl hpow, Finset.sum_const,
    Finset.card_range, ← Nat.cast_smul_eq_nsmul K, hchar, zero_smul]

/-! ## 2. The descent -/

/-- **One round of the descent**: the canonical primitive, the norm, the canonical
primitive again, then `T − 1`.  The two multipliers are `OddPResolution.altCoeff`'s, in the
order the starting `W`-index `p − 1` (even, since `p` is odd) dictates. -/
noncomputable def eRound : EMod K p →ₗ[K] EMod K p :=
  ((eT K - 1).comp (eH K)).comp ((eN K).comp (eH K))

/-- The term of the descent at `W`-degree `p − 1 − 2k`. -/
noncomputable def eA (k : ℕ) : EMod K p := ((eRound K) ^ k) (eTop K)

/-- The canonical primitive of `A k`. -/
noncomputable def eY1 (k : ℕ) : EMod K p := eH K (eA K k)

/-- The term of the descent at the intermediate (odd) `W`-degree. -/
noncomputable def eMid (k : ℕ) : EMod K p := eN K (eY1 K k)

/-- The canonical primitive of `eMid k`. -/
noncomputable def eY2 (k : ℕ) : EMod K p := eH K (eMid K k)

@[simp] theorem eA_zero : eA K 0 = (eTop K : EMod K p) := by
  rw [eA, pow_zero, Module.End.one_apply]

theorem eA_succ (k : ℕ) : eA (p := p) K (k + 1) = (eT K - 1) (eY2 K k) := by
  rw [eA, pow_succ', Module.End.mul_apply, ← eA]
  simp only [eRound, eY2, eMid, eY1, LinearMap.comp_apply]

/-! ### The cocycle and primitive statements (deliverable 2) -/

/-- `A_{k+1}` lies in the image of `T − 1`, so the norm kills it over any ring. -/
theorem eN_eA_succ (k : ℕ) : eN K (eA K (k + 1)) = (0 : EMod K p) := by
  rw [eA_succ]
  have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f (eY2 K k))
    (eN_mul_eT_sub_one K (p := p))
  simp only [Module.End.mul_apply, LinearMap.zero_apply] at h
  exact h

/-- **The norm kills every level.**  At level `0` this is where the characteristic is used,
and it is the only place in the lane. -/
theorem eN_eA (hodd : Odd p) (hchar : (p : K) = 0) (k : ℕ) :
    eN K (eA K k) = (0 : EMod K p) := by
  cases k with
  | zero => rw [eA_zero]; exact eN_eTop K hodd hchar
  | succ k => exact eN_eA_succ K k

/-- **Every term of the descent is a `D`-cocycle.** -/
theorem eD_eA (hp : 1 < p) (hodd : Odd p) (hchar : (p : K) = 0) (k : ℕ) :
    eD K (eA K k) = (0 : EMod K p) := by
  induction k with
  | zero => rw [eA_zero]; exact eD_eTop K
  | succ k ih =>
      -- every `have` whose type names no `EMod K p` must name `p`, or `NeZero ?p` is stuck
      have hY1 : eD K (eY1 (p := p) K k) = eA K k := by
        have h := eD_eH_add K (eA (p := p) K k)
        rw [ih, map_zero, add_zero] at h
        exact h
      have hMid : eD K (eMid K k) = (0 : EMod K p) := by
        have hcomm := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f (eY1 K k))
          (eN_comp_eD K hp)
        simp only [LinearMap.comp_apply] at hcomm
        rw [eMid, ← hcomm, hY1, eN_eA K hodd hchar k]
      have hY2 : eD K (eY2 (p := p) K k) = eMid K k := by
        have h := eD_eH_add K (eMid (p := p) K k)
        rw [hMid, map_zero, add_zero] at h
        exact h
      have hcommT := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f (eY2 K k))
        (eT_comp_eD K hp)
      simp only [LinearMap.comp_apply] at hcommT
      rw [eA_succ, LinearMap.sub_apply, Module.End.one_apply, map_sub, ← hcommT, hY2, eMid,
        eT_eN_apply, sub_self]

/-- **`H(A)` is a primitive**: the first half-step of each round. -/
theorem eD_eY1 (hp : 1 < p) (hodd : Odd p) (hchar : (p : K) = 0) (k : ℕ) :
    eD K (eY1 (p := p) K k) = eA K k := by
  have h := eD_eH_add K (eA (p := p) K k)
  rw [eD_eA K hp hodd hchar k, map_zero, add_zero] at h
  exact h

theorem eD_eMid (hp : 1 < p) (hodd : Odd p) (hchar : (p : K) = 0) (k : ℕ) :
    eD K (eMid K k) = (0 : EMod K p) := by
  have hcomm := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f (eY1 K k)) (eN_comp_eD K hp)
  simp only [LinearMap.comp_apply] at hcomm
  rw [eMid, ← hcomm, eD_eY1 K hp hodd hchar k, eN_eA K hodd hchar k]

/-- **`H(eMid)` is a primitive**: the second half-step of each round. -/
theorem eD_eY2 (hp : 1 < p) (hodd : Odd p) (hchar : (p : K) = 0) (k : ℕ) :
    eD K (eY2 (p := p) K k) = eMid K k := by
  have h := eD_eH_add K (eMid (p := p) K k)
  rw [eD_eMid K hp hodd hchar k, map_zero, add_zero] at h
  exact h

/-! ## 3. The dual sequence and the pairing -/

/-- `ξ_0 ∧ ρ^k`, the sequence the descent becomes when read against the pairing. -/
noncomputable def eX (k : ℕ) : EMod K p := eWedge K 0 (((eR K) ^ k) (eBot K))

/-- The adjoint of one round. -/
noncomputable def eRoundStar : EMod K p →ₗ[K] EMod K p :=
  ((eWedge K 0).comp (eN K)).comp ((eWedge K 0).comp ((eT K) ^ (p - 1) - 1))

theorem eAdj_eRound : eAdj K (eRound K) (eRoundStar K : EMod K p →ₗ[K] EMod K p) := by
  have hH : eAdj K (eH K) (eWedge K (0 : Fin p)) := eAdj_ePart_eWedge K 0
  have hS : eAdj K (eT K - 1) (((eT K) ^ (p - 1) - 1 : EMod K p →ₗ[K] EMod K p)) := by
    have h := eAdj_sub K (eAdj_eT K) (eAdj_id K (p := p))
    rw [show (LinearMap.id : EMod K p →ₗ[K] EMod K p) = 1 from rfl] at h
    exact h
  exact eAdj_comp K (eAdj_comp K hS hH) (eAdj_comp K (eAdj_eN K) hH)

/-- `p − 1` reduces to `−1` in `Fin p`. -/
theorem eCast_pred : ((p - 1 : ℕ) : Fin p) = -1 := by
  have hp1 : (p - 1 : ℕ) + 1 = p := by
    have := NeZero.ne p
    omega
  have h2 : ((p - 1 : ℕ) : Fin p) + 1 = 0 := by
    have hc : ((((p - 1 : ℕ) + 1 : ℕ)) : Fin p) = ((p : ℕ) : Fin p) := by rw [hp1]
    rw [Nat.cast_add, Nat.cast_one, Fin.natCast_self] at hc
    exact hc
  -- not `simpa`: `a + b = 0 → a = -b` directly, with no simp set to guess at
  exact eq_neg_of_add_eq_zero_left h2

/-- **The dual recursion.**  `T^{-1}` moves `ξ_0` to `ξ_1`, the `−1` half dies against a
repeated `ξ_0`, and the norm sweeps the pair `(0,1)` over every cyclically adjacent pair. -/
theorem eX_succ (hp : 1 < p) (k : ℕ) :
    eX (p := p) K (k + 1) = eRoundStar K (eX K k) := by
  have hZinv : eT K (((eR K) ^ k) (eBot K)) = ((eR K) ^ k) (eBot K) :=
    eT_eR_pow_eBot K hp k
  have hTZ : ((eT K) ^ (p - 1)) (((eR K) ^ k) (eBot K)) = ((eR K) ^ k) (eBot K) :=
    eT_pow_apply_of_inv K (p - 1) hZinv
  have hshift : ((eT (p := p) K) ^ (p - 1)) (eWedge K 0 (((eR K) ^ k) (eBot K)))
      = eWedge K 1 (((eR K) ^ k) (eBot K)) := by
    have hidx : (0 : Fin p) - (-1 : Fin p) = 1 := by abel
    rw [eT_pow_eWedge K hp (p - 1) 0 (((eR K) ^ k) (eBot K)), hTZ, eCast_pred, hidx]
  have hzero : eWedge K (0 : Fin p) (eWedge K (0 : Fin p) (((eR K) ^ k) (eBot K))) = 0 := by
    have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f (((eR K) ^ k) (eBot K)))
      (eWedge_eWedge_self K (0 : Fin p))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
    exact h
  have hRHS : eRoundStar (p := p) K (eX K k)
      = eWedge K 0 (eN K (eWedge K 0 (eWedge K 1 (((eR K) ^ k) (eBot K))))) := by
    simp only [eRoundStar, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, eX]
    rw [map_sub, hshift, hzero, sub_zero]
  -- name the factors: a bare `← Module.End.mul_apply` folds the outer `eWedge K 0 (…)`
  rw [hRHS, eN_eWedge_zero_one K hp hZinv, eX,
    ← Module.End.mul_apply (eR K) (eR K ^ k) (eBot K), ← pow_succ']

theorem ePair_eRound_pow (hp : 1 < p) (j : ℕ) (x : EMod K p) (k : ℕ) :
    ePair K (((eRound K) ^ j) x) (eX K k) = ePair K x (eX K (j + k)) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
      have harith : j + (k + 1) = j + 1 + k := by omega
      rw [pow_succ', Module.End.mul_apply,
        eAdj_eRound K ((eRound K ^ j) x) (eX K k), ← eX_succ K hp, ih (k + 1), harith]

/-! ## 4. The value -/

theorem eX_zero : eX K 0 = Finsupp.single (eHeadWord p) (1 : K) := by
  rw [eX, pow_zero, Module.End.one_apply, eBot, eWedge_single,
    eWedgeGen_of_false K (show eBotWord p (0 : Fin p) = false from rfl),
    ePre_zero_of_card, pow_zero, one_smul, eHeadWord]

theorem eTopWord_update_zero (hp : 1 < p) :
    Function.update (eTopWord p) (0 : Fin p) false = eIntervalWord (p := p) 1 (p - 1) := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [Function.update_self]
    symm
    -- not `simp only`: its default simprocs fold `1 ≤ 0` and can leave `omega` nothing to do
    exact Bool.eq_false_of_not_eq_true (by rw [eIntervalWord_apply, Fin.val_zero]; omega)
  · rw [Function.update_of_ne hj]
    have hjv : 1 ≤ (j : ℕ) := by
      rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
      · exact absurd (Fin.ext (by rw [h, Fin.val_zero])) hj
      · exact h
    have hjlt := j.isLt
    symm
    simp only [eIntervalWord, eTopWord, decide_eq_true_eq]
    omega

/-- **The evaluation obligation, as a named `Prop`.**  `λ₁` is by definition the value of
the last term of the descent against the `p`-fold Alexander–Whitney diagonal of `ι₁`.  This
says that that evaluation functional is the coefficient of `eHeadWord` — equivalently, that
the diagonal has exactly one term with no vertex-`0` factor and that the Koszul evaluation
sign there is `+1`.

Discharged by `sp-steenrod` once `tupEval` and the iterated Alexander–Whitney diagonal exist
in the tuple model; VERIFIED (model) here at `p = 3, 5, 7` by enumerating every cut
sequence.  It is **stated, not used**: `eDescent_value` below is the coefficient statement
itself, so no theorem of this lane rests on it.  Building the diagonal here would import the
whole vendored cochain tower for one linear functional. -/
def EvalIsHeadCoeff (ev : EMod K p → K) : Prop := ∀ x : EMod K p, ev x = x (eHeadWord p)

/-- **`λ₁ = ((p−1)/2)!`.**  The coefficient of `g ⊗ f^{⊗(p−1)}` in the last term of the
descent, generic in the odd prime `p`, over an arbitrary commutative ring. -/
theorem eDescent_value (m : ℕ) (hm : p = 2 * m + 1) (hp : 1 < p) :
    (eA K m) (eHeadWord p) = (Nat.factorial m : K) := by
  have hstart : (eA (p := p) K m) (eHeadWord p) = ePair K (eA (p := p) K m) (eX K 0) := by
    rw [eX_zero, ePair_single_right]
  rw [hstart, eA, ePair_eRound_pow K hp m (eTop K) 0, Nat.add_zero, eTop,
    ePair_single_left, eX,
    eWedge_coeff_of_true K (0 : Fin p) _ _ (show eTopWord p (0 : Fin p) = true from rfl),
    ePre_zero_of_card, pow_zero, one_mul, eTopWord_update_zero hp,
    show p - 1 = 2 * m from by omega]
  exact eR_pow_interval K hp m 1 le_rfl (by omega)

omit [NeZero p] in
/-- **The constant is a unit.**  `((p−1)/2)!` is a product of integers below `p`, so a prime
`p` does not divide it. -/
theorem eDescent_value_isUnit (m : ℕ) (hprime : p.Prime) (hm : p = 2 * m + 1) :
    IsUnit ((Nat.factorial m : ZMod p)) := by
  -- through `ZMod.unitOfCoprime`, so no `Field (ZMod p)` instance (`Mathlib.Algebra.Field.ZMod`)
  -- has to be in the import closure
  have hndvd : ¬ p ∣ Nat.factorial m := by
    rw [Nat.Prime.dvd_factorial hprime]
    omega
  have hcop : Nat.Coprime (Nat.factorial m) p := (hprime.coprime_iff_not_dvd.2 hndvd).symm
  exact ⟨ZMod.unitOfCoprime _ hcop, ZMod.coe_unitOfCoprime _ hcop⟩

/-- **The constant, read off through any evaluation satisfying the obligation.** -/
theorem eDescent_value_of_eval (ev : EMod K p → K) (hev : EvalIsHeadCoeff K ev)
    (m : ℕ) (hm : p = 2 * m + 1) (hp : 1 < p) :
    ev (eA K m) = (Nat.factorial m : K) := by
  -- `EvalIsHeadCoeff` is a plain `def`: apply it before rewriting with it
  rw [hev (eA K m), eDescent_value K m hm hp]

/-- **The descent's constant, at the ring where it is used.** -/
theorem eDescent_value_zmod (m : ℕ) (hprime : p.Prime) (hm : p = 2 * m + 1) :
    (eA (ZMod p) m) (eHeadWord p) = (Nat.factorial m : ZMod p)
      ∧ IsUnit ((Nat.factorial m : ZMod p)) :=
  ⟨eDescent_value (ZMod p) m hm hprime.one_lt, eDescent_value_isUnit m hprime hm⟩

/-- **The degree-one normalisation constant of the odd-primary construction, closed.**

For every odd prime `q = 2m + 1`, over `F_q`: the descent runs at **every** level (every `A_k`
is a `D`-cocycle, and both half-steps `H(A_k)` and `H(N(H(A_k)))` are primitives), its last
term has head coefficient `λ₁ = m! = ((q−1)/2)!`, and that constant is a unit of `F_q`.  This
is `c₁` of `sp-steenrod`'s report §12, derived rather than cited.

The quantifiers are inside the proposition, so `#audit_closed_axioms` reads a constant, not a
bare `∀`. -/
def PrintedOddPDescentConstant : Prop :=
  ∀ (q m : ℕ) [NeZero q], q.Prime → q = 2 * m + 1 →
    (∀ k : ℕ, eD (ZMod q) (eA (ZMod q) (p := q) k) = 0
        ∧ eD (ZMod q) (eY1 (ZMod q) (p := q) k) = eA (ZMod q) k
        ∧ eD (ZMod q) (eY2 (ZMod q) (p := q) k) = eMid (ZMod q) k)
      ∧ (eA (ZMod q) (p := q) m) (eHeadWord q) = (Nat.factorial m : ZMod q)
      ∧ IsUnit (Nat.factorial m : ZMod q)

theorem printedOddPDescentConstant : PrintedOddPDescentConstant := by
  intro q m _ hprime hm
  have hp : 1 < q := hprime.one_lt
  have hodd : Odd q := ⟨m, hm⟩
  have hchar : (q : ZMod q) = 0 := ZMod.natCast_self q
  exact ⟨fun k => ⟨eD_eA (ZMod q) hp hodd hchar k, eD_eY1 (ZMod q) hp hodd hchar k,
    eD_eY2 (ZMod q) hp hodd hchar k⟩, eDescent_value (ZMod q) m hm hp,
    eDescent_value_isUnit m hprime hm⟩

/-! ## 5. The axiom closure

Audited on every build: `#audit_axioms` prints the closure **and fails the build** if it
leaves the classical allowlist `[propext, Classical.choice, Quot.sound]`, which
`#print axioms` does not. -/

#audit_axioms eDescent_value
#audit_axioms eDescent_value_isUnit
#audit_axioms eDescent_value_zmod
#audit_axioms eD_eA
#audit_axioms eD_eY1
#audit_axioms eD_eY2
#audit_axioms eD_comp_eH_add
#audit_axioms eD_comp_eD
#audit_closed_axioms printedOddPDescentConstant

end GroupApproximation.CharClass
