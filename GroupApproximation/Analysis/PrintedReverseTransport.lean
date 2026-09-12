import GroupApproximation.Analysis.OmegaConjugationOperators

/-!
# The printed reverse step of `cor:generaltransport`

`non_mf_group_notes.tex`, the proof of
`\begin{corollary}[one-sided conjugators preserve the commutant under
conjugation and inverse conjugation]` (`\label{cor:generaltransport}`), reads:

> For a one-sided conjugator `s`, Theorem 3.1 gives the conclusion for
> `V_{g,n} x_n V_{g,n}^*`, and the equality `P = VPV^*` established in its proof
> gives `V^*PV = P`, hence `V^* Fix = Fix` and the conclusion for
> `V_{g,n}^* x_n V_{g,n}`.

Proof-ledger row `ID.06` records that Lean does something different in kind
here: `KazhdanAsymptoticCommutant.transport_star` reverses the *approximate*
leakage bound `one_sub_moved_mul_corner_vanishing`, at the finite stage.  The
printed reverse step is not an estimate at all — it is an exact identity
between projections, and it needs neither a norm, nor completeness, nor
finiteness, nor property (T).  Once `P = VPV^*` has been established (which is
where finiteness of the norm ultraproduct is spent, in KT.10), reversing it is
three lines of star-ring algebra.

That is what this file supplies, in the same bare `Ring` + `StarRing` setting
as `OmegaConjugationOperators.isometry_identities_of`, which carries the
neighbouring printed identities `Q = VPV^*`, `P ≤ Q` and `r = V^*Q`:

* `star_conj_eq_of_conj_eq` is the printed implication `P = VPV^* ⟹ V^*PV = P`;
* `conj_eq_iff_star_conj_eq` records that the two are equivalent, so "preserved
  both ways" is literally a biconditional;
* `commute_of_conj_eq` and `star_commute_of_conj_eq` extract the reason the
  fixed subspace moves both ways: `P = VPV^*` says exactly that `V` commutes
  with `P`, and then so does `V^*`;
* `act_fix_iff` is the printed "hence `V^* Fix = Fix`", for the fixed vectors of
  `P` under any action of the ambient star ring by module endomorphisms: `ζ` is
  fixed by `P` if and only if `Vζ` is.

Only the isometry half `V^*V = 1` of unitarity is consumed by the forward
implication, and only `VV^* = 1` by the reverse; no statement below takes a
hypothesis it does not use.

**What this file does not do.**  It does not rewire
`KazhdanAsymptoticCommutant.transport_star` onto this route.  That rewiring
also has to move the *forward* step (`ID.05`) onto the literal Section-3
theorem `manuscriptKazhdanTransport`, and those two are stated over different
model families — the literal theorem in the natural coordinates
`naturalFiniteModel (d n)`, the consumer over an arbitrary
`OpAlmostRepresentation` — so the rewiring needs a coordinate transfer that is
a separate piece of work.  The exact identity the printed reverse step turns
on had no counterpart anywhere in the corpus; it does now.
-/

namespace GroupApproximation
namespace PrintedReverseTransport

/-! ## The exact reversal, in a bare star ring -/

section StarRing

variable {B : Type*} [Ring B] [StarRing B]

/-- **The printed reverse step.**  `P = VPV^*` gives `V^*PV = P`.

This is the sentence "the equality `P = VPV^*` established in its proof gives
`V^*PV = P`", and it is an exact identity: conjugating the hypothesis by `V^*`
cancels `V^*V = 1` on both sides.  Only the isometry half of unitarity is
used. -/
theorem star_conj_eq_of_conj_eq {V P : B}
    (hVsm : star V * V = 1) (hPQ : V * P * star V = P) :
    star V * P * V = P := by
  calc star V * P * V = star V * (V * P * star V) * V := by rw [hPQ]
    _ = star V * V * P * (star V * V) := by noncomm_ring
    _ = P := by rw [hVsm]; simp

/-- The same reversal in the other direction, by the coisometry half. -/
theorem conj_eq_of_star_conj_eq {V P : B}
    (hVms : V * star V = 1) (hPQ : star V * P * V = P) :
    V * P * star V = P := by
  calc V * P * star V = V * (star V * P * V) * star V := by rw [hPQ]
    _ = V * star V * P * (V * star V) := by noncomm_ring
    _ = P := by rw [hVms]; simp

/-- **"Preserved both ways", as a biconditional.**  For a unitary `V`, the
conjugated and inverse-conjugated identities are equivalent. -/
theorem conj_eq_iff_star_conj_eq {V P : B}
    (hVsm : star V * V = 1) (hVms : V * star V = 1) :
    V * P * star V = P ↔ star V * P * V = P :=
  ⟨star_conj_eq_of_conj_eq hVsm, conj_eq_of_star_conj_eq hVms⟩

/-- **Why the fixed subspace moves both ways.**  `P = VPV^*` says exactly that
`V` commutes with `P`. -/
theorem commute_of_conj_eq {V P : B}
    (hVsm : star V * V = 1) (hPQ : V * P * star V = P) :
    V * P = P * V := by
  calc V * P = V * P * (star V * V) := by rw [hVsm]; simp
    _ = V * P * star V * V := by noncomm_ring
    _ = P * V := by rw [hPQ]

/-- And then so does `V^*`. -/
theorem star_commute_of_conj_eq {V P : B}
    (hVsm : star V * V = 1) (hVms : V * star V = 1)
    (hPQ : V * P * star V = P) :
    star V * P = P * star V := by
  have h : star V * P * V = P := star_conj_eq_of_conj_eq hVsm hPQ
  calc star V * P = star V * P * (V * star V) := by rw [hVms]; simp
    _ = star V * P * V * star V := by noncomm_ring
    _ = P * star V := by rw [h]

end StarRing

/-! ## `V^* Fix = Fix`

The printed conclusion drawn from `V^*PV = P`.  `Fix` is `ran P`, so what has
to be said is that `V` carries the fixed vectors of `P` onto the fixed vectors
of `P`; since the statement is a biconditional and `V` is invertible, this is
the printed equality of subspaces rather than an inclusion. -/

section Fix

variable {B : Type*} [Ring B] [StarRing B]
variable {R K : Type*} [Semiring R] [AddCommMonoid K] [Module R K]

omit [StarRing B] in
theorem act_mul_apply (rho : B →* Module.End R K) (a b : B) (ζ : K) :
    rho (a * b) ζ = rho a (rho b ζ) := by
  simp only [map_mul, Module.End.mul_apply]

omit [StarRing B] in
theorem act_one_apply (rho : B →* Module.End R K) (ζ : K) :
    rho 1 ζ = ζ := by
  simp only [map_one, Module.End.one_apply]

/-- An isometry acts injectively, with `V^*` undoing `V`. -/
theorem act_star_left (rho : B →* Module.End R K) {V : B}
    (hVsm : star V * V = 1) (ζ : K) :
    rho (star V) (rho V ζ) = ζ := by
  rw [← act_mul_apply, hVsm, act_one_apply]

/-- **"hence `V^* Fix = Fix`".**  If `P = VPV^*`, then a vector is fixed by `P`
exactly when its image under `V` is.  Both directions are available because the
identity reverses, which is the content of `star_conj_eq_of_conj_eq`. -/
theorem act_fix_iff (rho : B →* Module.End R K) {V P : B}
    (hVsm : star V * V = 1) (hPQ : V * P * star V = P) (ζ : K) :
    rho P (rho V ζ) = rho V ζ ↔ rho P ζ = ζ := by
  have hcomm : V * P = P * V := commute_of_conj_eq hVsm hPQ
  have hswap : ∀ η : K, rho P (rho V η) = rho V (rho P η) := by
    intro η
    rw [← act_mul_apply, ← act_mul_apply, ← hcomm]
  constructor
  · intro hfix
    have h1 : rho V (rho P ζ) = rho V ζ := by
      rw [← hswap]
      exact hfix
    have h2 := congrArg (rho (star V)) h1
    rwa [act_star_left rho hVsm, act_star_left rho hVsm] at h2
  · intro hfix
    rw [hswap, hfix]

end Fix

end PrintedReverseTransport
end GroupApproximation
