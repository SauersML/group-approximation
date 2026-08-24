import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Comparison in a finite C-star algebra

This file formalizes the *generic* finiteness principle printed in
`non_mf_groups_exist.tex` as the lemma captioned
*comparison in a finite algebra* (the finite-algebra comparison result), in the
`\section{One-sided Kazhdan transport}` (the former transport argument).  Grep the
manuscript for the sentence "In the right-hand column, $p\sim q$ is
Murray--von Neumann equivalence"; line numbers are deliberately not cited
because the manuscript is under concurrent edit.  The printed statement is

> Let `A` be a finite unital C-star algebra and let `p, q ∈ A` be projections
> with `p ≤ q` and `p ∼ q`.  Then `p = q`.

together with the printed conventions, from the display that introduces the
three "manifestations of one finiteness principle":

> In the right-hand column, `p ∼ q` is Murray--von Neumann equivalence, and a
> C-star algebra is *finite* when every isometry in it is unitary.

Both conventions are honoured literally below: `MurrayVonNeumannEquiv` is the
existence of a partial isometry with initial projection `p` and final
projection `q`, and finiteness enters as the hypothesis
`∀ x, star x * x = 1 → x * star x = 1` -- the manuscript's own words -- not as
the formally stronger `IsDedekindFiniteMonoid`, which starts from an arbitrary
one-sided inverse.  A bridge from that class is supplied for the repository's
existing instances, whose only witness is
`Sofic/UltraproductDedekindFinite.normMatrixCStarCorona_isDedekindFiniteMonoid`.

## The printed computation

The manuscript proves the lemma by

> Let `r ∈ A` satisfy `r*r = q` and `rr* = p`.  From `r*r = q` we get `r = rq`,
> and from `ran r = ran p ⊆ ran q` we get `r = qr`.  Hence the cross terms in
> `σ*σ` vanish for `σ = r + (1 - q)`, and `σ*σ = q + (1 - q) = 1`, so `σ` is an
> isometry.  Finiteness makes `σ` unitary, and `σσ* = p + (1 - q) = 1` gives
> `p = q`.

Written out with every step algebraic -- this is what
`eq_of_murrayVonNeumannEquiv_of_absorbs` executes:

* `r` is the *reversed* implementer.  Murray--von Neumann equivalence supplies
  `v` with `v*v = p` and `vv* = q`; the manuscript's `r` is `v*`, which is why
  the proof below opens `hmvn.symm` rather than `hmvn`.
* `r = rq`, i.e. `r(1 - q) = 0`.  The two range statements of the manuscript
  are the C-star-algebraic facts `x*x = 0 → x = 0`; here
  `(r(1-q))*(r(1-q)) = (1-q)(r*r)(1-q) = (1-q)q(1-q) = 0`.
* `r = pr`, i.e. `(1 - p)r = 0`, from the mirrored fact `xx* = 0 → x = 0`:
  `((1-p)r)((1-p)r)* = (1-p)(rr*)(1-p) = (1-p)p(1-p) = 0`.  This is the
  manuscript's `ran r = ran p`.
* `r = qr` is now the *only* place the containment `p ≤ q` is used:
  `(1 - q)r = (1 - q)(pr) = ((1 - q)p)r = 0` because `qp = p`.  This is the
  manuscript's `ran p ⊆ ran q`.
* Starring the last two identities gives `r*(1 - q) = 0` and `(1 - q)r* = 0`,
  which are the vanishing cross terms.
* `σ*σ = r*r + r*(1-q) + (1-q)r + (1-q)² = q + 0 + 0 + (1 - q) = 1`.
* `σσ* = rr* + r(1-q) + (1-q)r* + (1-q)² = p + 0 + 0 + (1 - q)`.
* Finiteness turns the first identity into `σσ* = 1`, so `p + (1 - q) = 1`,
  i.e. `p = q`.

Note that only `qp = p` is consumed, never `pq = p`: the second absorption
identity is the star of the first and is therefore free.

## Relation to what the repository already had

`Analysis/ProperIsometryFromCompression.lean` runs this same calculation in the
special case `q = u p u*` with `u` unitary, and its
`ProperProjectionCompression.isometry := p * star u + (1 - q)` is *literally*
the `σ` above for the Murray--von Neumann implementer `v = u p` (so
`r = v* = p u*`).  That file is not superseded, and it is not a weaker version
of this one: it works in a bare star ring, because there it never has to
*derive* `r = rq` and `r = pr` -- both are visible from the explicit formula
for `r`.  The generic statement has no explicit formula to read them off, so
the printed route needs `x*x = 0 → x = 0` at exactly those two steps, and that
is a C-star input.  (Whether the generic statement nevertheless holds in a bare
star ring is not settled here; no counterexample is claimed.)  So the two
results are incomparable as stated: this file is generic in the pair `(p, q)`
and costs a C-star algebra; that file is generic in the ring and costs a
unitary implementer.
-/

namespace GroupApproximation

/-! ## Murray--von Neumann equivalence -/

/-- **Murray--von Neumann equivalence of projections**, the manuscript's
`p ∼ q`: a partial isometry with initial projection `p` and final projection
`q`.

No projection hypothesis is imposed on `p` and `q` here -- the two identities
alone do not force it, since `v*v` need not be idempotent for a general `v`.
The lemmas that consume this relation take the projection hypotheses
separately, exactly as the manuscript's sentence does. -/
def MurrayVonNeumannEquiv {A : Type*} [Mul A] [Star A] (p q : A) : Prop :=
  ∃ v : A, star v * v = p ∧ v * star v = q

/-- Every projection is Murray--von Neumann equivalent to itself, implemented
by the projection itself. -/
theorem MurrayVonNeumannEquiv.refl {A : Type*} [Mul A] [Star A] {p : A}
    (hp : IsStarProjection p) : MurrayVonNeumannEquiv p p :=
  ⟨p, by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

/-- Murray--von Neumann equivalence is symmetric: adjointing the implementer
exchanges the initial and final projections.  This is what lets the proof of
`eq_of_murrayVonNeumannEquiv_of_absorbs` work with the manuscript's `r`, whose
identities are `r*r = q` and `rr* = p`, rather than with the implementer in the
orientation the definition fixes. -/
theorem MurrayVonNeumannEquiv.symm {A : Type*} [Mul A] [InvolutiveStar A]
    {p q : A} (h : MurrayVonNeumannEquiv p q) : MurrayVonNeumannEquiv q p := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  exact ⟨star v, by rw [star_star]; exact hv₂, by rw [star_star]; exact hv₁⟩

/-- A projection is Murray--von Neumann equivalent to any conjugate of itself
by an isometry, implemented by `v = u p`.

Only `u*u = 1` is used; `u` need not be unitary.  This is the instance the
Kazhdan transport step consumes: there `u = π(s)` is the image of the shift and
`q = u p u*` is the conjugated Kazhdan projection. -/
theorem MurrayVonNeumannEquiv.of_isometry_conjugate {A : Type*} [Ring A]
    [StarRing A] {p u : A} (hp : IsStarProjection p) (hu : star u * u = 1) :
    MurrayVonNeumannEquiv p (u * p * star u) := by
  refine ⟨u * p, ?_, ?_⟩
  · rw [star_mul, hp.isSelfAdjoint.star_eq]
    calc p * star u * (u * p) = p * (star u * u) * p := by noncomm_ring
      _ = p * 1 * p := by rw [hu]
      _ = p * p := by rw [mul_one]
      _ = p := hp.isIdempotentElem.eq
  · rw [star_mul, hp.isSelfAdjoint.star_eq]
    calc u * p * (p * star u) = u * (p * p) * star u := by noncomm_ring
      _ = u * p * star u := by rw [hp.isIdempotentElem.eq]

/-- The isometry conjugate of a projection is again a projection.  Only
`u*u = 1` is needed for idempotence, and nothing at all for self-adjointness. -/
theorem isStarProjection_isometry_conjugate {A : Type*} [Ring A] [StarRing A]
    {p u : A} (hp : IsStarProjection p) (hu : star u * u = 1) :
    IsStarProjection (u * p * star u) where
  isIdempotentElem := by
    show u * p * star u * (u * p * star u) = u * p * star u
    calc u * p * star u * (u * p * star u)
        = u * (p * (star u * u) * p) * star u := by noncomm_ring
      _ = u * (p * 1 * p) * star u := by rw [hu]
      _ = u * (p * p) * star u := by rw [mul_one]
      _ = u * p * star u := by rw [hp.isIdempotentElem.eq]
  isSelfAdjoint := by
    show star (u * p * star u) = u * p * star u
    rw [star_mul, star_mul, star_star, hp.isSelfAdjoint.star_eq]
    noncomm_ring

/-! ## The comparison lemma -/

/-- **Comparison in a finite algebra, the star-ring core.**  This is
the finite-algebra comparison result of `non_mf_groups_exist.tex` with the two C-star
inputs it actually uses isolated as hypotheses:

* `hproper`: `x*x = 0 → x = 0`.  In a C-star algebra this is
  `CStarRing.star_mul_self_eq_zero_iff`; it is what turns the manuscript's two
  range statements `r = rq` and `r = pr` into algebra.  Without it the printed
  derivation of those two identities is unavailable; no claim is made here that
  the conclusion fails in a bare star ring.
* `hfinite`: the manuscript's definition of a finite C-star algebra, "every
  isometry in it is unitary".

The containment `p ≤ q` appears in its ring-theoretic form `qp = p`; the
mirrored identity `pq = p` is the star of it and is never needed.

The proof is the printed one, step for step; see the module docstring for the
full computation. -/
theorem eq_of_murrayVonNeumannEquiv_of_absorbs {A : Type*} [Ring A] [StarRing A]
    (hproper : ∀ x : A, star x * x = 0 → x = 0)
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q * p = p) (hmvn : MurrayVonNeumannEquiv p q) :
    p = q := by
  -- The manuscript's `r`, with `r*r = q` and `rr* = p`.
  obtain ⟨r, hrq, hrp⟩ := hmvn.symm
  -- The mirrored properness statement, obtained by adjointing.
  have hproper' : ∀ x : A, x * star x = 0 → x = 0 := by
    intro x hx
    have hstar : star (star x) * star x = 0 := by rw [star_star]; exact hx
    exact star_eq_zero.mp (hproper (star x) hstar)
  have hone_sub_q_mul_q : (1 - q) * q = 0 := by
    rw [sub_mul, one_mul, hq.isIdempotentElem.eq, sub_self]
  have hone_sub_p_mul_p : (1 - p) * p = 0 := by
    rw [sub_mul, one_mul, hp.isIdempotentElem.eq, sub_self]
  have hone_sub_q_mul_p : (1 - q) * p = 0 := by
    rw [sub_mul, one_mul, hqp, sub_self]
  have hone_sub_q_idem : (1 - q) * (1 - q) = 1 - q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hq.isIdempotentElem.eq, sub_self,
      sub_zero]
  -- `r = rq`: the manuscript's first range statement.
  have hr_one_sub_q : r * (1 - q) = 0 := by
    refine hproper _ ?_
    have hstar : star (r * (1 - q)) = (1 - q) * star r := by
      rw [star_mul, star_sub, star_one, hq.isSelfAdjoint.star_eq]
    calc star (r * (1 - q)) * (r * (1 - q))
        = (1 - q) * star r * (r * (1 - q)) := by rw [hstar]
      _ = (1 - q) * (star r * r) * (1 - q) := by noncomm_ring
      _ = (1 - q) * q * (1 - q) := by rw [hrq]
      _ = 0 := by rw [hone_sub_q_mul_q, zero_mul]
  -- `ran r = ran p`, i.e. `r = pr`.
  have hone_sub_p_r : (1 - p) * r = 0 := by
    refine hproper' _ ?_
    have hstar : star ((1 - p) * r) = star r * (1 - p) := by
      rw [star_mul, star_sub, star_one, hp.isSelfAdjoint.star_eq]
    calc (1 - p) * r * star ((1 - p) * r)
        = (1 - p) * r * (star r * (1 - p)) := by rw [hstar]
      _ = (1 - p) * (r * star r) * (1 - p) := by noncomm_ring
      _ = (1 - p) * p * (1 - p) := by rw [hrp]
      _ = 0 := by rw [hone_sub_p_mul_p, zero_mul]
  have hpr : p * r = r := by
    have h : r - p * r = 0 := by
      have hexpand := hone_sub_p_r
      rwa [sub_mul, one_mul] at hexpand
    exact (sub_eq_zero.mp h).symm
  -- `ran p ⊆ ran q`, i.e. `r = qr`.  The only use of the containment `p ≤ q`.
  have hone_sub_q_r : (1 - q) * r = 0 := by
    calc (1 - q) * r = (1 - q) * (p * r) := by rw [hpr]
      _ = (1 - q) * p * r := by noncomm_ring
      _ = 0 := by rw [hone_sub_q_mul_p, zero_mul]
  -- The two cross terms, obtained by adjointing the two range statements.
  have hstar_r_one_sub_q : star r * (1 - q) = 0 := by
    have h := congrArg star hone_sub_q_r
    rwa [star_mul, star_sub, star_one, hq.isSelfAdjoint.star_eq,
      star_zero] at h
  have hone_sub_q_star_r : (1 - q) * star r = 0 := by
    have h := congrArg star hr_one_sub_q
    rwa [star_mul, star_sub, star_one, hq.isSelfAdjoint.star_eq,
      star_zero] at h
  -- The manuscript's `σ = r + (1 - q)`.
  have hstar_sigma : star (r + (1 - q)) = star r + (1 - q) := by
    rw [star_add, star_sub, star_one, hq.isSelfAdjoint.star_eq]
  have hsigma_isometry : star (r + (1 - q)) * (r + (1 - q)) = 1 := by
    calc star (r + (1 - q)) * (r + (1 - q))
        = (star r + (1 - q)) * (r + (1 - q)) := by rw [hstar_sigma]
      _ = star r * r + star r * (1 - q) + (1 - q) * r
            + (1 - q) * (1 - q) := by noncomm_ring
      _ = q + 0 + 0 + (1 - q) := by
            rw [hrq, hstar_r_one_sub_q, hone_sub_q_r, hone_sub_q_idem]
      _ = 1 := by abel
  have hsigma_range : (r + (1 - q)) * star (r + (1 - q)) = p + (1 - q) := by
    calc (r + (1 - q)) * star (r + (1 - q))
        = (r + (1 - q)) * (star r + (1 - q)) := by rw [hstar_sigma]
      _ = r * star r + r * (1 - q) + (1 - q) * star r
            + (1 - q) * (1 - q) := by noncomm_ring
      _ = p + 0 + 0 + (1 - q) := by
            rw [hrp, hr_one_sub_q, hone_sub_q_star_r, hone_sub_q_idem]
      _ = p + (1 - q) := by abel
  -- Finiteness makes `σ` unitary, and `σσ* = p + (1 - q) = 1` gives `p = q`.
  have hunitary : (r + (1 - q)) * star (r + (1 - q)) = 1 :=
    hfinite _ hsigma_isometry
  rw [hsigma_range] at hunitary
  refine sub_eq_zero.mp ?_
  calc p - q = p + (1 - q) - 1 := by abel
    _ = 1 - 1 := by rw [hunitary]
    _ = 0 := sub_self 1

/-- **Comparison in a finite C-star algebra**, with the containment in its
ring-theoretic form `qp = p`.  The properness input of
`eq_of_murrayVonNeumannEquiv_of_absorbs` is discharged by the C-star identity
through `CStarRing.star_mul_self_eq_zero_iff`, so the only remaining hypothesis
beyond the projections and the containment is the manuscript's own definition
of finiteness. -/
theorem cstar_eq_of_murrayVonNeumannEquiv_of_absorbs {A : Type*}
    [CStarAlgebra A]
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q * p = p) (hmvn : MurrayVonNeumannEquiv p q) :
    p = q :=
  eq_of_murrayVonNeumannEquiv_of_absorbs
    (fun x hx ↦ (CStarRing.star_mul_self_eq_zero_iff x).mp hx) hfinite hp hq
    hqp hmvn

/-- **the finite-algebra comparison result verbatim.**  Let `A` be a finite unital
C-star algebra and let `p, q ∈ A` be projections with `p ≤ q` and `p ∼ q`.
Then `p = q`.

Here `p ≤ q` is the genuine order of the C-star algebra, and the passage to the
ring-theoretic form `qp = p` used by the proof is Mathlib's
`IsStarProjection.le_iff_mul_eq_right`.  The order instances are side inputs, as
everywhere in Mathlib's C-star order API; for a concrete algebra they are
installed by `CStarAlgebra.spectralOrder` and
`CStarAlgebra.spectralOrderedRing`, exactly as
`Analysis/MaximalCStarProperCompression.lean` does. -/
theorem finiteCStar_eq_of_le_of_murrayVonNeumannEquiv {A : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hle : p ≤ q) (hmvn : MurrayVonNeumannEquiv p q) :
    p = q :=
  cstar_eq_of_murrayVonNeumannEquiv_of_absorbs hfinite hp hq
    ((hp.le_iff_mul_eq_right hq).mp hle) hmvn

/-- The comparison lemma for the repository's finiteness class.  Dedekind
finiteness is formally stronger than the manuscript's "every isometry is
unitary" -- it starts from an arbitrary one-sided inverse -- so this is a
weakening of `cstar_eq_of_murrayVonNeumannEquiv_of_absorbs`.  It exists because
the only finiteness witness in this repository,
`normMatrixCStarCorona_isDedekindFiniteMonoid`, is stated in that class. -/
theorem dedekindFiniteCStar_eq_of_murrayVonNeumannEquiv_of_absorbs {A : Type*}
    [CStarAlgebra A] [IsDedekindFiniteMonoid A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q * p = p) (hmvn : MurrayVonNeumannEquiv p q) :
    p = q :=
  cstar_eq_of_murrayVonNeumannEquiv_of_absorbs
    (fun _ hx ↦ mul_eq_one_symm hx) hp hq hqp hmvn

/-- **The Kazhdan transport instance of the comparison lemma.**  In a
Dedekind-finite unital C-star algebra, a projection absorbed by an isometry
conjugate of itself equals that conjugate.

This is the manuscript's sentence "the inclusion `s ι(Γ) s⁻¹ ⊆ ι(Γ)` implies
`P ≤ V P V*`, the two projections are Murray--von Neumann equivalent, and the
ultraproduct is finite, so `P = V P V*`", and it reaches that conclusion *by
that route*: the equivalence comes from
`MurrayVonNeumannEquiv.of_isometry_conjugate` and the comparison from
`dedekindFiniteCStar_eq_of_murrayVonNeumannEquiv_of_absorbs`.

`ProperProjectionCompression.unitary_conjugate_eq_of_absorbs` reaches the same
conclusion in a bare star ring, but without ever naming the Murray--von Neumann
step; conversely this statement needs only the one isometry identity
`u*u = 1`, not both unitary identities.  Neither subsumes the other. -/
theorem dedekindFiniteCStar_isometry_conjugate_eq_of_absorbs {A : Type*}
    [CStarAlgebra A] [IsDedekindFiniteMonoid A] {p u : A}
    (hp : IsStarProjection p) (hu : star u * u = 1)
    (hqp : u * p * star u * p = p) :
    u * p * star u = p :=
  (dedekindFiniteCStar_eq_of_murrayVonNeumannEquiv_of_absorbs hp
    (isStarProjection_isometry_conjugate hp hu) hqp
    (MurrayVonNeumannEquiv.of_isometry_conjugate hp hu)).symm

end GroupApproximation
