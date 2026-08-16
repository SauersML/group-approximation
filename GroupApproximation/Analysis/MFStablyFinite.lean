import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Sofic.UltraproductDedekindFinite
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Every MF algebra is finite, and what stands between that and stably finite

`non_mf_groups_exist.tex` opens the subsection *A stably finite non-MF group
algebra* with

> Every MF algebra is stably finite \cite{BK}; the converse fails.

and then immediately routes around it: the next sentence says the canonical
trace on `Cred(E)` is faithful, "so `Cred(E)` is stably finite
(Lemma~\ref{lem:faithfultrace}), **independently of the MF question**", and
the proof of the theorem labelled `thm:reduced`/`thm:D` cites only
`lem:faithfultrace`.  That lemma is already machine-checked
(`ManuscriptExactWrappers.manuscriptFaithfulTraceAndStableFiniteness`).  So the
quoted Blackadar--Kirchberg sentence carries **no formal debt**: nothing
badged depends on it, and no proof in the manuscript consumes it.  It is
scene-setting — it says why "stably finite but not MF" is the interesting
combination — not a premise.

This file settles how much of it is provable here anyway.

## What is proved

`mul_star_eq_one_of_hasMFEmbedding`: **an MF algebra is finite** — every
isometry in it is a unitary, which is the manuscript's own definition of
finiteness (quoted in `Analysis/FiniteCStarMurrayVonNeumann.lean`).  The proof
is unconditional and uses only what the repository already has:

* the embedding `e : A →⋆ₙₐ Q` into a norm-matrix corona supplied by
  `HasMFEmbedding`, which is *not* assumed unital — so `P := e 1` is a
  proper projection of `Q` and the argument runs in the corner `PQP`;
* `normMatrixCStarCorona_isDedekindFiniteMonoid` (KT.06), the corona's
  Dedekind finiteness, proved by the coordinatewise Neumann estimate;
* `mul_star_eq_of_corner_isometry` below, which is the manuscript's own
  `σ = v + (1 - P)` computation — the same computation
  `Analysis/FiniteCStarMurrayVonNeumann.eq_of_murrayVonNeumannEquiv_of_absorbs`
  runs for the comparison lemma, here used to push finiteness from an algebra
  into a corner of it.

## What is not proved, and exactly why

Stable finiteness is finiteness of `M_k(A)` for every `k`, in the shape the
manuscript's `lem:faithfultrace` states it and this repository spells
`CStarMatrix I I A`.  The reduction is immediate and is recorded as
`mul_star_eq_one_of_matrixHasMFEmbedding`: *if* every matrix amplification of
`A` again has an MF embedding, `A` is stably finite.  The missing input is
therefore a single named C-star fact and nothing else:

> `M_I(Q_X)` is again a norm-matrix corona — concretely
> `CStarMatrix I I (NormMatrixCStarCorona X) ≃⋆ NormMatrixCStarCorona (I × X)`.

That is not a formality in Lean.  `NormMatrixCStarCorona X` is
`ℓ∞(M_{X n}) / c₀(M_{X n})`, and the isomorphism needs (i) the `CStarMatrix`
norm over an `ℓ∞` product to be identified with the supremum of the coordinate
matrix norms, and (ii) `M_I` of the `c₀` ideal to be exactly the `c₀` ideal of
the amplified sequence.  Neither is in Mathlib and neither is in this
repository.  It cannot be dodged by rerunning KT.06 one level up: that proof is
quantitative *and finite-dimensional* — its coordinate step is
`Matrix.mul_eq_one_comm` — and the corresponding norm estimate is false in a
general Banach algebra, as the unilateral shift shows.

So the honest status of the quoted sentence is: **not a live literature input**
(nothing uses it), and, if one insists on formalizing it, **one C-star lemma
short**, with the lemma named above — not research-scale, and not comparable to
the two genuinely open external inputs of this development.
-/

namespace GroupApproximation

universe u

/-! ## Finiteness passes to a corner -/

/-- **The manuscript's `σ = v + (1 - P)` computation, in corner form.**

In a ring where every isometry is a unitary, a partial isometry supported in
the corner cut by a star projection `P` is a unitary *of that corner*: from
`v*v = P` and `PvP = v` one gets `vv* = P`.

This is the same algebraic move as the printed proof of `lem:finitecompare`
formalized in `Analysis/FiniteCStarMurrayVonNeumann.lean` — adjoin the
complementary projection to turn a corner isometry into a genuine isometry,
apply finiteness, and read off the corner identity from the result.  It is
stated in a bare star ring because that is all it needs; the C-star input of
that file (`x*x = 0 → x = 0`) is not required here, since the two absorption
identities are hypotheses rather than things to be derived. -/
theorem mul_star_eq_of_corner_isometry {A : Type*} [Ring A] [StarRing A]
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {P v : A} (hP : IsStarProjection P) (hPv : P * v = v) (hvP : v * P = v)
    (hv : star v * v = P) : v * star v = P := by
  have hsvP : star v * P = star v := by
    have h := congrArg star hPv
    rwa [star_mul, hP.isSelfAdjoint.star_eq] at h
  have hPsv : P * star v = star v := by
    have h := congrArg star hvP
    rwa [star_mul, hP.isSelfAdjoint.star_eq] at h
  have hone_sub_P_idem : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hP.isIdempotentElem.eq, sub_self,
      sub_zero]
  have hv_one_sub_P : v * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hvP, sub_self]
  have hone_sub_P_v : (1 - P) * v = 0 := by
    rw [sub_mul, one_mul, hPv, sub_self]
  have hsv_one_sub_P : star v * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hsvP, sub_self]
  have hone_sub_P_sv : (1 - P) * star v = 0 := by
    rw [sub_mul, one_mul, hPsv, sub_self]
  have hstar_sigma : star (v + (1 - P)) = star v + (1 - P) := by
    rw [star_add, star_sub, star_one, hP.isSelfAdjoint.star_eq]
  have hsigma_isometry : star (v + (1 - P)) * (v + (1 - P)) = 1 := by
    calc star (v + (1 - P)) * (v + (1 - P))
        = (star v + (1 - P)) * (v + (1 - P)) := by rw [hstar_sigma]
      _ = star v * v + star v * (1 - P) + (1 - P) * v
            + (1 - P) * (1 - P) := by noncomm_ring
      _ = P + 0 + 0 + (1 - P) := by
            rw [hv, hsv_one_sub_P, hone_sub_P_v, hone_sub_P_idem]
      _ = 1 := by abel
  have hsigma_range :
      (v + (1 - P)) * star (v + (1 - P)) = v * star v + (1 - P) := by
    calc (v + (1 - P)) * star (v + (1 - P))
        = (v + (1 - P)) * (star v + (1 - P)) := by rw [hstar_sigma]
      _ = v * star v + v * (1 - P) + (1 - P) * star v
            + (1 - P) * (1 - P) := by noncomm_ring
      _ = v * star v + 0 + 0 + (1 - P) := by
            rw [hv_one_sub_P, hone_sub_P_sv, hone_sub_P_idem]
      _ = v * star v + (1 - P) := by abel
  have hunitary : (v + (1 - P)) * star (v + (1 - P)) = 1 :=
    hfinite _ hsigma_isometry
  rw [hsigma_range] at hunitary
  refine sub_eq_zero.mp ?_
  calc v * star v - P = v * star v + (1 - P) - 1 := by abel
    _ = 1 - 1 := by rw [hunitary]
    _ = 0 := sub_self 1

/-! ## An MF algebra is finite -/

/-- **Every MF algebra is finite.**  If `A` admits a faithful, not necessarily
unital, star homomorphism into a norm-matrix corona, then every isometry of
`A` is a unitary.

This is the `k = 1` half of the sentence "Every MF algebra is stably finite"
quoted from Blackadar--Kirchberg in the manuscript, and it is proved here from
repository inputs only: the corona is Dedekind finite by KT.06
(`normMatrixCStarCorona_isDedekindFiniteMonoid`), and nonunitality of the
embedding is absorbed by running the manuscript's `σ`-computation in the
corner cut by `P = e 1` (`mul_star_eq_of_corner_isometry`).

Note that `HasMFEmbedding` is used rather than `IsMFAlgebra`: separability
plays no role in this direction, so the weaker hypothesis is the honest
one. -/
theorem mul_star_eq_one_of_hasMFEmbedding {A : Type u} [CStarAlgebra A]
    (hA : HasMFEmbedding A) {v : A} (hv : star v * v = 1) :
    v * star v = 1 := by
  rcases hA with ⟨X, hne, _hX, _hmono, e, he⟩
  letI : ∀ n, Nonempty (X n) := hne
  have hfinite : ∀ x : NormMatrixCStarCorona (fun n ↦ X n),
      star x * x = 1 → x * star x = 1 := fun _ hx ↦ mul_eq_one_symm hx
  have hPidem : e 1 * e 1 = e 1 := by
    rw [← map_mul, one_mul]
  have hPsa : star (e 1) = e 1 := by
    rw [← map_star, star_one]
  have hP : IsStarProjection (e 1) := ⟨hPidem, hPsa⟩
  have hPv : e 1 * e v = e v := by
    rw [← map_mul, one_mul]
  have hvP : e v * e 1 = e v := by
    rw [← map_mul, mul_one]
  have hev : star (e v) * e v = e 1 := by
    rw [← map_star, ← map_mul, hv]
  have hmain : e v * star (e v) = e 1 :=
    mul_star_eq_of_corner_isometry hfinite hP hPv hvP hev
  have hcomp : e (v * star v) = e v * star (e v) := by
    rw [map_mul, map_star]
  exact he (by rw [hcomp, hmain, map_one])

/-! ## The reduction to matrix amplification -/

/-- **MF plus matrix amplification gives stable finiteness.**

The manuscript's stable finiteness — `lem:faithfultrace`(2), "for every
`k ≥ 1`, every isometry in `M_k(A)` is a unitary" — follows from
`mul_star_eq_one_of_hasMFEmbedding` the moment one knows that every matrix
amplification of `A` is again MF.  That single implication is taken as an
explicit hypothesis rather than hidden in a predicate, because it is precisely
what this repository cannot currently supply: it reduces to
`M_I(NormMatrixCStarCorona X) ≃⋆ NormMatrixCStarCorona (I × X)`, and the
module docstring records why that isomorphism is real analytic work rather
than bookkeeping.

Stating the reduction is the point: it converts "every MF algebra is stably
finite" from a literature citation into one named, unproved C-star lemma. -/
theorem mul_star_eq_one_of_matrixHasMFEmbedding
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hamp : ∀ (I : Type) [Fintype I] [DecidableEq I],
      HasMFEmbedding (CStarMatrix I I A))
    (I : Type) [Fintype I] [DecidableEq I]
    {v : CStarMatrix I I A} (hv : star v * v = 1) :
    v * star v = 1 :=
  mul_star_eq_one_of_hasMFEmbedding (hamp I) hv

/-- The same reduction in the manuscript's indexing, over `Fin k`. -/
theorem fin_mul_star_eq_one_of_matrixHasMFEmbedding
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (hamp : ∀ (I : Type) [Fintype I] [DecidableEq I],
      HasMFEmbedding (CStarMatrix I I A))
    (k : ℕ) {v : CStarMatrix (Fin k) (Fin k) A} (hv : star v * v = 1) :
    v * star v = 1 :=
  mul_star_eq_one_of_matrixHasMFEmbedding hamp (Fin k) hv

end GroupApproximation
