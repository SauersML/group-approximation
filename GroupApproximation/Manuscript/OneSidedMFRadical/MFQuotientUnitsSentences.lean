import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnits

/-!
# `thm:mf-quotient-units`, sentence by sentence

`non_mf_groups_exist.tex`, the printed proof of Theorem
`thm:mf-quotient-units`.  The statement is carried by
`MFQuotientUnits.PrintedMFQuotientUnits`; this module adds one named lemma per
printed sentence, each quoting its sentence verbatim and each proved from the
pieces already landed.

Three kinds of carrier appear, and the docstrings say which is which.

* Sentences the proof *proves* are carried unconditionally: the
  countable-abelian clause, the containment `N ≤ ker κ`, the normal-subgroup
  absorption, and the printed display `eq:corner-units`.
* Sentences the proof *quotes* from Ara--Goodearl--Pardo are carried
  conditionally on the corresponding named proposition, which is the honest
  shape: the sentence holds exactly as far as its citation does.
* One printed sentence is not separately carried, and is named as such below.

The `n ≥ 2` reduction is the printed one but shorter: the printed sentence also
invokes Morita invariance to identify `K_1(M_n R)` with `K_1(R)`, and the
formalized statement does not name that group, so the Morita half has no
carrier and needs none.
-/

namespace GroupApproximation
namespace MFQuotientUnitsSentences

open Manuscript.OneSidedMFRadical
open MFQuotientUnits

noncomputable section

/-! ## The reduction to `n = 1` -/

/-- **Printed sentence 1.**

> The ring `M_n(R)` is again countable, purely infinite, and simple
> \[AGP, Corollary 1.7\], and `K_1(M_n(R)) ≅ K_1(R)` by Morita invariance, so
> it suffices to treat `n = 1`.

Carried conditionally on `AGPMatrixReduction`, which is the citation.  The
Morita clause has no carrier: the formalized conclusion states the quotient as
an unnamed countable abelian MF group, so nothing has to identify
`K_1(M_n R)` with `K_1(R)`, and the reduction goes through the unit group of
`M_n(R)`, which *is* `GL_n(R)`. -/
theorem manuscriptSentence_matrixRingAgainPurelyInfinite
    (hMat : AGPMatrixReduction) (R : Type) [Ring R] [Countable R]
    (hR : IsPurelyInfiniteSimpleRing R) (n : ℕ) (hn : 1 ≤ n) :
    Countable (Matrix (Fin n) (Fin n) R) ∧
      IsPurelyInfiniteSimpleRing (Matrix (Fin n) (Fin n) R) := by
  refine ⟨?_, hMat R hR n hn⟩
  show Countable (Fin n → Fin n → R)
  infer_instance

/-! ## `N ≤ ker κ` -/

/-- **Printed sentence 2.**

> Write `H = Rˣ` and `N = N_1`.  Ara, Goodearl, and Pardo show that `κ` is
> surjective with kernel `[H,H]` \[AGP, Theorem 2.4\].

Carried conditionally on `AGPUnitK1`, which is the citation.  `K_1(R)` is
supplied by that proposition as an abstract countable abelian group rather than
constructed. -/
theorem manuscriptSentence_kappaSurjectiveKernelCommutator
    (hK1 : AGPUnitK1) (R : Type) [Ring R] [Countable R]
    (hR : IsPurelyInfiniteSimpleRing R) :
    ∃ (A : Type) (_ : CommGroup A) (_ : Countable A) (κ : Rˣ →* A),
      Function.Surjective κ ∧ κ.ker = commutator Rˣ :=
  hK1 R hR

/-- **Printed sentence 3.**

> A countable abelian group `A` is MF: `C*_max(A)` is commutative and
> separable, hence residually finite-dimensional and MF \[BK\], and an
> embedding `ι` of `C*_max(A)` in a norm matrix corona restricts to the
> embedding `a ↦ ι(u_a) + 1 - ι(1)` of `A` in its unitary group.

Carried unconditionally, and *not* by the printed argument.  The print goes
through residual finite-dimensionality and Brown--Kirchberg; the carrier goes
through LEF and residual finiteness of finitely generated abelian groups, so it
quotes nothing.  The conclusion is the same. -/
theorem manuscriptSentence_countableAbelianIsMF (A : Type) [CommGroup A]
    [Countable A] : IsOperatorMF A :=
  isOperatorMF_of_commGroup_countable A

/-- **Printed sentence 4.**

> So `κ` is a homomorphism to an MF group, and `N ≤ ker κ`.

Unconditional, given the target of `κ`: the intersection of the kernels of all
homomorphisms to MF groups is contained in the kernel of any one of them. -/
theorem manuscriptSentence_radicalLeKerKappa {R : Type} [Ring R] {A : Type}
    [CommGroup A] [Countable A] (κ : Rˣ →* A) : mfHomKernel Rˣ ≤ κ.ker := by
  intro x hx
  exact (mem_mfHomKernel_iff x).mp hx A
    (manuscriptSentence_countableAbelianIsMF A) κ

/-! ## `eq:corner-units` -/

/-- **Printed sentence 5.**

> Every nonzero idempotent `e` of `R` is infinite \[AGP, Proposition 1.5\], so
> `eRe` contains `s, t` with `ts = e ≠ st`, and `eRe` is simple, so `e - st`
> generates `eRe` as a two-sided ideal; hence every homomorphism from
> `EL_m(eRe)`, `m ≥ 2`, to an MF group is trivial.

The final clause is the one the rest of the proof consumes, and it is carried
here for an arbitrary countable ring with a one-sided inverse pair whose
complementary idempotent is full --- which is what the earlier clauses say of
`eRe`.  Conditional on Theorem `thm:full-defect-ring` in its rank-two form,
which is where that theorem enters this proof. -/
theorem manuscriptSentence_cornerElementaryKillsMFTargets
    (hB : FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo)
    (S : Type) [Ring S] [Countable S] (s t : S) (hts : t * s = 1)
    (hfull : ∃ (m : ℕ) (a b : Fin m → S), ∑ k, a k * (1 - s * t) * b k = 1)
    (m : ℕ) (hm : 2 ≤ m) (M : Type) [Group M] (hM : IsOperatorMF M)
    (f : elementaryGroup (Fin m) S →* M) (x : elementaryGroup (Fin m) S) :
    f x = 1 :=
  hB S s t hts hfull m hm M hM f x

/-- **Printed sentence 6, the display `eq:corner-units`.**

> Consequently, if `e` and `P` are nonzero idempotents and
> `θ : M_m(eRe) → PRP` is a ring isomorphism, then
> `1 - P + θ(A) ∈ N` for `A ∈ EL_m(eRe)`, since these units form the image of
> `EL_m(eRe)` under a homomorphism to `H`.

Unconditional given sentence 5.  The printed justification is the whole
content, and it is general: the image of a group with no nontrivial
homomorphism to an MF group lies in the intersection of the kernels of all of
them.  Neither the corner ring nor `θ` has to be constructed. -/
theorem manuscriptSentence_cornerUnitsLieInRadical
    (hB : FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo)
    (R : Type) [Ring R] : cornerUnitSubgroup R ≤ mfHomKernel Rˣ :=
  cornerUnitSubgroup_le_mfHomKernel hB R

/-! ## `ker κ ≤ N` -/

/-- **Printed sentence 7.**

> Let `u ∈ ker κ`.  Following the proof of \[AGP, Theorem 2.4\], choose
> orthogonal idempotents `e_1, …, e_m` with sum `1`, `m ≥ 4`, such that
> `e_1, …, e_{m-1}` are pairwise equivalent and `e_m` is equivalent to an
> idempotent `f ≤ e_1`. … the argument of Menal and Moncasi transforms the
> matrix of `u` by elementary row and column operations into one of the form
> `diag(1, ∗)`.  So `u = PvQ`, where `P` and `Q` are products of elementary
> matrices `e_{ij}(x)` of this matrix ring and `v = e_1 + (1-e_1)v(1-e_1)`.

Carried conditionally on `AGPMenalMoncasiReduction`, which is the citation.  The
idempotent decomposition and the twisted matrix ring are internal to that
proposition and are not named separately. -/
theorem manuscriptSentence_menalMoncasiReduction
    (hMM : AGPMenalMoncasiReduction) (R : Type) [Ring R] [Countable R]
    (hR : IsPurelyInfiniteSimpleRing R) (A : Type) [CommGroup A]
    (κ : Rˣ →* A) (hsurj : Function.Surjective κ)
    (hker : κ.ker = commutator Rˣ) {u : Rˣ} (hu : u ∈ κ.ker) :
    ∃ (v : Rˣ) (e : R), e ≠ 0 ∧ IsIdempotentElem e ∧
      (v : R) = e + (1 - e) * (v : R) * (1 - e) ∧
      u * v⁻¹ ∈ cornerUnitSubgroup R :=
  hMM R hR A κ hsurj hker u hu

/-- **Printed sentence 8.**

> The elementary matrices with `i, j ≤ m-1` form `EL_{m-1}(T)` inside
> `(1-e_m)R(1-e_m) ≅ M_{m-1}(T)`, so they lie in `N` by `eq:corner-units`; for
> distinct `i, j ≤ m-1`, `e_{im}(x) = [e_{ij}(1), e_{jm}(x)]` and
> `e_{mj}(x) = [e_{mi}(x), e_{ij}(1)]` are products of an element of
> `EL_{m-1}(T)` and a conjugate of its inverse, so they lie in the normal
> subgroup `N` as well.

Partially carried.  The first clause is `eq:corner-units` (sentence 6).  The
second clause's *reason* --- a normal subgroup absorbs a product of one of its
elements with a conjugate of the inverse of another --- is the lemma below, and
it is unconditional.  The identification of the two Steinberg displays with
elements of `EL_{m-1}(T)` is internal to `AGPMenalMoncasiReduction` and has no
separate carrier; that is the one printed sentence of this proof not carried on
its own. -/
theorem manuscriptSentence_normalAbsorbsConjugateOfInverse
    {G : Type} [Group G] (N : Subgroup G) [hN : N.Normal] {a b : G}
    (ha : a ∈ N) (hb : b ∈ N) (g : G) : a * (g * b⁻¹ * g⁻¹) ∈ N :=
  N.mul_mem ha (hN.conj_mem _ (N.inv_mem hb) g)

/-- **Printed sentence 9.**

> Hence `u ≡ v` modulo `N`, and `κ(v) = κ(u) = 0` because `N ≤ ker κ`.

Unconditional.  `u` and `v` differ by a corner unit, corner units lie in `N` by
`eq:corner-units`, and `N ≤ ker κ` by sentence 4; so `κ` cannot tell `u` and
`v` apart, and `κ(u) = 1` forces `κ(v) = 1`. -/
theorem manuscriptSentence_kappaVEqOne {R : Type} [Ring R] {A : Type}
    [CommGroup A] [Countable A] (κ : Rˣ →* A) {u v : Rˣ} (hu : u ∈ κ.ker)
    (huv : u * v⁻¹ ∈ mfHomKernel Rˣ) : κ v = 1 := by
  have hkuv : κ (u * v⁻¹) = 1 := manuscriptSentence_radicalLeKerKappa κ huv
  have hku : κ u = 1 := hu
  rw [map_mul, hku, one_mul, map_inv, inv_eq_one] at hkuv
  exact hkuv

/-- **Printed sentence 10.**

> Finally let `v = e + (1-e)v(1-e)` with `e ≠ 0` and `κ(v) = 0`.  By the
> definition of `K_1`, `diag(v,1,…,1) ∈ EL_n(R)` for some `n ≥ 2`. … There is a
> ring isomorphism `θ : M_n(R) → PRP` under which `diag(v,1,…,1)` corresponds
> to `(1-e)v(1-e) + f + r_2 + … + r_n = v - (1-P)`.  So
> `v = 1 - P + θ(diag(v,1,…,1)) ∈ N` by `eq:corner-units`.  Hence
> `ker κ ≤ N`.

The body is carried conditionally on `AGPStepOne`, which is the citation; the
final clause `ker κ ≤ N`, and with it the whole theorem, is unconditional given
the quoted propositions and is
`MFQuotientUnits.mfHomKernel_units_eq_commutator`. -/
theorem manuscriptSentence_stepOneGivesKerKappaLeRadical
    (hS1 : AGPStepOne) (R : Type) [Ring R] [Countable R]
    (hR : IsPurelyInfiniteSimpleRing R) (A : Type) [CommGroup A]
    (κ : Rˣ →* A) (hsurj : Function.Surjective κ)
    (hker : κ.ker = commutator Rˣ) (v : Rˣ) (e : R) (hene : e ≠ 0)
    (hidem : IsIdempotentElem e)
    (hvform : (v : R) = e + (1 - e) * (v : R) * (1 - e)) (hkv : κ v = 1) :
    v ∈ cornerUnitSubgroup R :=
  hS1 R hR A κ hsurj hker v e hene hidem hvform hkv

/-- **The printed conclusion of the proof.**

> Hence `ker κ ≤ N`.

Together with sentence 4 this is the equality `N = ker κ = [H,H]`, which with
the reduction of sentence 1 is the theorem. -/
theorem manuscriptSentence_conclusion
    (hB : FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo)
    (hK1 : AGPUnitK1) (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne)
    (R : Type) [Ring R] [Countable R] (hR : IsPurelyInfiniteSimpleRing R) :
    mfHomKernel Rˣ = commutator Rˣ :=
  (mfHomKernel_units_eq_commutator hB hK1 hMM hS1 countableAbelianMF R hR).1

end

end MFQuotientUnitsSentences
end GroupApproximation
