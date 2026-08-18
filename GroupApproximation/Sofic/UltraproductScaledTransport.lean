import GroupApproximation.Sofic.ScaledKazhdanTransport
import GroupApproximation.Sofic.UltraproductKazhdanTransport

/-!
# Transport at every Hilbertian scale: the printed proof of `thm:transport-variants`(1)

This file replays part **(1)** of Theorem `\ref{thm:transport-variants}`
("transport at every scale, and of intertwiners") of `non_mf_groups_exist.tex`,
inside `\section{Weights and intertwiners}` (`\ref{supp:transport-variants}`),
together with the trailing remark that identifies the dimension weight
(`Taking $\nu_n=d_n$ gives Theorem`).  The route is the one the manuscript
prints.

## STATUS: THE ROUTE IS NOT YET CLOSED

**Nothing here certifies the printed theorem yet, and no declaration in this
file may carry a `\leanverified` badge.**  The endpoints `transport_variants_one`
and `scaled_transport_both_of_ambient` each take an `ambient` argument: a
`WeightedUltraproductAdjointModel` for every free ultrafilter on `ℕ`.  **Until
an instance of that structure is constructed from the real ambient, the
endpoints are vacuous** — true, but about an empty hypothesis class — and this
file is an unfinished target, not a formalization of
`thm:transport-variants`(1).  The structure is retained only because it is
scheduled to be discharged: it is an interface awaiting its construction, not a
standing assumption.  **The signature of `WeightedUltraproductAdjointModel` is
frozen**: the construction is being built against it as written, so it must not
be changed --- neither field added nor field removed --- until that instance
exists.  The same caveat applies verbatim to `ultraproductKazhdanTransport` in
`Sofic.UltraproductKazhdanTransport`.

What *is* closed here, unconditionally and with no structure in sight, is the
whole weight layer: `eq_zero_of_matMass_eq_zero`, `eq_zero_of_weight_zero`,
`kt_01_matMass_adjoint`, `kt_01_matMass_coadjoint`, the `WeightNull` calculus,
`weightNull_atTop_of_forall_free_ultrafilter` (the manuscript's contradiction
skeleton at the weight), `weightNull_atTop_iff_scaledMassVanishing`, and the
dimension-weight dictionaries `hsNormSq_eq_matMass_div`,
`matMass_le_iff_hsNormSq_le`, `weightNull_dimension_iff_tendsto`,
`hsNormSq_displacement_eq_commutator`.  Also closed, modulo the interface, are
KT.10 and KT.11 at an arbitrary weight in both directions.

## The printed statement

Let `Γ`, `H`, `ι`, `s` be as in `\ref{thm:kazhdan-transport}`, let
`(U_n)` be as there, let `(w_n)` be nonnegative weights, suppose there is `C`
with `Tr(x_n* x_n) ≤ C w_n` for all `n`, and suppose that for every `γ ∈ Γ`
and every `ε > 0`, eventually

`Tr |x_n - U_n(ι γ) x_n U_n(ι γ)*|² ≤ ε w_n`.

Then `U_n(s) x_n U_n(s)*` **and** `U_n(s)* x_n U_n(s)` satisfy both conditions
as well.  Both directions are asserted, and both are proved here
(`transport_variants_one`).

Here `Tr` is the *unnormalized* trace, so `Tr(x* x)` is the unnormalized
squared Frobenius mass `matMass` of `Sofic.ScaledKazhdanTransport`; that file's
`matMass` API is reused verbatim rather than rebuilt.

## The printed proof, step by step

> Give each coordinate space with `w_n > 0` the inner product
> `⟨x,y⟩ = Tr(y* x)/w_n`; an index with `w_n = 0` forces `x_n = 0`.
> Conjugation by a unitary is unitary for every weight, and both hypotheses
> and both conclusions concern only the renormalized norms, so the
> ultraproduct proof of `thm:kazhdan-transport` applies verbatim: the mass
> bound defines the ultraproduct vector, the adjoint actions remain
> operator-norm almost multiplicative, and finiteness reverses the one-sided
> compression in both directions.

Each clause is a declaration below.

* "an index with `w_n = 0` forces `x_n = 0`" is `eq_zero_of_weight_zero`.
* "conjugation by a unitary is unitary for every weight" is
  `kt_01_matMass_adjoint` and `kt_01_matMass_coadjoint`: the renormalized norm
  at weight `w_n` is `matMass/w_n`, and `matMass` is exactly invariant under
  `X ↦ U X U*` and `X ↦ U* X U`, with no weight entering.
* "both hypotheses and both conclusions concern only the renormalized norms"
  is the pair of predicates `WeightBounded` and `WeightNull`, which are the
  printed conditions verbatim.
* "the ultraproduct proof of `thm:kazhdan-transport` applies verbatim" is the
  interface `WeightedUltraproductAdjointModel`, which is
  `UltraproductAdjointModel` of `Sofic.UltraproductKazhdanTransport` with the
  dimension normalization `hsNormSq` replaced by the weight `w`.
* "the mass bound defines the ultraproduct vector" is the hypothesis
  `WeightBounded w C ξ` guarding `cls_eq_iff`.
* "finiteness reverses the one-sided compression in both directions" is
  `kt_10_conjugate_eq` (Dedekind finiteness of `B_ω` turns `P ≤ Q` into
  `Q = P`, exactly as in KT.10) together with `pi_mul_P` and `star_pi_mul_P`,
  the two directions in which `Q = P` is used.
* KT.11 at the weight is `kt_11_descend_at_every_weight`, and the manuscript's
  contradiction skeleton ("fix a free ultrafilter `ω` with `I ∈ ω`") is
  `weightNull_atTop_of_forall_free_ultrafilter`.

## What the weight does and does not touch

Only two things in the chain see the weight: the Hilbert-space ultraproduct
`K_ω` (its vectors, hence `cls` and `cls_eq_iff`) and the concluding descent.
The ambient algebra `B_ω = ∏_ω B(K_n)`, the homomorphism `π`, the averaged
operator `h`, its spectral projection `P`, the unitary `V = π s`, the
compression `Q = V P V*` and the identity `Q = P` are all *the same objects at
every weight*, because rescaling the inner product of `K_n` by a positive
constant does not change the operator norm of any operator on `K_n`.  That is
the precise sense in which the manuscript's "applies verbatim" is true, and it
is why KT.10 below never mentions `w`.

The converse warning matters just as much, and it is why this file exists
rather than being a corollary of the dimension-weight one: **the weighted model
is not derivable from its own `w n = card (Y n)` instance.**  Since
`‖ξ‖²_w = matMass ξ / w n`, a family null at the dimension weight need not be
null at `w` when `w n ≪ card (Y n)`; there is a natural map
`K_ω^w → K_ω^card` and none back.  Building the Hilbert-space half at the
dimension weight and retrofitting would build it twice.  Equivalently, and this
is the manuscript's own remark (`Taking $\nu_n=d_n$ gives Theorem`), the
dimension weight recovers
`\ref{thm:kazhdan-transport}` *with the operator-norm bound relaxed to mass
boundedness*, so the weighted statement is strictly stronger and cannot be got
from the unweighted one by rescaling: `y_n = x_n √(d_n/w_n)` is
Hilbert--Schmidt bounded but not operator-norm bounded.

## Coordinates

Everything is indexed by a model family `Y : ℕ → FiniteModel`, never by
`naturalFiniteModel (d n)`, so that the block space `Y¹ n ⊕ Y² n` of the
intertwiner reduction can be substituted directly with no reindexing bridge.
`Y = B.model`, `U = B.map` recovers the `OpAlmostRepresentation` convention of
`Sofic.ScaledKazhdanTransport`; that specialization is
`scaled_transport_both_of_ambient`, the exact statement consumed by
`thm:transport-variants`(2).

The trap of `docs/NOTEPAD.md:548` is avoided exactly as in the unweighted
file: no step uses a Hilbert--Schmidt bound on the *unitaries*.  Almost
multiplicativity of `U_n` is consumed only inside the ambient, in operator
norm, and the only bound placed on `(x_n)` is the printed mass bound, which is
what makes the ultraproduct vector well defined at the weight `w`.
-/

namespace GroupApproximation
namespace UltraproductScaledTransport

open Matrix ScaledKazhdanTransport
open KazhdanAsymptoticCommutant
open scoped Matrix.Norms.L2Operator

/-! ## The renormalized coordinate norms

`matMass X = Tr(X* X)` is the unnormalized squared Frobenius mass.  Giving the
coordinate space `M_{d n}(ℂ)` the inner product `⟨x,y⟩ = Tr(y* x)/w n` makes
its squared norm `matMass X / w n`, so every statement below is a statement
about `matMass X` compared with a multiple of `w n`: this is the manuscript's
"both hypotheses and both conclusions concern only the renormalized norms". -/

/-- The dimension normalization is the weight `w n = d n`: `hsNormSq` is
`matMass` divided by the cardinality of the model. -/
@[simp] theorem hsNormSq_eq_matMass_div (Z : FiniteModel) (A : Matrix Z Z ℂ) :
    hsNormSq Z A = matMass A / (Fintype.card Z : ℝ) := rfl

/-- A matrix of zero Frobenius mass is zero. -/
theorem eq_zero_of_matMass_eq_zero {Z : Type*} [Fintype Z]
    {X : Matrix Z Z ℂ} (h : matMass X = 0) : X = 0 := by
  have hsum : (∑ i : Z, ∑ j : Z, Complex.normSq (X i j)) = 0 := h
  have hnn : ∀ i ∈ (Finset.univ : Finset Z),
      0 ≤ ∑ j : Z, Complex.normSq (X i j) :=
    fun i _ ↦ Finset.sum_nonneg fun j _ ↦ Complex.normSq_nonneg (X i j)
  have hentry : ∀ i j : Z, X i j = 0 := by
    intro i j
    have hrow : (∑ j : Z, Complex.normSq (X i j)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
    have hnn' : ∀ j ∈ (Finset.univ : Finset Z), 0 ≤ Complex.normSq (X i j) :=
      fun j _ ↦ Complex.normSq_nonneg (X i j)
    have h0 : Complex.normSq (X i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn').mp hrow j (Finset.mem_univ j)
    exact Complex.normSq_eq_zero.mp h0
  ext i j
  simp [hentry i j]

/-- **"An index with `w_n = 0` forces `x_n = 0`."**  The printed proof's first
sentence: the renormalized inner product is only defined where the weight is
positive, and the mass bound makes the coordinate vanish everywhere else, so
nothing is lost by ignoring those indices.

This is also exactly the tolerance that `docs/COLLAPSE_STEP_AUDIT.md` §4 asks
of the weighted transport: the collapse weight `k_n` is positive only
eventually. -/
theorem eq_zero_of_weight_zero {Z : Type*} [Fintype Z] {X : Matrix Z Z ℂ}
    {C c : ℝ} (h : matMass X ≤ C * c) (hc : c = 0) : X = 0 := by
  refine eq_zero_of_matMass_eq_zero (le_antisymm ?_ (matMass_nonneg X))
  rw [hc, mul_zero] at h
  exact h

/-- **"Conjugation by a unitary is unitary for every weight."**  The adjoint
action `X ↦ U X U*` preserves `matMass` exactly, hence preserves the
renormalized norm `matMass / w n` for every weight at once. -/
theorem kt_01_matMass_adjoint {Z : Type*} [Fintype Z] [DecidableEq Z]
    {V : Matrix Z Z ℂ} (hV : V ∈ Matrix.unitaryGroup Z ℂ) (X : Matrix Z Z ℂ) :
    matMass (V * X * Vᴴ) = matMass X :=
  matMass_unitary_conj hV X

/-- The reverse adjoint action `X ↦ U* X U` likewise preserves `matMass`, and
hence the renormalized norm at every weight.  The printed conclusion of (1)
names this conjugate too. -/
theorem kt_01_matMass_coadjoint {Z : Type*} [Fintype Z] [DecidableEq Z]
    {V : Matrix Z Z ℂ} (hV : V ∈ Matrix.unitaryGroup Z ℂ) (X : Matrix Z Z ℂ) :
    matMass (Vᴴ * X * V) = matMass X := by
  have hVH : Vᴴ ∈ Matrix.unitaryGroup Z ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hV
  have h := matMass_unitary_conj hVH X
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-! ## The two printed conditions, at an arbitrary weight -/

/-- The manuscript's mass bound `Tr(x_n* x_n) ≤ C w_n`. -/
def WeightBounded (Y : ℕ → FiniteModel) (w : ℕ → ℝ) (C : ℝ)
    (ξ : ∀ n, Matrix (Y n) (Y n) ℂ) : Prop :=
  ∀ n, matMass (ξ n) ≤ C * w n

/-- The manuscript's defect condition at weight `w`: for every `ε > 0`,
eventually `Tr|y_n|² ≤ ε w_n`.  Stated at a general filter so that the
manuscript's `atTop` hypotheses can be pushed to the ultrafilter `ω`. -/
def WeightNull (Y : ℕ → FiniteModel) (w : ℕ → ℝ) (l : Filter ℕ)
    (y : ∀ n, Matrix (Y n) (Y n) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, matMass (y n) ≤ ε * w n

namespace WeightNull

variable {Y : ℕ → FiniteModel} {w : ℕ → ℝ} {l l' : Filter ℕ}

/-- The condition only sees the coordinate masses. -/
theorem congr {y z : ∀ n, Matrix (Y n) (Y n) ℂ} (hy : WeightNull Y w l y)
    (h : ∀ n, matMass (z n) = matMass (y n)) : WeightNull Y w l z :=
  fun ε hε ↦ (hy ε hε).mono fun n hn ↦ by rw [h n]; exact hn

/-- A finer filter inherits the condition; this is how the manuscript's
`atTop` hypotheses become hypotheses along the ultrafilter `ω`. -/
theorem mono {y : ∀ n, Matrix (Y n) (Y n) ℂ} (hy : WeightNull Y w l y)
    (h : l' ≤ l) : WeightNull Y w l' y :=
  fun ε hε ↦ Filter.Eventually.filter_mono h (hy ε hε)

/-- Reversing a difference does not change the condition. -/
theorem sub_symm {ξ η : ∀ n, Matrix (Y n) (Y n) ℂ}
    (h : WeightNull Y w l (fun n ↦ ξ n - η n)) :
    WeightNull Y w l (fun n ↦ η n - ξ n) := by
  refine h.congr fun n ↦ ?_
  show matMass (η n - ξ n) = matMass (ξ n - η n)
  rw [show η n - ξ n = -(ξ n - η n) by abel]
  exact matMass_neg _

end WeightNull

/-! ## The interface produced by manuscript steps KT.01--KT.09, at weight `w`

This is `UltraproductAdjointModel` of `Sofic.UltraproductKazhdanTransport`,
field for field, with the dimension normalization `hsNormSq` replaced
throughout by the renormalized norm at the weight `w`.  Only `cls_eq_iff` --- the
description of the Hilbert-space ultraproduct `K_ω` --- actually changes: the
ambient algebra `B_ω`, the homomorphism `π`, the projection `P` and the
absorption identities are literally weight-independent, because rescaling the
inner product of a Hilbert space by a positive constant leaves the operator
norm, hence the algebra `B(K_n)` and its norm ultraproduct, unchanged.

One field is added relative to the unweighted interface, `act_star_pi_cls`,
because the printed conclusion of `thm:transport-variants`(1) asserts the
statement for `U_n(s)* x_n U_n(s)` as well as for `U_n(s) x_n U_n(s)*`.  It is
not a new hypothesis about the theorem: the adjoint of the unitary `Ad U_n(g)`
of `K_n` is exactly `Ad (U_n(g)*)`, coordinate by coordinate.

**This signature is frozen** while the construction is built against it, and
**no instance exists yet** — see the status section of the module docstring. -/
structure WeightedUltraproductAdjointModel
    {Γ : Type} {H : Type*} [Group Γ] [Group H]
    (iota : Γ →* H) (s : H) (Y : ℕ → FiniteModel)
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (w : ℕ → ℝ) (ω : Ultrafilter ℕ) where
  /-- KT.03: the carrier of the norm ultraproduct `B_ω = ∏_ω B(K_n)`.  It does
  not depend on the weight. -/
  Alg : Type
  /-- `B_ω` is a ring. -/
  [ring : Ring Alg]
  /-- `B_ω` is a star ring. -/
  [starRing : StarRing Alg]
  /-- KT.06: `B_ω` is finite, i.e. `σ*σ = 1` forces `σσ* = 1`.  At the real
  ambient `NormMatrixCStarCorona X` this is
  `Sofic.UltraproductDedekindFinite.normMatrixCStarCorona_isDedekindFiniteMonoid`. -/
  [dedekindFinite : IsDedekindFiniteMonoid Alg]
  /-- KT.02: the carrier of the Hilbert-space ultraproduct `K_ω` built from the
  renormalized inner products `⟨x,y⟩ = Tr(y* x)/w n`. -/
  Vec : Type
  /-- KT.03: the action of `B_ω` on `K_ω`. -/
  act : Alg → Vec → Vec
  /-- The action is an action of the multiplicative structure. -/
  act_mul : ∀ (a b : Alg) (ζ : Vec), act (a * b) ζ = act a (act b ζ)
  /-- KT.02: the class `[ξ_n]_ω` of a family of matrices read as vectors of the
  renormalized coordinate spaces. -/
  cls : (∀ n, Matrix (Y n) (Y n) ℂ) → Vec
  /-- KT.02 and KT.04, at the weight `w`: two families with the printed mass
  bound have the same class exactly when their difference satisfies the printed
  defect condition along `ω`.  This is the only field in which the weight
  appears, and it is the manuscript's "the mass bound defines the ultraproduct
  vector". -/
  cls_eq_iff : ∀ (C : ℝ) (ξ η : ∀ n, Matrix (Y n) (Y n) ℂ),
      WeightBounded Y w C ξ → WeightBounded Y w C η →
      (cls ξ = cls η ↔ WeightNull Y w (ω : Filter ℕ) (fun n ↦ ξ n - η n))
  /-- KT.05: `π : H → U(B_ω)`, `π g = [Ad U_n g]_ω`, is a homomorphism. -/
  pi : H →* Alg
  /-- KT.05: `π` is a star homomorphism, so every `π g` is a unitary. -/
  pi_star : ∀ g : H, star (pi g) = pi g⁻¹
  /-- KT.01 and KT.03: `π g` acts on classes by the ultraproduct of the adjoint
  actions `Ad U_n(g) ξ = U_n(g) ξ U_n(g)*`. -/
  act_pi_cls : ∀ (g : H) (ξ : ∀ n, Matrix (Y n) (Y n) ℂ),
      act (pi g) (cls ξ) =
        cls (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
          (U n g : Matrix (Y n) (Y n) ℂ)ᴴ)
  /-- KT.01 and KT.03, adjoint form: the adjoint of the unitary `Ad U_n(g)` of
  `K_n` is `Ad (U_n(g)*)`, so `(π g)*` acts by the reverse conjugation.  This is
  what the *second* conclusion of the printed statement needs.  It is guarded by
  the mass bound, exactly like `cls_eq_iff`: the coordinate identity
  `star (Ad U_n(g)) = Ad (U_n(g)*)` is exact, and the passage from `π g⁻¹` to
  `(π g)*` costs only the operator-norm defect `‖U_n(g⁻¹) - U_n(g)*‖ → 0`, which
  moves a mass-bounded class by a null amount at every weight. -/
  act_star_pi_cls : ∀ (C : ℝ) (g : H) (ξ : ∀ n, Matrix (Y n) (Y n) ℂ),
      WeightBounded Y w C ξ →
      act (star (pi g)) (cls ξ) =
        cls (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ)ᴴ * ξ n *
          (U n g : Matrix (Y n) (Y n) ℂ))
  /-- KT.08: the Kazhdan projection, the spectral projection of the averaged
  operator `h` at its isolated spectral point `1`. -/
  P : Alg
  /-- The Kazhdan projection is self-adjoint. -/
  P_star : star P = P
  /-- The Kazhdan projection is idempotent. -/
  P_mul_P : P * P = P
  /-- KT.07 and KT.08: `P` projects onto `Fix`, the subspace of vectors fixed by
  every `π(ι γ)`.  Both directions are used: `←` places `ξ` in `Fix` at the
  start of the concluding paragraph, and `→` takes `V ξ ∈ ran P` back to "fixed
  by every `π(ι γ)`" at the end, which is the asserted vanishing.

  Construction note.  Both directions come from one algebraic identity, with no
  Hilbert structure and at every weight at once: the resolvent factorisation
  `Analysis.KazhdanProjectionAbsorption.one_sub_spectralProjection_eq`,
  `1 - spectralProjection m c = cfc (gapResolvent c) m * (1 - m)`, applied to
  the averaged operator `m = h`.  Together with `ℂ`-linearity of `act` in the
  algebra argument it gives `(1 - P) ζ` as a bounded multiple of `(1 - h) ζ`,
  which is what makes the equivalence weight-blind: nothing in it refers to
  `w`, so it holds at the dimension weight and at a rank weight by the same
  proof. -/
  act_P_iff : ∀ ζ : Vec, act P ζ = ζ ↔ ∀ γ : Γ, act (pi (iota γ)) ζ = ζ
  /-- KT.09: `Fix ⊆ V·Fix` read as `P ≤ Q`, first absorption identity. -/
  P_mul_conjugate : P * (pi s * P * star (pi s)) = P
  /-- KT.09: `Fix ⊆ V·Fix` read as `P ≤ Q`, second absorption identity. -/
  conjugate_mul_P : (pi s * P * star (pi s)) * P = P

attribute [instance] WeightedUltraproductAdjointModel.ring
  WeightedUltraproductAdjointModel.starRing
  WeightedUltraproductAdjointModel.dedekindFinite

namespace WeightedUltraproductAdjointModel

variable {Γ : Type} {H : Type*} [Group Γ] [Group H]
  {iota : Γ →* H} {s : H} {Y : ℕ → FiniteModel}
  {U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ}
  {w : ℕ → ℝ} {ω : Ultrafilter ℕ}
  (D : WeightedUltraproductAdjointModel iota s Y U w ω)

/-- Every `π g` is a unitary of `B_ω`: the left inverse identity. -/
theorem star_pi_mul_pi (g : H) : star (D.pi g) * D.pi g = 1 := by
  rw [D.pi_star, ← map_mul]
  simp

/-- Every `π g` is a unitary of `B_ω`: the right inverse identity. -/
theorem pi_mul_star_pi (g : H) : D.pi g * star (D.pi g) = 1 := by
  rw [D.pi_star, ← map_mul]
  simp

/-- **KT.10, unchanged by the weight.**  With `V = π s` and `Q = V P V*`, the
one-sided containment `P ≤ Q` of KT.09 and finiteness of `B_ω` force `Q = P`.

Neither the statement nor the proof mentions `w`: `B_ω`, `π`, `P` and the
absorption identities are the same objects at every weight, which is exactly
why the printed proof of (1) can say that the ultraproduct proof of
`thm:kazhdan-transport` applies verbatim. -/
theorem kt_10_conjugate_eq : D.pi s * D.P * star (D.pi s) = D.P :=
  ProperProjectionCompression.unitary_conjugate_eq_of_absorbs
    D.P_star D.P_mul_P (D.star_pi_mul_pi s) (D.pi_mul_star_pi s)
    D.P_mul_conjugate D.conjugate_mul_P

/-- "Finiteness reverses the one-sided compression", first direction: `Q = P`
says that `V` commutes with `P`, which turns `ξ ∈ Fix` into `V ξ ∈ Fix`. -/
theorem pi_mul_P : D.pi s * D.P = D.P * D.pi s := by
  calc D.pi s * D.P
      = D.pi s * D.P * (star (D.pi s) * D.pi s) := by
        rw [D.star_pi_mul_pi s, mul_one]
    _ = (D.pi s * D.P * star (D.pi s)) * D.pi s := by noncomm_ring
    _ = D.P * D.pi s := by rw [D.kt_10_conjugate_eq]

/-- "Finiteness reverses the one-sided compression", **second direction**: the
same identity `Q = P`, starred, says that `V*` commutes with `P`, which turns
`ξ ∈ Fix` into `V* ξ ∈ Fix`.  This is the half of the printed conclusion that
concerns `U_n(s)* x_n U_n(s)`, and it is why that conclusion costs nothing
beyond the first. -/
theorem star_pi_mul_P : star (D.pi s) * D.P = D.P * star (D.pi s) := by
  have h := congrArg star D.pi_mul_P
  rw [star_mul, star_mul, D.P_star] at h
  exact h.symm

/-- **KT.26.**  `V·Fix ⊆ ran P`: a vector fixed by the Kazhdan projection is
still fixed by it after applying `V = π(s)`.  This is where `Q = P` is
consumed, and it is the step that turns the one-sided compression into the
conclusion. -/
theorem act_P_shift_of_act_P {ζ : D.Vec} (hζ : D.act D.P ζ = ζ) :
    D.act D.P (D.act (D.pi s) ζ) = D.act (D.pi s) ζ := by
  rw [← D.act_mul, ← D.pi_mul_P, D.act_mul, hζ]

/-- **KT.26, adjoint form.**  `V*·Fix ⊆ ran P`, from the starred identity.  It
is the half of the printed conclusion concerning `U_n(s)* x_n U_n(s)`. -/
theorem act_P_star_shift_of_act_P {ζ : D.Vec} (hζ : D.act D.P ζ = ζ) :
    D.act D.P (D.act (star (D.pi s)) ζ) = D.act (star (D.pi s)) ζ := by
  rw [← D.act_mul, ← D.star_pi_mul_P, D.act_mul, hζ]

/-- **The fixed-vector dictionary at the weight `w`.**  For a family `ξ` with
the printed mass bound, the class `[ξ_n]_ω` is fixed by `π g` exactly when the
adjoint displacements `ξ_n - U_n(g) ξ_n U_n(g)*` satisfy the printed defect
condition along `ω`.

This is the manuscript's use of unitary invariance, in both directions: at the
start of the concluding paragraph to place `ξ` in `Fix`, and at the end to read
the membership back off as the asserted vanishing.  Nothing but
`kt_01_matMass_adjoint` --- "conjugation by a unitary is unitary for every
weight" --- is needed to move it from the dimension normalization to `w`. -/
theorem act_pi_cls_eq_iff (C : ℝ) (ξ : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hξ : WeightBounded Y w C ξ) (g : H) :
    D.act (D.pi g) (D.cls ξ) = D.cls ξ ↔
      WeightNull Y w (ω : Filter ℕ)
        (fun n ↦ ξ n - (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
          (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) := by
  have hconj : WeightBounded Y w C
      (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) := by
    intro n
    show matMass ((U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
      (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) ≤ C * w n
    rw [kt_01_matMass_adjoint (U n g).2]
    exact hξ n
  -- the manuscript writes the displacement as `x_n - U_n(γ) x_n U_n(γ)*`, so
  -- the class identity is taken in that order
  have hkey := D.cls_eq_iff C ξ
    (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
      (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) hξ hconj
  constructor
  · intro hfix
    have h1 : D.cls ξ = D.cls (fun n ↦ (U n g : Matrix (Y n) (Y n) ℂ) * ξ n *
        (U n g : Matrix (Y n) (Y n) ℂ)ᴴ) := by
      rw [← D.act_pi_cls g ξ]
      exact hfix.symm
    exact hkey.mp h1
  · intro hnull
    rw [D.act_pi_cls g ξ]
    exact (hkey.mpr hnull).symm

include D in
/-- **KT.11 at the weight `w`, in both directions.**

Let `ξ = [ξ_n]_ω` be the class of the family `x`, which the printed mass bound
makes well defined.  By unitary invariance of the renormalized norm the defect
hypothesis says exactly that every `π(ι γ)` fixes `ξ`, so `ξ ∈ Fix = ran P`.
Finiteness has already forced `Q = P`, so `V` and `V*` both commute with `P`;
hence `V ξ` and `V* ξ` lie in `Fix` as well.  The vectors of
`U_n(s) x_n U_n(s)*` and of `U_n(s)* x_n U_n(s)` are `Ad U_n(s) ξ_n` and
`Ad U_n(s)* ξ_n`, so, again by unitary invariance, both conjugated families
satisfy the printed defect condition along `ω`. -/
theorem kt_11_descend_at_every_weight (C : ℝ) (x : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hx : WeightBounded Y w C x)
    (hdefect : ∀ γ : Γ, WeightNull Y w (ω : Filter ℕ)
      (fun n ↦ x n - (U n (iota γ) : Matrix (Y n) (Y n) ℂ) * x n *
        (U n (iota γ) : Matrix (Y n) (Y n) ℂ)ᴴ)) :
    (∀ γ : Γ, WeightNull Y w (ω : Filter ℕ) (fun n ↦
        (U n s : Matrix (Y n) (Y n) ℂ) * x n *
            (U n s : Matrix (Y n) (Y n) ℂ)ᴴ -
          (U n (iota γ) : Matrix (Y n) (Y n) ℂ) *
            ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
              (U n s : Matrix (Y n) (Y n) ℂ)ᴴ) *
            (U n (iota γ) : Matrix (Y n) (Y n) ℂ)ᴴ)) ∧
      ∀ γ : Γ, WeightNull Y w (ω : Filter ℕ) (fun n ↦
        (U n s : Matrix (Y n) (Y n) ℂ)ᴴ * x n *
            (U n s : Matrix (Y n) (Y n) ℂ) -
          (U n (iota γ) : Matrix (Y n) (Y n) ℂ) *
            ((U n s : Matrix (Y n) (Y n) ℂ)ᴴ * x n *
              (U n s : Matrix (Y n) (Y n) ℂ)) *
            (U n (iota γ) : Matrix (Y n) (Y n) ℂ)ᴴ) := by
  -- the two conjugated families carry the same mass bound
  have hy : WeightBounded Y w C (fun n ↦ (U n s : Matrix (Y n) (Y n) ℂ) * x n *
      (U n s : Matrix (Y n) (Y n) ℂ)ᴴ) := by
    intro n
    show matMass ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
      (U n s : Matrix (Y n) (Y n) ℂ)ᴴ) ≤ C * w n
    rw [kt_01_matMass_adjoint (U n s).2]
    exact hx n
  have hz : WeightBounded Y w C (fun n ↦ (U n s : Matrix (Y n) (Y n) ℂ)ᴴ * x n *
      (U n s : Matrix (Y n) (Y n) ℂ)) := by
    intro n
    show matMass ((U n s : Matrix (Y n) (Y n) ℂ)ᴴ * x n *
      (U n s : Matrix (Y n) (Y n) ℂ)) ≤ C * w n
    rw [kt_01_matMass_coadjoint (U n s).2]
    exact hx n
  -- ξ ∈ Fix
  have hfix : D.act D.P (D.cls x) = D.cls x :=
    (D.act_P_iff (D.cls x)).mpr fun γ ↦
      (D.act_pi_cls_eq_iff C x hx (iota γ)).mpr (hdefect γ)
  constructor
  · -- V ξ ∈ Fix
    have hVfix : D.act D.P (D.act (D.pi s) (D.cls x))
        = D.act (D.pi s) (D.cls x) := D.act_P_shift_of_act_P hfix
    have hall := (D.act_P_iff (D.act (D.pi s) (D.cls x))).mp hVfix
    rw [D.act_pi_cls s x] at hall
    intro γ
    exact (D.act_pi_cls_eq_iff C
      (fun n ↦ (U n s : Matrix (Y n) (Y n) ℂ) * x n *
        (U n s : Matrix (Y n) (Y n) ℂ)ᴴ) hy (iota γ)).mp (hall γ)
  · -- V* ξ ∈ Fix
    have hVfix : D.act D.P (D.act (star (D.pi s)) (D.cls x))
        = D.act (star (D.pi s)) (D.cls x) := D.act_P_star_shift_of_act_P hfix
    have hall := (D.act_P_iff (D.act (star (D.pi s)) (D.cls x))).mp hVfix
    rw [D.act_star_pi_cls C s x hx] at hall
    intro γ
    exact (D.act_pi_cls_eq_iff C
      (fun n ↦ (U n s : Matrix (Y n) (Y n) ℂ)ᴴ * x n *
        (U n s : Matrix (Y n) (Y n) ℂ)) hz (iota γ)).mp (hall γ)

end WeightedUltraproductAdjointModel

/-! ## The manuscript's contradiction skeleton, at the weight

The printed proof of `thm:kazhdan-transport` assumes the conclusion fails on an
infinite set `I`, fixes a free ultrafilter `ω` with `I ∈ ω`, derives the
vanishing along `ω`, and contradicts `I ∈ ω`.  At the weight `w` the failing
set is `{n | ε w n < Tr|y_n|²}`, and the same skeleton runs. -/

/-- If the printed defect condition holds along every free ultrafilter, it
holds along `atTop`, which is the manuscript's "since the failing subsequence
was arbitrary, the full sequence converges". -/
theorem weightNull_atTop_of_forall_free_ultrafilter
    {Y : ℕ → FiniteModel} (w : ℕ → ℝ) (y : ∀ n, Matrix (Y n) (Y n) ℂ)
    (h : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
      WeightNull Y w (ω : Filter ℕ) y) :
    WeightNull Y w Filter.atTop y := by
  intro ε hε
  rw [Filter.eventually_atTop]
  by_contra hcon
  push Not at hcon
  -- `hcon` is the manuscript's infinite bad set `I`, presented cofinally.
  choose sel hselge hselbad using hcon
  have hid : Filter.Tendsto (fun n : ℕ ↦ n) Filter.atTop Filter.atTop :=
    Filter.tendsto_id
  have hseltop : Filter.Tendsto sel Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ (hselge n : n ≤ sel n)) hid
  haveI : (Filter.map sel Filter.atTop).NeBot := inferInstance
  -- a free ultrafilter containing the bad set
  let ω : Ultrafilter ℕ := Ultrafilter.of (Filter.map sel Filter.atTop)
  have hωle : (ω : Filter ℕ) ≤ Filter.map sel Filter.atTop :=
    Ultrafilter.of_le (Filter.map sel Filter.atTop)
  have hωcof : (ω : Filter ℕ) ≤ Filter.cofinite := by
    refine le_trans hωle ?_
    rw [Nat.cofinite_eq_atTop]
    exact hseltop
  have hbad : {n : ℕ | ε * w n < matMass (y n)} ∈ (ω : Filter ℕ) := by
    have hmem : {n : ℕ | ε * w n < matMass (y n)} ∈
        Filter.map sel Filter.atTop := by
      rw [Filter.mem_map]
      have huniv : sel ⁻¹' {n : ℕ | ε * w n < matMass (y n)} = Set.univ := by
        ext k
        simp [hselbad k]
      rw [huniv]
      exact Filter.univ_mem
    exact hωle hmem
  have hgood : ∀ᶠ n in (ω : Filter ℕ), matMass (y n) ≤ ε * w n := h ω hωcof ε hε
  have hbadev : ∀ᶠ n in (ω : Filter ℕ), ε * w n < matMass (y n) :=
    Filter.eventually_iff.mpr hbad
  obtain ⟨n, hn1, hn2⟩ := (hbadev.and hgood).exists
  exact absurd hn2 (not_le.mpr hn1)

/-! ## The printed statement of `thm:transport-variants`(1) -/

/-- **Transport at every Hilbertian scale.**
`non_mf_groups_exist.tex`, Theorem `\ref{thm:transport-variants}`, part (1),
with its printed proof.

Let `Γ`, `H`, `ι`, `s` be as in `thm:kazhdan-transport`, let `(U_n)` be as
there, let `(w_n)` be nonnegative weights, suppose `Tr(x_n* x_n) ≤ C w_n` for
all `n`, and suppose that for every `γ` and every `ε > 0`, eventually
`Tr |x_n - U_n(ι γ) x_n U_n(ι γ)*|² ≤ ε w_n`.  Then `U_n(s) x_n U_n(s)*` **and**
`U_n(s)* x_n U_n(s)` satisfy both conditions as well, with the same constant
`C`.

The proof is the printed one.  The mass bound is preserved because conjugation
by a unitary is unitary for every weight; the defect condition is transported
by the ultraproduct proof of `thm:kazhdan-transport` run at the weight `w`,
whose ambient is `WeightedUltraproductAdjointModel`; and both directions come
out because finiteness of `B_ω` reverses the one-sided compression
(`kt_10_conjugate_eq`), giving `V P V* = P` and hence commutation of `P` with
both `V` and `V*`.

**Not badgeable as it stands**: `ambient` has no instance in the repository, so
this statement is currently vacuous.  See the status section of the module
docstring. -/
theorem transport_variants_one
    {Γ : Type} {H : Type*} [Group Γ] [Group H]
    (iota : Γ →* H) (s : H) (Y : ℕ → FiniteModel)
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (w : ℕ → ℝ) (_hw : ∀ n, 0 ≤ w n) (C : ℝ)
    (x : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hmass : WeightBounded Y w C x)
    (hdefect : ∀ γ : Γ, WeightNull Y w Filter.atTop
      (fun n ↦ x n - (U n (iota γ) : Matrix (Y n) (Y n) ℂ) * x n *
        (U n (iota γ) : Matrix (Y n) (Y n) ℂ)ᴴ))
    (ambient : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
      WeightedUltraproductAdjointModel iota s Y U w ω) :
    (WeightBounded Y w C (fun n ↦ (U n s : Matrix (Y n) (Y n) ℂ) * x n *
          (U n s : Matrix (Y n) (Y n) ℂ)ᴴ) ∧
        ∀ γ : Γ, WeightNull Y w Filter.atTop (fun n ↦
          (U n s : Matrix (Y n) (Y n) ℂ) * x n *
              (U n s : Matrix (Y n) (Y n) ℂ)ᴴ -
            (U n (iota γ) : Matrix (Y n) (Y n) ℂ) *
              ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
                (U n s : Matrix (Y n) (Y n) ℂ)ᴴ) *
              (U n (iota γ) : Matrix (Y n) (Y n) ℂ)ᴴ)) ∧
      (WeightBounded Y w C (fun n ↦ (U n s : Matrix (Y n) (Y n) ℂ)ᴴ * x n *
            (U n s : Matrix (Y n) (Y n) ℂ)) ∧
        ∀ γ : Γ, WeightNull Y w Filter.atTop (fun n ↦
          (U n s : Matrix (Y n) (Y n) ℂ)ᴴ * x n *
              (U n s : Matrix (Y n) (Y n) ℂ) -
            (U n (iota γ) : Matrix (Y n) (Y n) ℂ) *
              ((U n s : Matrix (Y n) (Y n) ℂ)ᴴ * x n *
                (U n s : Matrix (Y n) (Y n) ℂ)) *
              (U n (iota γ) : Matrix (Y n) (Y n) ℂ)ᴴ)) := by
  have hωtop : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
      (ω : Filter ℕ) ≤ Filter.atTop := by
    intro ω hωcof
    rw [← Nat.cofinite_eq_atTop]
    exact hωcof
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro n
    show matMass ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
      (U n s : Matrix (Y n) (Y n) ℂ)ᴴ) ≤ C * w n
    rw [kt_01_matMass_adjoint (U n s).2]
    exact hmass n
  · intro γ
    refine weightNull_atTop_of_forall_free_ultrafilter w _ ?_
    intro ω hωcof
    exact ((ambient ω hωcof).kt_11_descend_at_every_weight C x hmass
      (fun γ' ↦ (hdefect γ').mono (hωtop ω hωcof))).1 γ
  · intro n
    show matMass ((U n s : Matrix (Y n) (Y n) ℂ)ᴴ * x n *
      (U n s : Matrix (Y n) (Y n) ℂ)) ≤ C * w n
    rw [kt_01_matMass_coadjoint (U n s).2]
    exact hmass n
  · intro γ
    refine weightNull_atTop_of_forall_free_ultrafilter w _ ?_
    intro ω hωcof
    exact ((ambient ω hωcof).kt_11_descend_at_every_weight C x hmass
      (fun γ' ↦ (hdefect γ').mono (hωtop ω hωcof))).2 γ

/-! ## Part (1) in the `OpAlmostRepresentation` vocabulary

`Sofic.ScaledKazhdanTransport` states the same two conditions as
`IsScaledMassBounded` and `IsScaledAsymptoticCommutantOf`, over an
`OpAlmostRepresentation`.  Taking `Y = B.model` and `U = B.map` turns
`transport_variants_one` into exactly that statement, which is the form the
intertwiner reduction of `thm:transport-variants`(2) consumes. -/

/-- The printed defect condition along `atTop` is `ScaledMassVanishing`. -/
theorem weightNull_atTop_iff_scaledMassVanishing
    {E : Type} [Group E] (B : OpAlmostRepresentation E) (w : ℕ → ℝ)
    (y : ∀ n, Matrix (B.model n) (B.model n) ℂ) :
    WeightNull B.model w Filter.atTop y ↔ ScaledMassVanishing B w y := by
  constructor
  · intro h ε hε
    exact Filter.eventually_atTop.mp (h ε hε)
  · intro h ε hε
    exact Filter.eventually_atTop.mpr (h ε hε)

/-- **`thm:transport-variants`(1) in coordinate form.**  A one-sided compressor
of a Kazhdan image acts in both directions on the `w`-mass-bounded, `w`-scaled
asymptotic commutant, for every nonnegative weight, by the printed ultraproduct
proof.  This is the same assertion as
`ScaledKazhdanTransport.scaled_transport_both`, by the printed ultraproduct
route rather than by the finite-stage equal-rank route.

This is the shape specified for the collapse proof by
`docs/COLLAPSE_STEP_AUDIT.md` §4, route (b): the qualitative `∀ ε` form at an
arbitrary weight, tolerating `w n = 0` at finitely many stages (there the mass
bound forces `x n = 0`, which is the manuscript's own convention --- see
`eq_zero_of_weight_zero`).  It still needs the diagonalization lemma of that
section to be usable there, and **it is not badgeable until `ambient` has an
instance**; until then `ScaledKazhdanTransport.scaled_transport_both` remains
the only proved form of this assertion, by the finite-stage route. -/
theorem scaled_transport_both_of_ambient
    {Γ E : Type} [Group Γ] [Group E]
    (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (iota : Γ →* E) (t : E)
    (ambient : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
      WeightedUltraproductAdjointModel iota t B.model B.map w ω)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsScaledAsymptoticCommutantOf B w iota x)
    (hbound : IsScaledMassBounded B w x) :
    IsScaledAsymptoticCommutantOf B w iota (adjointSequence B t x) ∧
      IsScaledAsymptoticCommutantOf B w iota (coadjointSequence B t x) := by
  obtain ⟨C, _hC0, hC⟩ := hbound
  have hmass : WeightBounded B.model w C x := hC
  have hdefect : ∀ γ : Γ, WeightNull B.model w Filter.atTop
      (fun n ↦ x n - (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
        x n * (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ) :=
    fun γ ↦ (weightNull_atTop_iff_scaledMassVanishing B w _).mpr (hx γ)
  have hmain := transport_variants_one iota t B.model B.map w hw C x
    hmass hdefect ambient
  refine ⟨fun γ ↦ ?_, fun γ ↦ ?_⟩
  · exact (weightNull_atTop_iff_scaledMassVanishing B w _).mp (hmain.1.2 γ)
  · exact (weightNull_atTop_iff_scaledMassVanishing B w _).mp (hmain.2.2 γ)

/-! ## The dimension weight

`non_mf_groups_exist.tex`, the remark after the proof of
`\ref{thm:transport-variants}`: "Taking `\nu_n=d_n` gives
Theorem `\ref{thm:kazhdan-transport}` with the uniform operator-norm bound
relaxed to a uniform bound on `\operatorname{Tr}(x_n^*x_n)/d_n`."  (The
manuscript writes the weight `\nu_n`; this file writes it `w`.) -/

/-- At the dimension weight the printed mass bound is the normalized
Hilbert--Schmidt bound. -/
theorem matMass_le_iff_hsNormSq_le (Z : FiniteModel) (hZ : 0 < Fintype.card Z)
    (A : Matrix Z Z ℂ) (c : ℝ) :
    matMass A ≤ c * (Fintype.card Z : ℝ) ↔ hsNormSq Z A ≤ c := by
  have hpos : (0 : ℝ) < (Fintype.card Z : ℝ) := by exact_mod_cast hZ
  rw [hsNormSq_eq_matMass_div, div_le_iff₀ hpos]

/-- At the dimension weight the printed defect condition is exactly normalized
Hilbert--Schmidt convergence to zero. -/
theorem weightNull_dimension_iff_tendsto {Y : ℕ → FiniteModel}
    (hY : ∀ n, 0 < Fintype.card (Y n)) (y : ∀ n, Matrix (Y n) (Y n) ℂ) :
    WeightNull Y (fun n ↦ (Fintype.card (Y n) : ℝ)) Filter.atTop y ↔
      Filter.Tendsto (fun n ↦ hsNormSq (Y n) (y n)) Filter.atTop (nhds 0) := by
  have hdist : ∀ n : ℕ, dist (hsNormSq (Y n) (y n)) 0 = hsNormSq (Y n) (y n) := by
    intro n
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNormSq_nonneg _ _)]
  constructor
  · intro h
    rw [Metric.tendsto_atTop]
    intro δ hδ
    have hhalf : (0 : ℝ) < δ / 2 := by linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h (δ / 2) hhalf)
    refine ⟨N, fun n hn ↦ ?_⟩
    have h1 : hsNormSq (Y n) (y n) ≤ δ / 2 :=
      (matMass_le_iff_hsNormSq_le (Y n) (hY n) (y n) (δ / 2)).mp (hN n hn)
    show dist (hsNormSq (Y n) (y n)) 0 < δ
    rw [hdist n]
    linarith
  · intro h ε hε
    rw [Filter.eventually_atTop]
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have h1 : dist (hsNormSq (Y n) (y n)) 0 < ε := hN n hn
    rw [hdist n] at h1
    exact (matMass_le_iff_hsNormSq_le (Y n) (hY n) (y n) ε).mpr h1.le

/-- The printed identification of the adjoint displacement with the commutator,
in the normalized Hilbert--Schmidt norm. -/
theorem hsNormSq_displacement_eq_commutator (Z : FiniteModel)
    {W : Matrix Z Z ℂ} (hW : W ∈ Matrix.unitaryGroup Z ℂ) (A : Matrix Z Z ℂ) :
    hsNormSq Z (A * W - W * A) = hsNormSq Z (A - W * A * Wᴴ) := by
  have h1 := hsNormSq_adjoint_sub Z hW A
  have h2 : A - W * A * Wᴴ = -(W * A * Wᴴ - A) := by abel
  rw [← h1, h2, hsNormSq_neg]

/-- **The dimension weight recovers `\ref{thm:kazhdan-transport}`, with the
uniform operator-norm bound relaxed to mass boundedness.**
`non_mf_groups_exist.tex`, the remark beginning `Taking $\nu_n=d_n$ gives
Theorem`.

Taking `w n = card (Y n)` in `transport_variants_one` gives back the conclusion
of `thm:kazhdan-transport` --- normalized Hilbert--Schmidt vanishing of the
conjugated commutators --- from a hypothesis that only bounds the normalized
Hilbert--Schmidt norms of `x_n`, not their operator norms.

This is also the reason the weighted statement cannot be obtained from the
unweighted one by rescaling: `y_n = x_n √(d_n / w_n)` is Hilbert--Schmidt
bounded but not operator-norm bounded, so `thm:kazhdan-transport` does not
apply to it.  The ultraproduct argument has to be run at the weight, which is
what this file does.

**Not badgeable as it stands**: inherits the `ambient` hypothesis. -/
theorem dimension_weight_recovers_kazhdan_transport
    {Γ : Type} {H : Type*} [Group Γ] [Group H]
    (iota : Γ →* H) (s : H) (Y : ℕ → FiniteModel)
    (hY : ∀ n, 0 < Fintype.card (Y n))
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (C : ℝ) (x : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hmass : ∀ n, hsNormSq (Y n) (x n) ≤ C)
    (hcomm : ∀ γ : Γ, Filter.Tendsto
      (fun n ↦ hsNormSq (Y n)
        (x n * (U n (iota γ) : Matrix (Y n) (Y n) ℂ) -
          (U n (iota γ) : Matrix (Y n) (Y n) ℂ) * x n))
      Filter.atTop (nhds 0))
    (ambient : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
      WeightedUltraproductAdjointModel iota s Y U
        (fun n ↦ (Fintype.card (Y n) : ℝ)) ω)
    (γ : Γ) :
    Filter.Tendsto
      (fun n ↦ hsNormSq (Y n)
        ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
              (U n s : Matrix (Y n) (Y n) ℂ)ᴴ *
            (U n (iota γ) : Matrix (Y n) (Y n) ℂ) -
          (U n (iota γ) : Matrix (Y n) (Y n) ℂ) *
            ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
              (U n s : Matrix (Y n) (Y n) ℂ)ᴴ)))
      Filter.atTop (nhds 0) := by
  have hmass' : WeightBounded Y (fun n ↦ (Fintype.card (Y n) : ℝ)) C x :=
    fun n ↦ (matMass_le_iff_hsNormSq_le (Y n) (hY n) (x n) C).mpr (hmass n)
  have hdefect : ∀ γ' : Γ,
      WeightNull Y (fun n ↦ (Fintype.card (Y n) : ℝ)) Filter.atTop
        (fun n ↦ x n - (U n (iota γ') : Matrix (Y n) (Y n) ℂ) * x n *
          (U n (iota γ') : Matrix (Y n) (Y n) ℂ)ᴴ) := by
    intro γ'
    refine (weightNull_dimension_iff_tendsto hY _).mpr ?_
    exact Filter.Tendsto.congr
      (fun n ↦ hsNormSq_displacement_eq_commutator (Y n) (U n (iota γ')).2 (x n))
      (hcomm γ')
  have hwnn : ∀ n : ℕ, (0 : ℝ) ≤ (Fintype.card (Y n) : ℝ) :=
    fun n ↦ Nat.cast_nonneg (Fintype.card (Y n))
  have hmain := transport_variants_one iota s Y U
    (fun n ↦ (Fintype.card (Y n) : ℝ)) hwnn C x hmass' hdefect ambient
  have htend := (weightNull_dimension_iff_tendsto hY _).mp (hmain.1.2 γ)
  exact Filter.Tendsto.congr
    (fun n ↦ (hsNormSq_displacement_eq_commutator (Y n) (U n (iota γ)).2
      ((U n s : Matrix (Y n) (Y n) ℂ) * x n *
        (U n s : Matrix (Y n) (Y n) ℂ)ᴴ)).symm)
    htend

end UltraproductScaledTransport
end GroupApproximation
