import GroupApproximation.Analysis.RankNormalizedHilbertization

/-!
# The collapse cocycle inside the rank-normalized ultraproduct

Proof-ledger row `CO.21`, the paragraph *An exact cocycle* in the proof of
`thm:projection-collapse` in `non_mf_groups_exist.tex` (navigate by the
label; the file is under concurrent edit).

The row was split on 2026-08-17: its algebraic half —
`eq:collapse-cocycle`, `d_{gh} = d_g + Θ(g) d_h Θ(g)*` — is
`Analysis/ProjectionOrbitCollapse.sub_conj_mul`, proved in an arbitrary ring
with involution.  Its analytic half was recorded as *the whole difficulty*:
the point of the printed step is that `Λ` is defined at all, that the
conjugation representation `π(h) = [Ad U_n(h)]_ω` acts on the
rank-normalized ultraproduct, and that `β(g) = Λ(d_g)` is a cocycle **there**
rather than in an abstract ring.

`Analysis/RankNormalizedHilbertization` supplies the first of those.  This
file supplies the second and third:

* `conjBounded` is `Ad U_n` on the numerator `massBounded Y w`, a
  `ℂ`-linear endomorphism — well defined because unitary conjugation is mass
  exact;
* `conjQ` is its descent to the ultraproduct `Vec Y w ω`, obtained from
  `Submodule.mapQ` and the fact that conjugation also preserves the
  denominator `massNull`.  This is the printed *"conjugation by a unitary
  preserves each `⟨·,·⟩_n` … so `π(h) = [Ad U_n(h)]_ω` defines a unitary
  representation of `H` on `K_ω`"*, at the level at which it is used: `π(h)`
  is a well-defined linear operator on the ultraproduct;
* `coordinate_cocycle` is `eq:collapse-cocycle` read in the coordinates,
  for the displacement families `d_g = Θ(g) p Θ(g)* - p` of a coordinatewise
  unitary representation;
* `cocycle_mk` transports any coordinate identity of that shape to the
  classes, and `cocycle_class` is the two combined:
  `β(gh) = β(g) + π(g) β(h)` in `Vec Y w ω`.

Because `conjQ` is built from `Submodule.mapQ`, the identity `cocycle_class`
is an identity between genuine ultraproduct vectors, not between coordinate
families; that is exactly the upgrade the row asks for.

## What is not here

`π` is built from a coordinatewise **exactly** multiplicative unitary family.
The printed proof lifts `Θ` to unitary coordinates that are only
asymptotically multiplicative (`lem:unitarycorona`), and multiplicativity of
`π` on classes is then a consequence of that asymptotic statement.  Nothing
below assumes exact multiplicativity of the *lift* — `cocycle_mk` takes the
coordinate identity as a hypothesis, and `coordinate_cocycle` supplies it
from an exact representation.  The upgrade of `conjQ` to a group
homomorphism `H →* (Vec ≃ₗ Vec)` from an asymptotic lift, and the isometry of
`conjQ` for the inner product of `Sofic/KOmegaHilbert`, are not proved here.
-/

namespace GroupApproximation
namespace CollapseCocycleAnalytic

open Filter Matrix Topology
open ScaledKazhdanTransport UltraproductModelConstruction
open RankNormalizedHilbertization
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : ℕ → FiniteModel) (w : ℕ → ℝ) (ω : Ultrafilter ℕ)

/-! ## `Ad U_n` on the numerator and on the ultraproduct -/

/-- **`Ad U_n` on the numerator.**  Conjugation by a coordinatewise unitary
family is a `ℂ`-linear endomorphism of the mass-bounded families: unitary
conjugation is mass exact, so it does not leave `massBounded`. -/
def conjBounded (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    massBounded Y w →ₗ[ℂ] massBounded Y w where
  toFun ξ :=
    ⟨fun n ↦ (U n : Matrix (Y n) (Y n) ℂ) * (ξ : MatFam Y) n *
        (U n : Matrix (Y n) (Y n) ℂ)ᴴ,
      massBounded_unitary_conj Y w U (ξ : MatFam Y) ξ.2⟩
  map_add' ξ η := by
    apply Subtype.ext
    funext n
    show (U n : Matrix (Y n) (Y n) ℂ) *
          ((ξ : MatFam Y) n + (η : MatFam Y) n) *
          (U n : Matrix (Y n) (Y n) ℂ)ᴴ
        = (U n : Matrix (Y n) (Y n) ℂ) * (ξ : MatFam Y) n *
            (U n : Matrix (Y n) (Y n) ℂ)ᴴ
          + (U n : Matrix (Y n) (Y n) ℂ) * (η : MatFam Y) n *
            (U n : Matrix (Y n) (Y n) ℂ)ᴴ
    rw [mul_add, add_mul]
  map_smul' c ξ := by
    apply Subtype.ext
    funext n
    show (U n : Matrix (Y n) (Y n) ℂ) * (c • (ξ : MatFam Y) n) *
          (U n : Matrix (Y n) (Y n) ℂ)ᴴ
        = c • ((U n : Matrix (Y n) (Y n) ℂ) * (ξ : MatFam Y) n *
            (U n : Matrix (Y n) (Y n) ℂ)ᴴ)
    rw [mul_smul_comm, smul_mul_assoc]

/-- **`π(h) = [Ad U_n(h)]_ω`.**  Conjugation descends to the ultraproduct,
because it preserves the denominator as well as the numerator. -/
def conjQ (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    Vec Y w ω →ₗ[ℂ] Vec Y w ω :=
  Submodule.mapQ (nullIn Y w ω) (nullIn Y w ω) (conjBounded Y w U)
    fun ξ hξ ↦ massNull_unitary_conj Y w ω U (ξ : MatFam Y) hξ

@[simp] theorem conjQ_mk (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ)
    (ξ : massBounded Y w) :
    conjQ Y w ω U (Submodule.Quotient.mk ξ)
      = Submodule.Quotient.mk (conjBounded Y w U ξ) :=
  rfl

/-! ## The cocycle -/

/-- **CO.21, transport of the cocycle identity to the classes.**  If three
mass-bounded families satisfy the printed relation
`d_{gh} = d_g + U d_h U*` coordinatewise, their classes satisfy
`β(gh) = β(g) + π(g) β(h)` in the ultraproduct. -/
theorem cocycle_mk (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ)
    (dgh dg dh : massBounded Y w)
    (hid : ∀ n, (dgh : MatFam Y) n
      = (dg : MatFam Y) n
        + (U n : Matrix (Y n) (Y n) ℂ) * (dh : MatFam Y) n *
          (U n : Matrix (Y n) (Y n) ℂ)ᴴ) :
    (Submodule.Quotient.mk dgh : Vec Y w ω)
      = Submodule.Quotient.mk dg
        + conjQ Y w ω U (Submodule.Quotient.mk dh) := by
  have hsum : dgh = dg + conjBounded Y w U dh := by
    apply Subtype.ext
    funext n
    exact hid n
  rw [hsum, conjQ_mk, Submodule.Quotient.mk_add]

/-- The coordinate displacement family `d_g = Θ(g) p Θ(g)* - p`. -/
def displacement {H : Type*} [Group H]
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) (p : MatFam Y) (g : H) :
    MatFam Y :=
  fun n ↦ (Θ g n : Matrix (Y n) (Y n) ℂ) * p n *
    (Θ g n : Matrix (Y n) (Y n) ℂ)ᴴ - p n

/-- **`eq:collapse-cocycle` in coordinates.**  `p_{gh} = Θ(g) p_h Θ(g)*` by
multiplicativity, and the two copies of `Θ(g) p Θ(g)*` cancel. -/
theorem coordinate_cocycle {H : Type*} [Group H]
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) (p : MatFam Y) (g h : H)
    (n : ℕ) :
    displacement Y Θ p (g * h) n
      = displacement Y Θ p g n
        + (Θ g n : Matrix (Y n) (Y n) ℂ) * displacement Y Θ p h n *
          (Θ g n : Matrix (Y n) (Y n) ℂ)ᴴ := by
  have hmul : (Θ (g * h) n : Matrix (Y n) (Y n) ℂ)
      = (Θ g n : Matrix (Y n) (Y n) ℂ) *
        (Θ h n : Matrix (Y n) (Y n) ℂ) :=
    congrArg (fun U : (∀ m, Matrix.unitaryGroup (Y m) ℂ) ↦
      ((U n : Matrix (Y n) (Y n) ℂ))) (map_mul Θ g h)
  show (Θ (g * h) n : Matrix (Y n) (Y n) ℂ) * p n *
        (Θ (g * h) n : Matrix (Y n) (Y n) ℂ)ᴴ - p n
      = ((Θ g n : Matrix (Y n) (Y n) ℂ) * p n *
            (Θ g n : Matrix (Y n) (Y n) ℂ)ᴴ - p n)
        + (Θ g n : Matrix (Y n) (Y n) ℂ) *
            ((Θ h n : Matrix (Y n) (Y n) ℂ) * p n *
              (Θ h n : Matrix (Y n) (Y n) ℂ)ᴴ - p n) *
            (Θ g n : Matrix (Y n) (Y n) ℂ)ᴴ
  rw [hmul, Matrix.conjTranspose_mul]
  noncomm_ring

/-- **CO.21.**  For a coordinatewise unitary representation `Θ` and a
coordinate family `p`, the classes of the displacements form an exact
`1`-cocycle for the conjugation action `π` on the ultraproduct:
`β(gh) = β(g) + π(g) β(h)`. -/
theorem cocycle_class {H : Type*} [Group H]
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) (p : MatFam Y) (g h : H)
    (hgh : displacement Y Θ p (g * h) ∈ massBounded Y w)
    (hg : displacement Y Θ p g ∈ massBounded Y w)
    (hh : displacement Y Θ p h ∈ massBounded Y w) :
    (Submodule.Quotient.mk ⟨displacement Y Θ p (g * h), hgh⟩ : Vec Y w ω)
      = Submodule.Quotient.mk ⟨displacement Y Θ p g, hg⟩
        + conjQ Y w ω (fun n ↦ Θ g n)
            (Submodule.Quotient.mk ⟨displacement Y Θ p h, hh⟩) :=
  cocycle_mk Y w ω (fun n ↦ Θ g n)
    ⟨displacement Y Θ p (g * h), hgh⟩ ⟨displacement Y Θ p g, hg⟩
    ⟨displacement Y Θ p h, hh⟩ fun n ↦ coordinate_cocycle Y Θ p g h n

end

end CollapseCocycleAnalytic
end GroupApproximation
