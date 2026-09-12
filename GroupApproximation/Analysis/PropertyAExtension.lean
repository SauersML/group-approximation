import GroupApproximation.Analysis.ExactnessPermanence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-!
# Link `E.3`: property A is closed under group extensions

## What this closes

`non_mf_groups_exist.tex`, the paragraph opened by
`\paragraph{An exact stably finite non-MF algebra.}` --- located by that string,
since line numbers drift --- deduces exactness of `Cred(W)` for the Clifford
witness `W = Cl(X) ⋊ Σ` in four links, numbered `E.1`--`E.4` in
`ExactnessPermanence.lean` and `CStarExactness.lean`:

| link | manuscript step | side |
|---|---|---|
| `E.1` | the locally finite lamp kernel is amenable, hence exact | group |
| `E.2` | the linear group `Σ ≤ GL₄(ℚ)` is exact (`\cite{GHW}`) | group |
| `E.3` | exact groups are closed under extensions (`\cite{KWPermanence}`) | group |
| `E.4` | for discrete groups, `W` exact ⟺ `Cred(W)` exact (`\cite{KWExact}`) | crossover |

`E.1` is proved in `ExactnessPermanence.lean`, on the manuscript's own lamp
group.  **This module proves `E.3`**, at the same level of abstraction: group
exactness in its combinatorial form, Yu's property A
(`ExactnessPermanence.HasPropertyA`).

## Why this is reachable, contrary to the earlier assessment

`ExactnessPermanence.lean` records `E.3` as needing coarse geometry --- word
metrics, finite balls, and a quasi-isometric section --- on the ground that a
set-theoretic section `σ : Q → G` has `σ(q)σ(q')⁻¹` unbounded, so fibre base
points cannot be compared uniformly.  That objection does not apply to the
construction below, and the reason is a cancellation.

Attach to a point `g ∈ G` and a fibre `q ∈ Q` the *fibre base point*

```
    n(g, q) = σ(q)⁻¹ · g · σ(π(g)⁻¹ q)   ∈  ker π ,
```

and compare two points `g, h` of `G` **inside one and the same fibre `q`**.
The section value `σ(q)` occurs once as `σ(q)⁻¹` on the left of `n(g,q)` and
once as `σ(q)` on the right of `n(g,q)⁻¹`, so it cancels outright:

```
    n(g, q)⁻¹ · n(h, q) = σ(π(g)⁻¹ q)⁻¹ · (g⁻¹h) · σ(π(h)⁻¹ q) .
```

Writing `u = π(h)⁻¹ q` and `r = g⁻¹h`, this is `σ(π(r)u)⁻¹ · r · σ(u)`, which
involves `σ` only at `u` and at `π(r)u`.  In the estimate below `u` ranges over
the **finite** template of the quotient witness and `r` over the given finite
scale, so only finitely many section values are ever compared: no uniform
control on `σ` is needed, and no metric enters.  The unboundedness of
`σ(q)σ(q')⁻¹` is real; it is simply never invoked, because base points are only
ever compared within a single fibre.

This is the standard proof of Kirchberg--Wassermann permanence for *groups*.
The corresponding statement for general bounded-geometry metric spaces is
subtler, which is presumably the source of the earlier caution.  What makes the
group case work is that the support constraint in `PropertyAWitness` is
`g`-*relative* --- the measure at `g` lives on `g · template` for one fixed
finite `template` --- so translating the whole construction by `g` costs
nothing.

## The construction

Given a surjection `π : G →* Q` with `ker π` and `Q` both of property A, a
scale `R : Finset G` and a tolerance `ε`:

* take a `Q`-witness `WQ` at scale `π(R)` and tolerance `ε/2`, with template
  `T`;
* take a `ker π`-witness `WN` at scale
  `{σ(π(r)u)⁻¹ r σ(u) : u ∈ T, r ∈ R}` and tolerance `ε/2`, with template `S`;
* put, for `g, x ∈ G`,

  ```
      ζ_g(x) = WQ.weight (π g) (π x) · WN.weight (n(g, π x)) (σ(π x)⁻¹ x) ,
  ```

  the mass the quotient measure gives to the fibre of `x`, times the mass the
  kernel measure based at `n(g, π x)` gives to `x` inside that fibre.

Total mass is `1` because the fibre masses sum to `1` and each fibre measure
has mass `1`; the support sits inside `g · {σ(u)m : u ∈ T, m ∈ S}`; and the
`ℓ¹` estimate splits by

```
    |a b - c d| ≤ |a - c| b + c |b - d| ,
```

the first term summing to the quotient defect `≤ ε/2` (the fibre masses of a
probability measure sum to at most `1`) and the second to the kernel defect
`≤ ε/2` (weighted by quotient masses, which again sum to at most `1`).

## What is still missing on the chain

* `E.2` --- property A for finitely generated linear groups --- is
  Guentner--Higson--Weinberger's theorem.  It is **neither proved here nor
  assumed here as a named proposition**: the corollaries below that need it
  carry `HasPropertyA Σ` as an ordinary hypothesis, so the conditionality is
  visible in the type rather than hidden in a transcription.  The repository's
  `LITERATURE_INPUT` roster is deliberately empty (`scripts/Audit.lean`), and
  nothing here adds to it.
* `E.4` --- the crossover from group exactness to exactness of the reduced
  C⋆-algebra --- is not *statable* against the pinned Mathlib: there is no
  C⋆-norm on a tensor product, hence no `⊗_min`, hence no definition of an
  exact C⋆-algebra.  See the survey with file/line evidence in
  `CStarExactness.lean`.

So after this module the manuscript's exactness row still stands as MISSING;
what has changed is that the missing part is exactly `E.2` and `E.4`, rather
than `E.2`, `E.3` and `E.4`.

## Contents

* `abs_mul_sub_mul_le` --- the elementary product splitting behind the `ℓ¹`
  estimate.
* `PropertyAWitness.sum_le_one`, `PropertyAWitness.sum_abs_sub_le` --- the two
  facts about a single witness that the construction consumes: partial masses
  are at most `1`, and the `ℓ¹` bound holds over *any* window.
* `HasPropertyA.of_mulEquiv` --- transport along a group isomorphism.
* `fibreCoord`, `fibreBase`, `fibreShift`, `fibreChart` and their identities;
  `fibreBase_inv_mul_fibreBase` is the cancellation described above.
* `hasPropertyA_of_ker_of_quotient` --- **link `E.3`**.
* `hasPropertyA_semidirectProduct`,
  `hasPropertyA_semidirectProduct_of_isLocallyFiniteGroup` --- the shape in
  which the manuscript uses `E.3`: a locally finite kernel, and a quotient
  whose property A is supplied by `E.2`.
-/

namespace GroupApproximation
namespace ExactnessPermanence

universe u v

/-! ## An elementary product splitting

The `ℓ¹` estimate for a product of measures needs exactly one inequality, and
it is worth isolating because its sign hypotheses are easy to lose. -/

/-- Splitting a difference of products: `ab - cd = (a-c)b + c(b-d)`, then the
triangle inequality.  Both `b` and `c` are masses of measures, hence
nonnegative, which is what lets their absolute values be dropped. -/
theorem abs_mul_sub_mul_le {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |a * b - c * d| ≤ |a - c| * b + c * |b - d| := by
  have hsplit : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  calc |a * b - c * d| = |(a - c) * b + c * (b - d)| := by rw [hsplit]
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * b + c * |b - d| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]

/-! ## Two facts about a single property-A witness

Neither is deep, but both are used repeatedly below and both are awkward to
inline: the first because the support clause has to be turned into a
containment of `Finset`s, the second because `weight_close` as stated demands a
window containing both supports, while the estimates below want to choose their
own windows. -/

namespace PropertyAWitness

variable {G : Type u} [Group G] {R : Finset G} {ε : ℝ}

/-- **A partial mass is at most the total mass.**  The measure attached to `g`
is supported inside `g · template` and has total mass `1`, so its sum over any
finite set of points is at most `1`. -/
theorem sum_le_one (W : PropertyAWitness G R ε) (g : G) (U : Finset G) :
    ∑ x ∈ U, W.weight g x ≤ 1 := by
  classical
  have hinj : Set.InjOn (fun s : G ↦ g * s) (W.template : Set G) :=
    fun a _ b _ hab ↦ mul_left_cancel hab
  have hres : ∑ x ∈ W.template.image (fun s : G ↦ g * s), W.weight g x
      = ∑ x ∈ U ∪ W.template.image (fun s : G ↦ g * s), W.weight g x := by
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro x _ hx
    refine W.weight_eq_zero g x ?_
    intro hmem
    exact hx (Finset.mem_image.mpr ⟨g⁻¹ * x, hmem, mul_inv_cancel_left g x⟩)
  calc ∑ x ∈ U, W.weight g x
      ≤ ∑ x ∈ U ∪ W.template.image (fun s : G ↦ g * s), W.weight g x :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun x _ _ ↦ W.weight_nonneg g x)
    _ = ∑ x ∈ W.template.image (fun s : G ↦ g * s), W.weight g x := hres.symm
    _ = ∑ s ∈ W.template, W.weight g (g * s) := Finset.sum_image hinj
    _ = 1 := W.weight_sum g

/-- **The `ℓ¹` bound holds over an arbitrary window.**  `weight_close` is stated
for windows containing both supports; enlarging any window to such a one only
adds nonnegative terms, so the bound holds for every finite window. -/
theorem sum_abs_sub_le (W : PropertyAWitness G R ε) {g h : G} (hgh : g⁻¹ * h ∈ R)
    (T : Finset G) : ∑ x ∈ T, |W.weight g x - W.weight h x| ≤ ε := by
  classical
  obtain ⟨T₀, h₀g, h₀h⟩ := W.exists_window g h
  calc ∑ x ∈ T, |W.weight g x - W.weight h x|
      ≤ ∑ x ∈ T ∪ T₀, |W.weight g x - W.weight h x| :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun x _ _ ↦ abs_nonneg _)
    _ ≤ ε := W.weight_close g h hgh (T ∪ T₀)
        (fun x hx ↦ Finset.mem_union_right _ (h₀g x hx))
        (fun x hx ↦ Finset.mem_union_right _ (h₀h x hx))

end PropertyAWitness

/-! ## Transport along an isomorphism

Property A is a property of the group, not of a presentation of it, and the
extension theorem is applied below to a kernel that is only *isomorphic* to the
group one starts from, so the transport has to be available. -/

/-- **Property A is an isomorphism invariant.**  The witness for `H` is the
witness for `G` read through `e`: template and scale are transported by `e` and
`e.symm`, and every clause becomes the corresponding clause for `G`. -/
theorem HasPropertyA.of_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (hG : HasPropertyA G) : HasPropertyA H := by
  classical
  intro R ε hε
  obtain ⟨W⟩ := hG (R.image (fun y : H ↦ e.symm y)) ε hε
  refine ⟨{
    template := W.template.image (fun t : G ↦ e t)
    weight := fun a y ↦ W.weight (e.symm a) (e.symm y)
    weight_nonneg := ?_
    weight_eq_zero := ?_
    weight_sum := ?_
    weight_close := ?_ }⟩
  · intro a y
    show (0 : ℝ) ≤ W.weight (e.symm a) (e.symm y)
    exact W.weight_nonneg _ _
  · intro a y hy
    show W.weight (e.symm a) (e.symm y) = 0
    refine W.weight_eq_zero (e.symm a) (e.symm y) ?_
    intro hmem
    refine hy (Finset.mem_image.mpr ⟨(e.symm a)⁻¹ * e.symm y, hmem, ?_⟩)
    show e ((e.symm a)⁻¹ * e.symm y) = a⁻¹ * y
    rw [map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply]
  · intro a
    show ∑ s ∈ W.template.image (fun t : G ↦ e t),
        W.weight (e.symm a) (e.symm (a * s)) = 1
    have hinj : Set.InjOn (fun t : G ↦ e t) (W.template : Set G) :=
      e.injective.injOn
    have hterm : ∀ t ∈ W.template,
        W.weight (e.symm a) (e.symm (a * e t))
          = W.weight (e.symm a) (e.symm a * t) := by
      intro t _
      rw [map_mul, e.symm_apply_apply]
    calc ∑ s ∈ W.template.image (fun t : G ↦ e t),
            W.weight (e.symm a) (e.symm (a * s))
        = ∑ t ∈ W.template, W.weight (e.symm a) (e.symm (a * e t)) :=
          Finset.sum_image hinj
      _ = ∑ t ∈ W.template, W.weight (e.symm a) (e.symm a * t) :=
          Finset.sum_congr rfl hterm
      _ = 1 := W.weight_sum _
  · intro a b hab T _ _
    show ∑ y ∈ T, |W.weight (e.symm a) (e.symm y)
      - W.weight (e.symm b) (e.symm y)| ≤ ε
    have hscale : (e.symm a)⁻¹ * e.symm b ∈ R.image (fun y : H ↦ e.symm y) := by
      have hrw : e.symm (a⁻¹ * b) = (e.symm a)⁻¹ * e.symm b := by
        rw [map_mul, map_inv]
      rw [← hrw]
      exact Finset.mem_image_of_mem _ hab
    have hinj : Set.InjOn (fun y : H ↦ e.symm y) (T : Set H) :=
      e.symm.injective.injOn
    -- Stated in the direction in which the image side is the left-hand side:
    -- there the summand is determined first order.  Applying `Finset.sum_image`
    -- directly to the `.symm` of this leaves the summand as a higher-order
    -- metavariable, because `e.symm y` occurs twice in the body.
    have hreindex : ∑ z ∈ T.image (fun y : H ↦ e.symm y),
          |W.weight (e.symm a) z - W.weight (e.symm b) z|
        = ∑ y ∈ T,
            |W.weight (e.symm a) (e.symm y) - W.weight (e.symm b) (e.symm y)| :=
      Finset.sum_image hinj
    calc ∑ y ∈ T, |W.weight (e.symm a) (e.symm y) - W.weight (e.symm b) (e.symm y)|
        = ∑ z ∈ T.image (fun y : H ↦ e.symm y),
            |W.weight (e.symm a) z - W.weight (e.symm b) z| := hreindex.symm
      _ ≤ ε := W.sum_abs_sub_le hscale _

/-! ## Fibre coordinates for a group extension

Everything below is relative to a surjection `π : G →* Q` together with a
purely set-theoretic section `σ`.  No property of `σ` beyond `π ∘ σ = id` is
ever used --- in particular no boundedness, no homomorphism property, and no
normalisation `σ(1) = 1`. -/

section Fibre

variable {G : Type u} {Q : Type v} [Group G] [Group Q]

/-- The **fibre coordinate** of `x`: the kernel element `σ(π x)⁻¹ x`, which
records where `x` sits inside its own fibre relative to the chosen section. -/
def fibreCoord (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (x : G) :
    ↥π.ker :=
  ⟨(σ (π x))⁻¹ * x, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]⟩

@[simp]
theorem coe_fibreCoord (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (x : G) :
    ((fibreCoord π σ hσ x : ↥π.ker) : G) = (σ (π x))⁻¹ * x := rfl

/-- The **fibre base point** attached to `g` in the fibre over `q`: the kernel
element `σ(q)⁻¹ g σ(π(g)⁻¹ q)`.  This is the point of `ker π` at which the
kernel's own property-A measure is evaluated when the measure attached to `g`
is restricted to the fibre over `q`. -/
def fibreBase (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (g : G) (q : Q) :
    ↥π.ker :=
  ⟨(σ q)⁻¹ * g * σ ((π g)⁻¹ * q), by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hσ, hσ, mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel]⟩

@[simp]
theorem coe_fibreBase (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q)
    (g : G) (q : Q) :
    ((fibreBase π σ hσ g q : ↥π.ker) : G) = (σ q)⁻¹ * g * σ ((π g)⁻¹ * q) := rfl

/-- The **fibre shift** by `r` at `u`: the kernel element `σ(π(r)u)⁻¹ r σ(u)`.

This is the reason the extension argument needs no coarse geometry.  As
`fibreBase_inv_mul_fibreBase` records, the displacement between the base points
that two elements attach to one and the same fibre is a fibre shift whose two
arguments range over *finite* sets: `r` over the given scale, and `u` over the
template of the quotient witness. -/
def fibreShift (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (r : G) (u : Q) :
    ↥π.ker :=
  ⟨(σ (π r * u))⁻¹ * r * σ u, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hσ, hσ, mul_assoc,
      inv_mul_cancel]⟩

@[simp]
theorem coe_fibreShift (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q)
    (r : G) (u : Q) :
    ((fibreShift π σ hσ r u : ↥π.ker) : G) = (σ (π r * u))⁻¹ * r * σ u := rfl

/-- The **chart** `Q × ker π → G`, `(q, n) ↦ σ(q) n`.  It is a bijection of
sets --- never a homomorphism --- and it is what turns a sum over an arbitrary
finite subset of `G` into a double sum over a fibre index and a fibre
coordinate. -/
def fibreChart (π : G →* Q) (σ : Q → G) (p : Q × ↥π.ker) : G :=
  σ p.1 * (p.2 : G)

@[simp]
theorem fibreChart_apply (π : G →* Q) (σ : Q → G) (q : Q) (n : ↥π.ker) :
    fibreChart π σ (q, n) = σ q * (n : G) := rfl

/-- The chart lands in the fibre named by its first coordinate. -/
theorem map_fibreChart (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q)
    (q : Q) (n : ↥π.ker) : π (fibreChart π σ (q, n)) = q := by
  show π (σ q * (n : G)) = q
  rw [map_mul, hσ, MonoidHom.mem_ker.mp n.2, mul_one]

/-- The chart's second coordinate is recovered as the fibre coordinate. -/
theorem fibreCoord_fibreChart (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q)
    (q : Q) (n : ↥π.ker) :
    fibreCoord π σ hσ (fibreChart π σ (q, n)) = n := by
  apply Subtype.ext
  simp only [coe_fibreCoord, map_fibreChart π σ hσ q n]
  show (σ q)⁻¹ * (σ q * (n : G)) = (n : G)
  rw [inv_mul_cancel_left]

/-- Every group element is the chart value at its own fibre data. -/
theorem fibreChart_fibreCoord (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q)
    (x : G) : fibreChart π σ (π x, fibreCoord π σ hσ x) = x := by
  show σ (π x) * ((fibreCoord π σ hσ x : ↥π.ker) : G) = x
  rw [coe_fibreCoord, mul_inv_cancel_left]

/-- The chart is injective: the fibre determines the first coordinate, and left
cancellation then determines the second. -/
theorem fibreChart_injective (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) :
    Function.Injective (fibreChart π σ) := by
  rintro ⟨q₁, n₁⟩ ⟨q₂, n₂⟩ hEq
  have h1 : q₁ = q₂ := by
    rw [← map_fibreChart π σ hσ q₁ n₁, ← map_fibreChart π σ hσ q₂ n₂, hEq]
  have h2 : n₁ = n₂ := by
    rw [← fibreCoord_fibreChart π σ hσ q₁ n₁, ← fibreCoord_fibreChart π σ hσ q₂ n₂,
      hEq]
  rw [h1, h2]

/-- **The support identity.**  The displacement between the base point that `g`
attaches to the fibre of `x` and the fibre coordinate of `x` is exactly the
fibre coordinate of `g⁻¹x`.

This is what makes the support of the constructed measure a *translate*
`g · template` of one fixed finite set, which is what `PropertyAWitness`
demands. -/
theorem fibreBase_inv_mul_fibreCoord (π : G →* Q) (σ : Q → G)
    (hσ : ∀ q, π (σ q) = q) (g x : G) :
    (fibreBase π σ hσ g (π x))⁻¹ * fibreCoord π σ hσ x
      = fibreCoord π σ hσ (g⁻¹ * x) := by
  have hπ : π (g⁻¹ * x) = (π g)⁻¹ * π x := by rw [map_mul, map_inv]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_fibreCoord, coe_fibreBase, hπ]
  group

/-- **The comparison identity, and the heart of the matter.**  The two base
points that `g` and `h` attach to one and the same fibre `q` differ by the
fibre shift with `r = g⁻¹h` and `u = π(h)⁻¹q`.

The section value `σ(q)` --- the one that is genuinely uncontrolled as `q`
varies --- has cancelled.  What remains involves `σ` only at `u` and at
`π(r)u`; in the estimate below `u` runs over the finite template of the
quotient witness and `r` over the finite scale, so the displacements that occur
form a finite subset of the kernel. -/
theorem fibreBase_inv_mul_fibreBase (π : G →* Q) (σ : Q → G)
    (hσ : ∀ q, π (σ q) = q) (g h : G) (q : Q) :
    (fibreBase π σ hσ g q)⁻¹ * fibreBase π σ hσ h q
      = fibreShift π σ hσ (g⁻¹ * h) ((π h)⁻¹ * q) := by
  have hq : π (g⁻¹ * h) * ((π h)⁻¹ * q) = (π g)⁻¹ * q := by
    rw [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_fibreBase, coe_fibreShift, hq]
  group

/-- Translating a chart point by `g` moves its fibre by `π g`. -/
theorem map_mul_fibreChart (π : G →* Q) (σ : Q → G) (hσ : ∀ q, π (σ q) = q)
    (g : G) (q : Q) (n : ↥π.ker) :
    π (g * fibreChart π σ (q, n)) = π g * q := by
  rw [map_mul, map_fibreChart π σ hσ q n]

/-- **The mass identity.**  Translating the chart point `(q, n)` by `g` places
it in the fibre over `π(g)q`, at the fibre coordinate obtained from the base
point `fibreBase g (π(g)q)` by translating by `n`.

This is the shape in which the kernel witness's `weight_sum` --- which sums
`weight b (b * s)` over the template --- can be applied. -/
theorem fibreCoord_mul_fibreChart (π : G →* Q) (σ : Q → G)
    (hσ : ∀ q, π (σ q) = q) (g : G) (q : Q) (n : ↥π.ker) :
    fibreCoord π σ hσ (g * fibreChart π σ (q, n))
      = fibreBase π σ hσ g (π g * q) * n := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_fibreCoord, coe_fibreBase,
    map_mul_fibreChart π σ hσ g q n, inv_mul_cancel_left]
  show (σ (π g * q))⁻¹ * (g * (σ q * (n : G)))
    = (σ (π g * q))⁻¹ * g * σ q * (n : G)
  group

end Fibre

/-! ## Link `E.3` -/

/-- **Property A is closed under extensions.**  If `π : G →* Q` is surjective
and both `ker π` and `Q` have property A, then so does `G`.

This is the manuscript's link `E.3`, `\cite{KWPermanence}`, in its group form.
The measure attached to `g` distributes the quotient witness's mass over the
fibres and, inside the fibre over `q`, spreads it by the kernel witness's
measure based at `fibreBase g q`.  The `ℓ¹` estimate splits by
`abs_mul_sub_mul_le` into a quotient defect and a kernel defect, each budgeted
`ε/2`; the kernel defect is controlled because, by
`fibreBase_inv_mul_fibreBase`, the base points that `g` and `h` attach to a
fibre carrying nonzero quotient mass differ by a fibre shift lying in the
finite scale at which the kernel witness was taken. -/
theorem hasPropertyA_of_ker_of_quotient {G : Type u} {Q : Type v} [Group G]
    [Group Q] (π : G →* Q) (hπ : Function.Surjective π)
    (hker : HasPropertyA ↥π.ker) (hQ : HasPropertyA Q) : HasPropertyA G := by
  classical
  intro R ε hε
  obtain ⟨σ, hσ⟩ : ∃ σ : Q → G, ∀ q, π (σ q) = q :=
    ⟨Function.surjInv hπ, fun q ↦ Function.surjInv_eq hπ q⟩
  have hεhalf : (0 : ℝ) < ε / 2 := half_pos hε
  obtain ⟨WQ⟩ := hQ (R.image (fun r : G ↦ π r)) (ε / 2) hεhalf
  obtain ⟨WN⟩ := hker
    ((WQ.template ×ˢ R).image (fun p : Q × G ↦ fibreShift π σ hσ p.2 p.1))
    (ε / 2) hεhalf
  have hchart : Function.Injective (fibreChart π σ) := fibreChart_injective π σ hσ
  refine ⟨{
    template := (WQ.template ×ˢ WN.template).image (fibreChart π σ)
    weight := fun a x ↦ WQ.weight (π a) (π x) *
      WN.weight (fibreBase π σ hσ a (π x)) (fibreCoord π σ hσ x)
    weight_nonneg := ?_
    weight_eq_zero := ?_
    weight_sum := ?_
    weight_close := ?_ }⟩
  -- Nonnegativity: a product of two masses.
  · intro a x
    show (0 : ℝ) ≤ WQ.weight (π a) (π x) *
      WN.weight (fibreBase π σ hσ a (π x)) (fibreCoord π σ hσ x)
    exact mul_nonneg (WQ.weight_nonneg _ _) (WN.weight_nonneg _ _)
  -- Support: both factors nonzero forces `a⁻¹x` into the one fixed template.
  · intro a x hx
    show WQ.weight (π a) (π x) *
      WN.weight (fibreBase π σ hσ a (π x)) (fibreCoord π σ hσ x) = 0
    by_contra hne
    have hQne : WQ.weight (π a) (π x) ≠ 0 := by
      intro h0
      exact hne (by rw [h0, zero_mul])
    have hNne : WN.weight (fibreBase π σ hσ a (π x)) (fibreCoord π σ hσ x) ≠ 0 := by
      intro h0
      exact hne (by rw [h0, mul_zero])
    have hQmem : (π a)⁻¹ * π x ∈ WQ.template := by
      by_contra hc
      exact hQne (WQ.weight_eq_zero (π a) (π x) hc)
    have hNmem : fibreCoord π σ hσ (a⁻¹ * x) ∈ WN.template := by
      by_contra hc
      refine hNne (WN.weight_eq_zero _ _ ?_)
      rwa [fibreBase_inv_mul_fibreCoord π σ hσ a x]
    have hπy : π (a⁻¹ * x) = (π a)⁻¹ * π x := by rw [map_mul, map_inv]
    refine hx (Finset.mem_image.mpr
      ⟨(π (a⁻¹ * x), fibreCoord π σ hσ (a⁻¹ * x)), ?_, ?_⟩)
    · refine Finset.mem_product.mpr ⟨?_, hNmem⟩
      show π (a⁻¹ * x) ∈ WQ.template
      rw [hπy]
      exact hQmem
    · exact fibreChart_fibreCoord π σ hσ (a⁻¹ * x)
  -- Total mass: the fibre masses sum to one, each fibre measure has mass one.
  · intro a
    show ∑ s ∈ (WQ.template ×ˢ WN.template).image (fibreChart π σ),
        WQ.weight (π a) (π (a * s)) *
          WN.weight (fibreBase π σ hσ a (π (a * s)))
            (fibreCoord π σ hσ (a * s)) = 1
    have hinj : Set.InjOn (fibreChart π σ)
        ((WQ.template ×ˢ WN.template : Finset (Q × ↥π.ker)) : Set (Q × ↥π.ker)) :=
      hchart.injOn
    -- Stated separately, and applied with `exact`, so that the rewrites do not
    -- have to fire underneath an unreduced application of the summand.
    have hterm : ∀ (q : Q) (n : ↥π.ker),
        WQ.weight (π a) (π (a * fibreChart π σ (q, n))) *
            WN.weight (fibreBase π σ hσ a (π (a * fibreChart π σ (q, n))))
              (fibreCoord π σ hσ (a * fibreChart π σ (q, n)))
          = WQ.weight (π a) (π a * q) *
              WN.weight (fibreBase π σ hσ a (π a * q))
                (fibreBase π σ hσ a (π a * q) * n) := by
      intro q n
      rw [map_mul_fibreChart π σ hσ a q n, fibreCoord_mul_fibreChart π σ hσ a q n]
    calc ∑ s ∈ (WQ.template ×ˢ WN.template).image (fibreChart π σ),
            WQ.weight (π a) (π (a * s)) *
              WN.weight (fibreBase π σ hσ a (π (a * s)))
                (fibreCoord π σ hσ (a * s))
        = ∑ p ∈ WQ.template ×ˢ WN.template,
            WQ.weight (π a) (π (a * fibreChart π σ p)) *
              WN.weight (fibreBase π σ hσ a (π (a * fibreChart π σ p)))
                (fibreCoord π σ hσ (a * fibreChart π σ p)) :=
          Finset.sum_image hinj
      _ = ∑ q ∈ WQ.template, ∑ n ∈ WN.template,
            WQ.weight (π a) (π a * q) *
              WN.weight (fibreBase π σ hσ a (π a * q))
                (fibreBase π σ hσ a (π a * q) * n) := by
          rw [Finset.sum_product]
          exact Finset.sum_congr rfl fun q _ ↦
            Finset.sum_congr rfl fun n _ ↦ hterm q n
      _ = ∑ q ∈ WQ.template, WQ.weight (π a) (π a * q) := by
          have hinner : ∀ q : Q,
              ∑ n ∈ WN.template, WQ.weight (π a) (π a * q) *
                  WN.weight (fibreBase π σ hσ a (π a * q))
                    (fibreBase π σ hσ a (π a * q) * n)
                = WQ.weight (π a) (π a * q) := by
            intro q
            rw [← Finset.mul_sum, WN.weight_sum, mul_one]
          exact Finset.sum_congr rfl fun q _ ↦ hinner q
      _ = 1 := WQ.weight_sum (π a)
  -- The `ℓ¹` estimate.
  · intro a b hab T _ _
    show ∑ x ∈ T, |WQ.weight (π a) (π x) *
          WN.weight (fibreBase π σ hσ a (π x)) (fibreCoord π σ hσ x)
        - WQ.weight (π b) (π x) *
          WN.weight (fibreBase π σ hσ b (π x)) (fibreCoord π σ hσ x)| ≤ ε
    -- Enlarge `T` to a chart box; all terms are nonnegative, so this is free.
    have hTsub : T ⊆ ((T.image (fun x : G ↦ π x)) ×ˢ
        (T.image (fun x : G ↦ fibreCoord π σ hσ x))).image (fibreChart π σ) := by
      intro x hx
      refine Finset.mem_image.mpr ⟨(π x, fibreCoord π σ hσ x), ?_, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
      · exact fibreChart_fibreCoord π σ hσ x
    have hinj : Set.InjOn (fibreChart π σ)
        (((T.image (fun x : G ↦ π x)) ×ˢ
          (T.image (fun x : G ↦ fibreCoord π σ hσ x)) :
            Finset (Q × ↥π.ker)) : Set (Q × ↥π.ker)) := hchart.injOn
    have hscale : (π a)⁻¹ * π b ∈ R.image (fun r : G ↦ π r) := by
      have hrw : π (a⁻¹ * b) = (π a)⁻¹ * π b := by rw [map_mul, map_inv]
      rw [← hrw]
      exact Finset.mem_image_of_mem _ hab
    -- The summand read in chart coordinates; stated separately and applied with
    -- `exact`, so the rewrites need not fire under an unreduced summand.
    have hchartterm : ∀ (q : Q) (n : ↥π.ker),
        |WQ.weight (π a) (π (fibreChart π σ (q, n))) *
              WN.weight (fibreBase π σ hσ a (π (fibreChart π σ (q, n))))
                (fibreCoord π σ hσ (fibreChart π σ (q, n)))
            - WQ.weight (π b) (π (fibreChart π σ (q, n))) *
              WN.weight (fibreBase π σ hσ b (π (fibreChart π σ (q, n))))
                (fibreCoord π σ hσ (fibreChart π σ (q, n)))|
          = |WQ.weight (π a) q * WN.weight (fibreBase π σ hσ a q) n
              - WQ.weight (π b) q * WN.weight (fibreBase π σ hσ b q) n| := by
      intro q n
      rw [map_fibreChart π σ hσ q n, fibreCoord_fibreChart π σ hσ q n]
    -- Fibre by fibre.
    have hfibre : ∀ q ∈ T.image (fun x : G ↦ π x),
        ∑ n ∈ T.image (fun x : G ↦ fibreCoord π σ hσ x),
            |WQ.weight (π a) q * WN.weight (fibreBase π σ hσ a q) n
              - WQ.weight (π b) q * WN.weight (fibreBase π σ hσ b q) n|
          ≤ |WQ.weight (π a) q - WQ.weight (π b) q|
              + WQ.weight (π b) q * (ε / 2) := by
      intro q _
      have hkernel : WQ.weight (π b) q ≠ 0 →
          ∑ n ∈ T.image (fun x : G ↦ fibreCoord π σ hσ x),
              |WN.weight (fibreBase π σ hσ a q) n
                - WN.weight (fibreBase π σ hσ b q) n| ≤ ε / 2 := by
        intro hq0
        have hqmem : (π b)⁻¹ * q ∈ WQ.template := by
          by_contra hc
          exact hq0 (WQ.weight_eq_zero (π b) q hc)
        have hmem : (fibreBase π σ hσ a q)⁻¹ * fibreBase π σ hσ b q ∈
            (WQ.template ×ˢ R).image
              (fun p : Q × G ↦ fibreShift π σ hσ p.2 p.1) := by
          rw [fibreBase_inv_mul_fibreBase π σ hσ a b q]
          exact Finset.mem_image.mpr
            ⟨((π b)⁻¹ * q, a⁻¹ * b), Finset.mem_product.mpr ⟨hqmem, hab⟩, rfl⟩
        exact WN.sum_abs_sub_le hmem _
      have hmass : ∑ n ∈ T.image (fun x : G ↦ fibreCoord π σ hσ x),
          WN.weight (fibreBase π σ hσ a q) n ≤ 1 :=
        WN.sum_le_one (fibreBase π σ hσ a q)
          (T.image (fun x : G ↦ fibreCoord π σ hσ x))
      have hsecond : WQ.weight (π b) q *
          (∑ n ∈ T.image (fun x : G ↦ fibreCoord π σ hσ x),
            |WN.weight (fibreBase π σ hσ a q) n
              - WN.weight (fibreBase π σ hσ b q) n|)
          ≤ WQ.weight (π b) q * (ε / 2) := by
        by_cases hq0 : WQ.weight (π b) q = 0
        · refine le_of_eq ?_
          rw [hq0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hkernel hq0) (WQ.weight_nonneg _ _)
      calc ∑ n ∈ T.image (fun x : G ↦ fibreCoord π σ hσ x),
              |WQ.weight (π a) q * WN.weight (fibreBase π σ hσ a q) n
                - WQ.weight (π b) q * WN.weight (fibreBase π σ hσ b q) n|
          ≤ ∑ n ∈ T.image (fun x : G ↦ fibreCoord π σ hσ x),
              (|WQ.weight (π a) q - WQ.weight (π b) q| *
                  WN.weight (fibreBase π σ hσ a q) n
                + WQ.weight (π b) q *
                  |WN.weight (fibreBase π σ hσ a q) n
                    - WN.weight (fibreBase π σ hσ b q) n|) :=
            Finset.sum_le_sum fun n _ ↦
              abs_mul_sub_mul_le (WN.weight_nonneg _ _) (WQ.weight_nonneg _ _)
        _ = |WQ.weight (π a) q - WQ.weight (π b) q| *
                (∑ n ∈ T.image (fun x : G ↦ fibreCoord π σ hσ x),
                  WN.weight (fibreBase π σ hσ a q) n)
              + WQ.weight (π b) q *
                (∑ n ∈ T.image (fun x : G ↦ fibreCoord π σ hσ x),
                  |WN.weight (fibreBase π σ hσ a q) n
                    - WN.weight (fibreBase π σ hσ b q) n|) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ |WQ.weight (π a) q - WQ.weight (π b) q| * 1
              + WQ.weight (π b) q * (ε / 2) :=
            add_le_add (mul_le_mul_of_nonneg_left hmass (abs_nonneg _)) hsecond
        _ = |WQ.weight (π a) q - WQ.weight (π b) q|
              + WQ.weight (π b) q * (ε / 2) := by rw [mul_one]
    -- Assemble.
    calc ∑ x ∈ T, |WQ.weight (π a) (π x) *
            WN.weight (fibreBase π σ hσ a (π x)) (fibreCoord π σ hσ x)
          - WQ.weight (π b) (π x) *
            WN.weight (fibreBase π σ hσ b (π x)) (fibreCoord π σ hσ x)|
        ≤ ∑ x ∈ ((T.image (fun x : G ↦ π x)) ×ˢ
              (T.image (fun x : G ↦ fibreCoord π σ hσ x))).image (fibreChart π σ),
            |WQ.weight (π a) (π x) *
                WN.weight (fibreBase π σ hσ a (π x)) (fibreCoord π σ hσ x)
              - WQ.weight (π b) (π x) *
                WN.weight (fibreBase π σ hσ b (π x)) (fibreCoord π σ hσ x)| :=
          Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun _ _ _ ↦ abs_nonneg _)
      _ = ∑ p ∈ (T.image (fun x : G ↦ π x)) ×ˢ
              (T.image (fun x : G ↦ fibreCoord π σ hσ x)),
            |WQ.weight (π a) (π (fibreChart π σ p)) *
                WN.weight (fibreBase π σ hσ a (π (fibreChart π σ p)))
                  (fibreCoord π σ hσ (fibreChart π σ p))
              - WQ.weight (π b) (π (fibreChart π σ p)) *
                WN.weight (fibreBase π σ hσ b (π (fibreChart π σ p)))
                  (fibreCoord π σ hσ (fibreChart π σ p))| := Finset.sum_image hinj
      _ = ∑ q ∈ T.image (fun x : G ↦ π x),
            ∑ n ∈ T.image (fun x : G ↦ fibreCoord π σ hσ x),
              |WQ.weight (π a) q * WN.weight (fibreBase π σ hσ a q) n
                - WQ.weight (π b) q * WN.weight (fibreBase π σ hσ b q) n| := by
          rw [Finset.sum_product]
          exact Finset.sum_congr rfl fun q _ ↦
            Finset.sum_congr rfl fun n _ ↦ hchartterm q n
      _ ≤ ∑ q ∈ T.image (fun x : G ↦ π x),
            (|WQ.weight (π a) q - WQ.weight (π b) q|
              + WQ.weight (π b) q * (ε / 2)) := Finset.sum_le_sum hfibre
      _ = (∑ q ∈ T.image (fun x : G ↦ π x),
              |WQ.weight (π a) q - WQ.weight (π b) q|)
            + (∑ q ∈ T.image (fun x : G ↦ π x), WQ.weight (π b) q) * (ε / 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ ε / 2 + 1 * (ε / 2) :=
          add_le_add (WQ.sum_abs_sub_le hscale (T.image (fun x : G ↦ π x)))
            (mul_le_mul_of_nonneg_right
              (WQ.sum_le_one (π b) (T.image (fun x : G ↦ π x))) hεhalf.le)
      _ = ε := by ring

/-! ## The shape in which the manuscript uses `E.3`

The manuscript's witness is `W = Cl(X) ⋊ Σ`, presented there as the extension
`1 → Cl(X) → W → Σ → 1` whose kernel is locally finite.  So the corollaries
below are stated for a semidirect product with a locally finite kernel. -/

/-- **Property A for a semidirect product.**  Apply `E.3` to the projection
`N ⋊[φ] H →* H`, whose kernel is the range of `inl` and hence isomorphic to
`N`. -/
theorem hasPropertyA_semidirectProduct {N : Type u} {H : Type u} [Group N]
    [Group H] {φ : H →* MulAut N} (hN : HasPropertyA N) (hH : HasPropertyA H) :
    HasPropertyA (SemidirectProduct N H φ) := by
  refine hasPropertyA_of_ker_of_quotient
    (SemidirectProduct.rightHom : SemidirectProduct N H φ →* H)
    SemidirectProduct.rightHom_surjective ?_ hH
  refine HasPropertyA.of_mulEquiv ?_ hN
  have hinj : Function.Injective
      (SemidirectProduct.inl : N →* SemidirectProduct N H φ) :=
    SemidirectProduct.inl_injective
  exact (MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom)

/-- **The manuscript's shape.**  A semidirect product of a *locally finite*
group by a group with property A has property A.

This is links `E.1` and `E.3` of the manuscript's chain, composed, on the
manuscript's own extension `1 → Cl(X) → W → Σ → 1`: the kernel `Cl(X)` is
locally finite, hence amenable, hence has property A
(`hasPropertyA_of_isLocallyFiniteGroup_viaAmenability`), and the extension
theorem does the rest.

The hypothesis `HasPropertyA H` is where link `E.2` enters --- for the
manuscript, property A of the linear group `Σ ≤ GL₄(ℚ)`, which is
Guentner--Higson--Weinberger's theorem and is **not** proved in this
repository.  It is left as an explicit hypothesis rather than transcribed as a
named proposition, so that the conditionality is visible in the type.

What remains missing even given `E.2` is `E.4`, the crossover from property A
to exactness of `Cred(W)` (Ozawa, Kirchberg--Wassermann), which is not statable
against the pinned Mathlib.

**Do not try to apply this to `LiteralBlockNormalForm.Model`.**  That is the
tempting next step and it does not work, for a reason that is worth spelling
out because the two groups look interchangeable.

`Model = LampFactor ⋊ Vertical`, where `LampFactor` is the Clifford group
`C(𝒢)` of the *orbital* graph.  Its braiding relator `IsLampRelator.braiding`
is gated on `Adjacent ξ η`, so between non-adjacent sites the presentation
imposes **no** relation and the two involutions generate an infinite dihedral
group.  `LampFactor` is therefore **not** locally finite (given a non-adjacent
pair, which is the generic case), and `isLocallyFiniteGroup_of_central_involution`
does not apply to it --- that lemma wants `⁅a, b⁆ ∈ zpowers z` for *every*
pair drawn from the generating set.  Structurally `C(𝒢)` is an amalgam
`∗_{⟨ζ⟩} Pᵢ`, and a nontrivial amalgam of that shape is never locally finite.
Amenability is no substitute either: with enough pieces such an amalgam
contains free subgroups.

The manuscript's `Cl(X)` is a *different* group and the hypothesis really does
hold for it: its braiding (`CliffordLamp.commutator_lamp_lamp`) fires for every
**distinct** pair with no adjacency side condition, so its graph is complete,
`W/⟨ζ⟩` is elementary abelian as `Theorem (commuting-generator quotient)`
prints, and `isLocallyFiniteGroup_cliffordLamp` goes through.  So this
corollary is sound exactly where the manuscript uses it, and unsound for the
literal orbital-graph model.

The general lesson: sameness of constructor is not sameness of instance.  Both
groups are `PresentedGroup` Clifford groups built the same way; the hypothesis
transfers only because the *relator family* differs. -/
theorem hasPropertyA_semidirectProduct_of_isLocallyFiniteGroup {N : Type u}
    {H : Type u} [Group N] [Group H] {φ : H →* MulAut N}
    (hN : IsLocallyFiniteGroup N) (hH : HasPropertyA H) :
    HasPropertyA (SemidirectProduct N H φ) :=
  hasPropertyA_semidirectProduct
    (hasPropertyA_of_isLocallyFiniteGroup_viaAmenability hN) hH

end ExactnessPermanence
end GroupApproximation
