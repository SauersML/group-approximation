import GroupApproximation.GGT.KazhdanHyp
import GroupApproximation.GGT.KazhdanHypGirthEight

/-!
# The cyclic Fano triangle presentation as an exact certificate calibration

This module instantiates the deterministic triangular-property-`(T)` pipeline
on the smallest source-defined example.  Herron, *Triangle Presentations
Encoded by Perfect Difference Sets*, Construction 4.1, Theorem 4.2 and the
order-two row of the examples table, starts from the perfect difference set
`{1,2,4}` in `Z/7Z`.  Its multiplier-two orbit gives the seven cyclic triples

```
  (j, j + 1, j + 3),  j in Z/7Z.
```

The link convention is checked against Kotowski--Kotowski, *Random groups and
property (T): Zuk's theorem revisited*, Definition 2.4: a relator `(x,y,z)`
adds the three edges `(x,y^-1)`, `(y,z^-1)`, `(z,x^-1)`.  For the triples
above, the three directed differences are `1`, `2` and `4`, so the link is the
incidence graph of the order-two cyclic projective plane, the Heawood graph.

The file proves all finite incidence and link identities by kernel evaluation,
then feeds the resulting `ProjectivePlaneData` to the rational Gram certificate
of `GGT/KazhdanHypLinkGap.lean`.  The certified rational gap is `19/36`, which
is strictly above Zuk's `1/2` threshold, so the presented group has the exact
repository predicate `HasKazhdanPropertyT.{0,0}`.

This is a calibration object rather than the hyperbolic witness sought by
`Hyperbolic.SharpExistence`.  Its Heawood link has girth six: the final section
exhibits three length-three paths across a non-edge, so
`GirthEightChecks fanoTriangles 3` fails.  This is the finite form of the
Euclidean `A~_2` obstruction and fixes the target for a future structured
construction at girth at least eight.
-/

namespace GroupApproximation
namespace KazhdanHyp
namespace FanoCalibration

/-! ## The perfect difference set and its seven triangles -/

/-- The order-two perfect difference set from the source examples table. -/
def fanoDifferenceSet : Finset (ZMod 7) := {1, 2, 4}

/-- The source set has three elements, as required for a plane of order two. -/
theorem fanoDifferenceSet_card : fanoDifferenceSet.card = 3 := by
  decide

/-- Multiplication by two cyclically permutes `1`, `2`, and `4`. -/
theorem fanoDifferenceSet_mul_two :
    fanoDifferenceSet.image (fun x : ZMod 7 => 2 * x) = fanoDifferenceSet := by
  decide

/-- The multiplier orbit closes because `1 + 2 + 4 = 0` in `Z/7Z`. -/
theorem fanoDifferenceSet_sum : (1 : ZMod 7) + 2 + 4 = 0 := by
  decide

/-- The seven nonredundant triangles obtained from the source construction
`(j, j+d, j+d+2d)` with `d=1`.  All letters are positive. -/
def fanoTriangles (j : ZMod 7) : TriangularHodgeLayer.Triangle (ZMod 7) :=
  ![(j, true), (j + 1, true), (j + 3, true)]

@[simp] theorem fanoTriangles_zero (j : ZMod 7) :
    fanoTriangles j 0 = (j, true) := rfl

@[simp] theorem fanoTriangles_one (j : ZMod 7) :
    fanoTriangles j 1 = (j + 1, true) := rfl

@[simp] theorem fanoTriangles_two (j : ZMod 7) :
    fanoTriangles j 2 = (j + 3, true) := rfl

/-- Every letter in the cyclic Fano table is positive. -/
theorem fanoTriangles_positive : ∀ j k, (fanoTriangles j k).2 = true := by
  intro j k
  fin_cases k <;> rfl

/-- The table has the seven relators stated in the source. -/
theorem fanoTriangleCount : Fintype.card (ZMod 7) = 7 := by
  exact ZMod.card 7

/-! ## The cyclic Fano incidence table -/

/-- Point `x` is incident to line `y` when the cyclic difference `y-x` lies
in the perfect difference set `{1,2,4}`. -/
def fanoIncidence (x y : ZMod 7) : ℚ :=
  if y - x ∈ fanoDifferenceSet then 1 else 0

/-- Every point is incident to three lines. -/
theorem fanoIncidence_rowSum :
    ∀ x : ZMod 7, ∑ y, fanoIncidence x y = 3 := by
  intro x
  fin_cases x <;> decide

/-- Every line contains three points. -/
theorem fanoIncidence_colSum :
    ∀ y : ZMod 7, ∑ x, fanoIncidence x y = 3 := by
  intro y
  fin_cases y <;> decide

/-- Two distinct points lie on one common line; a point has three incident
lines.  This is the row identity `N Nᵀ = 2I + J`. -/
theorem fanoIncidence_rowPair : ∀ x x' : ZMod 7,
    ∑ y, fanoIncidence x y * fanoIncidence x' y =
      2 * (if x = x' then 1 else 0) + 1 := by
  intro x x'
  fin_cases x <;> fin_cases x' <;> decide

/-- Two distinct lines meet in one point; a line contains three points.
This is the column identity `Nᵀ N = 2I + J`. -/
theorem fanoIncidence_colPair : ∀ y y' : ZMod 7,
    ∑ x, fanoIncidence x y * fanoIncidence x y' =
      2 * (if y = y' then 1 else 0) + 1 := by
  intro y y'
  fin_cases y <;> fin_cases y' <;> decide

/-- The cyclic incidence matrix is a projective plane of order two in the
exact rational interface consumed by the link certificate. -/
def fanoPlane : ProjectivePlaneData (ZMod 7) where
  inc := fanoIncidence
  order := 2
  order_gt_one := by norm_num
  rowSum := by
    intro x
    simpa using fanoIncidence_rowSum x
  colSum := by
    intro y
    simpa using fanoIncidence_colSum y
  rowPair := fanoIncidence_rowPair
  colPair := fanoIncidence_colPair

/-- The point count derived by the general projective-plane interface agrees
with the literal seven-element generator type. -/
theorem fanoPlane_card_identity :
    (Fintype.card (ZMod 7) : ℚ) = (fanoPlane.order + 1) ^ 2 - fanoPlane.order :=
  fanoPlane.card_eq

/-! ## Identification of the presentation link -/

/-- The link of the seven cyclic triangles is three-regular. -/
theorem fanoLink_regular :
    ∀ u, TriangularHodgeLayer.degree fanoTriangles u = 3 := by
  rintro ⟨x, s⟩
  fin_cases x <;> cases s <;> decide

/-- The presentation link is exactly the incidence graph of `fanoPlane`.
The equality includes edge multiplicities, matching the convention in
Kotowski--Kotowski, Definition 2.4. -/
theorem fanoLink_eq : ∀ u v,
    (TriangularHodgeLayer.adjacencyCount fanoTriangles u v : ℚ) =
      fanoPlane.linkAdj u v := by
  rintro ⟨x, s⟩ ⟨y, t⟩
  fin_cases x <;> fin_cases y <;> cases s <;> cases t <;> decide

/-- The source-defined table packaged with its computed projective-plane
link. -/
def fanoPresentation : TrianglePresentation (ZMod 7) (ZMod 7) where
  triangles := fanoTriangles
  plane := fanoPlane
  linkDegree := 3
  linkDegree_eq := by norm_num [fanoPlane]
  link_regular := fanoLink_regular
  link_eq := fanoLink_eq

/-! ## Exact rational property-`(T)` certificate -/

/-- The completed-square certificate uses the rational gap `19/36`. -/
theorem fanoCertificate_gap : (fanoPlane.linkData).gapValue = 19 / 36 := by
  rw [fanoPlane.linkData_gapValue]
  norm_num [fanoPlane]

/-- The certified gap clears the strict threshold in Zuk's criterion. -/
theorem fanoCertificate_gap_gt_half :
    (1 : ℚ) / 2 < (fanoPlane.linkData).gapValue := by
  rw [fanoCertificate_gap]
  norm_num

/-- The literal `LinkCertificateChecks` object for the cyclic Fano table.
Its rows are the rational Gram rows constructed by completing the square for
the Fano incidence matrix. -/
noncomputable def fanoLinkCertificate :
    TriangularHodgeLayer.LinkCertificateChecks fanoTriangles 3
      (fanoPlane.linkData).gapValue (fanoPlane.linkData).gramRow :=
  linkCertificateChecks_of_linkData fanoTriangles fanoPlane.linkData 3
    fanoLink_regular (by norm_num [fanoPlane]) fanoLink_eq

/-- The seven-generator cyclic Fano presentation has Kazhdan's property
`(T)`, in the exact universe used by `Hyperbolic.SharpExistence`. -/
theorem fano_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (TriangularHodgeLayer.Presented fanoTriangles) :=
  TriangularHodgeLayer.presented_hasKazhdanPropertyT_of_linkCertificate
    fanoTriangles 3 (fanoPlane.linkData).gapValue
      (fanoPlane.linkData).gramRow fanoLinkCertificate

/-- The same property-`(T)` conclusion through the bundled presentation
interface. -/
theorem fanoPresentation_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} fanoPresentation.Carrier :=
  fanoPresentation.hasKazhdanPropertyT

/-- Finite presentation is automatic for the literal finite triangle table. -/
theorem fano_isFinitelyPresented :
    Group.IsFinitelyPresented (TriangularHodgeLayer.Presented fanoTriangles) :=
  inferInstance

/-! ## The checked girth-six obstruction -/

/-- A point and its equally labelled line are not adjacent in the cyclic Fano
incidence graph. -/
theorem fano_zero_nonedge :
    TriangularHodgeLayer.adjacencyCount fanoTriangles
      ((0, true) : ZMod 7 × Bool) ((0, false) : ZMod 7 × Bool) = 0 := by
  decide

/-- There are three length-three link paths from point zero to the nonincident
line zero.  In particular the link contains six-cycles. -/
theorem fano_zero_threePaths :
    (∑ a, ∑ b,
      TriangularHodgeLayer.adjacencyCount fanoTriangles ((0, true) : ZMod 7 × Bool) a *
      TriangularHodgeLayer.adjacencyCount fanoTriangles a b *
      TriangularHodgeLayer.adjacencyCount fanoTriangles b ((0, false) : ZMod 7 × Bool))
      = 3 := by
  decide

/-- The Fano calibration table is outside the girth-eight geometric pipeline.
This is a concrete refutation rather than an appeal to the Euclidean building:
the final `GirthEightChecks` clause would bound the displayed path count by
one, while it is exactly three. -/
theorem fano_not_girthEight : ¬ GirthEightChecks fanoTriangles 3 := by
  intro h
  have hle := h.2.2.2.2 ((0, true) : ZMod 7 × Bool)
    ((0, false) : ZMod 7 × Bool) fano_zero_nonedge
  rw [fano_zero_threePaths] at hle
  omega

end FanoCalibration
end KazhdanHyp
end GroupApproximation
