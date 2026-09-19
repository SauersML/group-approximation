# GL06e step 2: how it splits, and the smallest remaining lemma (ms-nm-uncond-a, 09-19)

Target: `GL06p.slitPocketCoreStatement`, the slit pocket core without its windows. Step 3
(`Full/GL06eSlit/Pocket`, green at 1fa4f9277) turns a simple or noncrossing slit walk into it.
This note is a hand analysis against origin/main. Nothing in it is built yet.

## Observation 1: the collar surgery is proved, so only values matter

`geodesicCollarStatement_holds : GeodesicCollarStatement` (SurgeryGeodesicCollarStripStep:458) takes a
pocket region whose two cycles both follow, and splits its inverse complement cycle as `s ++ rest`.
For any word `g` in the letters of `D` with the value of `s`, it returns:
- an O-equivalent copy with a pocket whose two cycles still follow;
- a new inverse complement cycle `collar ++ rest.map ι`, where `collar` reads `g`;
- relator cells outside the pocket that keep their darts, and cells that stay on their side.

`PocketRegion.withOuter` restarts the cycle, so the collar can be applied to each side in turn.

So every non-arc part of a pocket boundary can be re-spelled as a geodesic word of the same VALUE:
- the slits `s₁`, `s₂`: geodesic words of length `m` when their values have norm `m`, the class
  minimum (`MetricClassMinimal`, via `GL06p.metricClassMinimal_of_geodesic`);
- the collar part `g`: a geodesic word of the value of a ∂Δ-arc, so `|g| ≤ |∂Δ|`.

Extra darts in a slit or in `g` therefore cost nothing, as long as they keep its value. Examples are
the parallel edges of G-digons, and vertex blow-up edges labelled `RelLetter.comp λ 1` (value 1; `1 ∈ fam λ`).
This settles the letter-count objection to the end digons (nm-gl06e board, "end design"), except at
Π (see Observation 2).

## Observation 2: the Π part cannot absorb anything

The arc part must stay `invDarts copy arc.darts`, i.e. genuine darts of Π, and Π's word is fixed
by O-equivalence (`cellWord_eq`). A digon on an edge of ∂Π adds a pocket dart there that is not a
Π dart and carries a Π label, so it changes a slit's value if it is put into a slit.

With a single foot and a full arc, the complement is pinched at the foot and at Π. There
`OuterTurn` fails (`outerTurn_iff_followsBoundary`; the lake model `not_outerTurn_lakeCycle`), and
so `follows` fails.

## The split

- **(2b) Collar normalization. Mechanical; I am writing it.** Input: a seed pocket region, both
  cycles following, whose inverse complement cycle is `g₀ ++ s₁ ++ invDarts arc ++ s₂`, where `Π`
  is the arc's cell, `‖val s₁‖ = ‖val s₂‖ = m`, a relator cell is inside, and the feet are on ∂.
  Three collars and two rotations give `SlitPocketCore`. The arc and Π transport through `ι`
  because Π is outside the pocket.
  - Sub-lemma (V): `ι` of the collar output preserves the vertex of a `rest` dart at the foot.
    It is needed for `foot_in`; `foot_out` then follows from the chain of the following cycle.
    It is not exported by `GeodesicCollarOutput` today.
- **(2a) Seed: THE SMALLEST REMAINING LEMMA.** In some O-copy of the least-area `Δ` with a metric
  nearest walk (class minimum `m`), there is a SIMPLE closed walk `g₀ ++ s₁ ++ invDarts arc ++ s₂`
  such that:
  - its side contains a relator cell, and the exterior is not on it;
  - `arc` is a nonempty arc of a relator cell;
  - `‖val s₁‖ = ‖val s₂‖ = m`;
  - `s₁` starts, and `s₂` ends, at vertices of the outer face.

  Simplicity gives both followings (`PocketRegion.ofSimpleClosedWalk`), and the nonempty arc puts
  Π outside (`nearest_face_not_mem_sideFaces`). Only values are asked of `g₀`, `s₁`, `s₂`, so the
  ribbon may use G-digons and value-1 blow-up edges anywhere off ∂Π.

The one genuinely geometric point in (2a) is the Π end. The walk must turn from `s₁` into ∂Π and
back out into `s₂` without visiting a vertex twice and without adding a non-Π dart between the
slit and the arc. The suggested move is to blow up the transition vertex inside G-faces only: first
double the slit's end edge on the pocket side, then split the vertex, so that no relator word
changes. This needs a model test first: one interior cell at distance 1.
