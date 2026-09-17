import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonDoublingTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# Outer-side thickening preserves a clean two-gon: dart correspondence

Target: `GroupApproximation.GGT.VanKampen.TwoGonOuterSideStepStatement`.

Notation. `M := S.diagram.toCombMap`, `w := FaceEdgeDoubling.dart S.diagram outerFace j` (the
first corner `w_j` of the rebased outer boundary), `b := M.facePerm w` (the second corner). The
thickened map `M'` is `EdgeInsertion.toCombMap M w b`, with darts `Option (Option M.Dart)`;
old darts enter through `embed z = some (some z)`, the new edge is `{none, some none}`.
Each old region `r ∈ S.family` becomes `r' := regionCandidate ⟨r, htgt r hr⟩`.

Mathematical proof.

(A) Crossings. For every region `r` and every side `s`, cell side `o`:
  `crossO r' s o = (crossO r s o).map embed`. The source arc is mapped by `embed`; the target
  arc by `targetImage`, which agrees with `embed` on every dart except `alpha w`, and by `htgt`
  the target arc of `r` never contains `alpha w`. `alpha` commutes with `embed` definitionally,
  and the Boolean selector of `crossO false` depends only on whether the target is `none`,
  which is preserved by `target' = target.map indexEquiv`.

(B) Faces. For `z ≠ w`, `faceOf' (embed z) = faceImage (faceOf z)`; `embed w` and `none` lie
  on the new digon, `some none` on the new outer face. New regions consist of face images of
  old region faces; neither the digon nor the new outer face lies in a region.

(C) Internal darts. `RegionInternal family' (embed z) ↔ RegionInternal family z`; the two new
  darts are not internal. Hence the collapsed maps are related by the embedding
  `ιc : x ↦ ⟨embed x, _⟩`, which commutes with `alpha`, and misses `some none`.

(D) Kept darts of the dual Phi map. `PhiKeepO family' E' (ιc x) ↔ PhiKeepO family E x` by (A)
  and injectivity of `embed`, where `E'` is the image of `E`; every kept new dart is in the
  range of `ιc` by (A). The dart `w` is not kept: a crossing on the cell side `true` lies on a
  relator cell face or, for an unbound target, is `alpha` of the head of the target arc, which
  differs from `w` by `htgt`; a crossing on side `false` lies on a region face, and `w` lies on
  the outer face, which belongs to no region.

(E) Rotation. Outside of `w`, the collapsed face rotation of the new map agrees with the old
  one along `ιc`; at the predecessor of `w` it goes to `some none`, and from `some none` it
  continues to `ιc (facePerm w)`. `PhiMapTransport.retainedEquiv_sigma_bypass` then gives an
  equivalence `e` of Phi maps commuting with `alpha` and `sigma`, hence with `facePerm`.

(F) Data. `linkedComponentO family' a₀'` is the image of `linkedComponentO family a₀`, since
  `sideCellO r' s = (sideCellO r s).map indexEquiv`. `ExtPhiData` transports field by field;
  `NoLoops` and `NoMultipleEdges` transport by injectivity of `indexEquiv` and
  `regionCandidate`.

(G) Two-gon. `phiRegionO (e y) = (phiRegionO y)'`, and side, cell side are equal (uniqueness of
  crossings). `IsTwoGon` transports along `e`. A gap-holding corner on the face of `e d` pulls
  back along `e⁻¹` to one on the face of `d` (same target profile). A holding cell on the new
  face pulls back along `backDart` (face class steps), and its cell face is the face image of
  an old relator cell face, whose index is not an end cell of `E` since its image is not an end
  cell of `E'`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide
