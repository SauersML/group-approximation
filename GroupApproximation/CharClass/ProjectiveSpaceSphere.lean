-- Re-proved in the `GroupApproximation.CharClass` namespace from the paused fleet's
-- `GroupApproximation/AlgTop/ComplexProjectiveSphere.lean`, which is red at the pin and owned by no
-- lane of the LIX program.  Lane `cc-projective` owns this copy.
import GroupApproximation.CharClass.ProjectiveSpaceTwoCover
import GroupApproximation.AlgTop.PuncturedNormedSphere

/-!
# The intersection of the Mayer–Vietoris cover is a sphere

The last homotopy-theoretic input for `H^*(ℂP^n; ℤ)`. The cover of `ℂP^{d+1}` from
`GroupApproximation/AlgTop/ComplexProjectiveCover.lean` has

```text
chartSet (d+1) ∩ punctured d  ≅  ℂ^{d+1} ∖ {0}  ≃  S^{2d+1}.
```

The first identification is `CPn.chartPuncturedHomeo`; the second is
`AlgTop.complexPuncturedHomotopyEquivSphere` from
`GroupApproximation/AlgTop/PuncturedNormedSphere.lean`, which is model-independent and
lives in its own module so that it compiles without the projection model.

## Main results

* `CPn.interHomotopyEquivSphere d` — the Mayer–Vietoris intersection is `S^{2d+1}`;
* `CPn.contractibleSpace_chartSet d` — the other piece of the cover is contractible.

Combined with `CPn.punctureHomotopyEquiv` (the second piece is `ℂP^d`) this pins down
every term of the Mayer–Vietoris sequence for `ℂP^{d+1}`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Matrix
open GroupApproximation.STW59
open GroupApproximation.AlgTop

namespace CPn

/-- **The intersection of the Mayer–Vietoris cover of `ℂP^{d+1}` is homotopy equivalent
to `S^{2d+1}`.** -/
def interHomotopyEquivSphere (d : ℕ) :
    ContinuousMap.HomotopyEquiv
      ↥(chartSet (d + 1) ∩ {x : CP (d + 1) | x ≠ basePoint (d + 1)})
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * (d + 1)))) 1) :=
  ((chartPuncturedHomeo (d + 1)).symm.toHomotopyEquiv).trans
    (complexPuncturedHomotopyEquivSphere d)

/-- The other piece of the cover is contractible: it is homeomorphic to a real vector
space. -/
theorem contractibleSpace_chartSet (d : ℕ) : ContractibleSpace ↥(chartSet d) :=
  (chartHomeo d).symm.contractibleSpace

end CPn

end GroupApproximation.CharClass
