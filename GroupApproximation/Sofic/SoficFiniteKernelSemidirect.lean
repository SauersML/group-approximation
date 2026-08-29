import GroupApproximation.Sofic.Sofic
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Soficity of split extensions with finite kernel

If a sofic group `G` acts on a finite group `N`, then `N ⋊ G` is sofic.  The
proof is direct.  A local permutation model `σ` for `G` acts on `N × Y` by

`(n,g) · (a,y) = (n * g(a), σ(g)y)`.

The first coordinate is exactly multiplicative; every defect is confined to
the second coordinate.  This is the finite-stage permanence theorem required
by the Clifford coset tower.
-/
