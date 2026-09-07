(* Reproduce the symbolic identities in the paired-projector obstruction.
   Run: wolframscript -file scripts/check_qpcp_rounding.wl
   Not executed in the 2026-09-07 session: Wolfram MCP returned HTTP 404.
   This verifies finite matrix algebra, not the quantum PCP conjecture. *)
ClearAll[n, d, p, w, q, k, g, f, checks];
d = n^2 + 1;
p = {{0, 0}, {0, 1}};
w = {2 n, n^2 - 1}/d;
q = Outer[Times, w, w];
k = p + q;
g = {n, -1};
f = {1, n};
checks = <|
  "unitVector" -> FullSimplify[w.w == 1, Element[n, Reals]],
  "projector" -> FullSimplify[q.q == q, Element[n, Reals]],
  "groundVector" -> FullSimplify[k.g == (2/d) g, Element[n, Reals]],
  "upperVector" -> FullSimplify[k.f == (2 n^2/d) f, Element[n, Reals]],
  "orthogonal" -> FullSimplify[g.f == 0, Element[n, Reals]],
  "orderedEigenvalues" -> FullSimplify[2/d <= 2 n^2/d, n >= 1],
  "positiveDeterminant" -> FullSimplify[Det[k] == 4 n^2/d^2, n >= 1],
  "normalizedEnergy" -> FullSimplify[(g.k.g)/(2 g.g) == 1/d, n >= 1],
  "sharpCostIdentity" -> FullSimplify[(d/2) (2 n/d) == n, n >= 1],
  "singletonCoverObstruction" -> FullSimplify[2/d < 1, n > 1],
  "zeroEnergyRegression" -> (p.{1, 0} == {0, 0})
|>;
Print[ExportString[checks, "RawJSON"]];
If[!TrueQ[And @@ Values[checks]], Exit[1]];
