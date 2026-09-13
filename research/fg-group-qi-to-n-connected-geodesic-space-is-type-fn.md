---
rg: 2
id: fg-group-qi-to-n-connected-geodesic-space-is-type-fn
kind: claim
title: A finitely generated group quasi-isometric to an (n-1)-connected proper geodesic space is of type F_n
---

For every n ≥ 2: if a finitely generated group G is quasi-isometric to a
proper geodesic metric space X that is (n − 1)-connected, then G is of type
F_n.

This is the affirmative answer to Zaremsky Problem 1.3 under the geodesic
reading (`zaremsky-1-03-qi-to-connected-space-implies-type-fn`).

## Attempts

- Case n = 2 (lane z1-03-qi-fn, 2026-09-13): proved; the write-up is landing
  as its own claim. Geodesics realize the edges of a coarse loop, and a disc
  in X fills the resulting continuous loop. A fine triangulation of that disc
  projects to a filling in a Rips complex of G at a scale fixed by the
  quasi-isometry constants. So G is coarsely simply connected, hence finitely
  presented.
- General n by induction (where it dies): to realize a coarse k-sphere of G
  in X we must fill the boundaries of its small simplices. Plain
  (k − 1)-connectedness of X gives fillings of unbounded diameter. The
  projected sphere then differs from the original by the spheres
  `sigma ∪ proj(h_sigma)` (a small simplex together with a large filling of
  its boundary), and nothing bounds these at a fixed scale. If X is
  **uniformly** (n − 1)-connected (spheres of diameter ≤ r bound balls of
  diameter ≤ phi(r)), the induction goes through; this is the standard route
  to quasi-isometry invariance of F_n. The question is whether uniformity can
  be removed for n ≥ 3.
