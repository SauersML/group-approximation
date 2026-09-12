---
rg: 2
id: square-pg23-kazhdan-hyperbolic-complex-exists
kind: claim
title: A finite square complex with PG(2,3) links has a Kazhdan hyperbolic fundamental group with b_2 at least one
distinct_from:
  kazhdan-two-complex-b2-is-euler-characteristic-minus-one: that is the proved b_2 and hyperbolicity computation for any such complex; this asserts that a finite complex of that shape exists and has property (T), inputs taken from the literature that are not yet source-verified here
  torsion-free-hyperbolic-kazhdan-partner-exists: that is an established existence theorem for some hyperbolic Kazhdan group with no Betti number information; this pins an explicit shape whose b_2 is computable from the vertex count
---

**OPEN (literature inputs unverified).** There is a finite connected square
complex `K` with at least two vertices, all corner angles `π/3` in the hyperbolic
metric, and every vertex link isomorphic to the incidence graph of `PG(2,3)`, such
that `Γ = π_1(K)` has property (T).

Given this, `kazhdan-two-complex-b2-is-euler-characteristic-minus-one` makes `Γ` an
explicit torsion-free hyperbolic Kazhdan group with `b_2(Γ) = |V| - 1 >= 1`. That is
a pinned candidate for `kazhdan-hyperbolic-b2-group-flexibly-hs-stable`.

## Inputs to verify at source

* **Property (T).** Żuk's criterion (Ballmann--Świątkowski for polygonal complexes):
  (T) holds when every link is connected with smallest positive normalized Laplacian
  eigenvalue `> 1/2`. The `PG(2,3)` incidence graph has normalized adjacency
  eigenvalues `±1`, `±√3/4`, so the gap is `1 - √3/4 ≈ 0.567`.
* **Existence.** Finite complexes with these links, e.g. torsion-free uniform lattices
  in the Fuchsian building with Coxeter group `⟨s_1..s_4 | s_i^2, (s_i s_(i+1))^3⟩`
  and projective-plane links (Bourdon; Gaboriau--Paulin). Unverified.
