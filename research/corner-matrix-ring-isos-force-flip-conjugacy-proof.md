---
rg: 2
id: corner-matrix-ring-isos-force-flip-conjugacy-proof
kind: route
title: Proof - corner groupoids are induced systems, and matching unit classes make the towers conjugate
target: corner-matrix-ring-isos-force-flip-conjugacy
requires:
  - cohomologous-roofs-give-conjugate-cantor-towers
  - diagonal-preserving-isomorphisms-reconstruct-effective-groupoids
  - topological-full-groups-determine-flip-conjugacy
artifacts: [research/artifacts/sk-cartan-counterexample-2026-09-13-part1.md]
---
Details are in the artifact §2.

1. **Corners are induced systems.** e_U R_X e_U is the Steinberg algebra of the reduction 𝒢_X|_U, and its diagonal is
   e_U D_X. X is minimal, so every arrow between two points of U on one orbit is a unique power of the induced map
   T_U, and 𝒢_X|_U = Z ⋉_{T_U} U.
2. **Flip conjugacy of the bases.** φ preserves diagonals, so `diagonal-preserving-isomorphisms-reconstruct-effective-groupoids`
   (effective groupoids, F_2 indecomposable) gives Z ⋉ U ≅ Z ⋉ V. This isomorphism carries full compact open
   bisections to full compact open bisections, so [[T_U]] ≅ [[S_V]]. Then
   `topological-full-groups-determine-flip-conjugacy` gives a homeomorphism θ: U → V with θ∘T_U = S_V^{±1}∘θ.
3. **Unit classes.** Induction ι_U(f)(u) = Σ_{i<r_U(u)} f(T^i u) descends to K^0(X,T) → K^0(U,T_U), with ι_U[1_X] = [r_U]
   and ι_U[1_U] = [1_U]. So [r_U] = n[1_U]. Likewise [r_V] = n[1_V], and θ_*[1_U] = [1_V] gives θ_*[r_U] = [r_V].
4. **Conclusion.** The corollary of `cohomologous-roofs-give-conjugate-cantor-towers` gives (X,T) ≅ (Y,S) or
   (X,T) ≅ (Y,S^{-1}). ∎
