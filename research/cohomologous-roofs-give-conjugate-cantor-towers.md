---
rg: 2
id: cohomologous-roofs-give-conjugate-cantor-towers
kind: claim
title: Towers over an infinite minimal Cantor system with cohomologous continuous roofs are conjugate
---
**Statement.**
- Let (Z,σ) be an infinite minimal Cantor system, and let r, r′: Z → {1,2,…} be continuous with r′ − r = h − h∘σ for
  some continuous h: Z → Z.
- Then the towers X_r = {(z,i) : 0 ≤ i < r(z)} and X_{r′} are topologically conjugate. In each, the map sends (z,i) to
  (z,i+1) below the roof and to (σz,0) at the roof.
- The conjugacy is Φ(T_r^n(z,0)) = T_{r′}^{n+h(z)}(z,0).

**Corollary (induced systems with matching unit class).**
- Let (X,T) and (Y,S) be infinite minimal Cantor systems, U ⊆ X and V ⊆ Y nonempty clopen, and θ: U → V a
  homeomorphism conjugating the induced maps T_U and S_V.
- Suppose θ carries the class of the return time r_U in K^0(U,T_U) to the class of r_V. This is the image of [1_X]
  under induction.
- Then (X,T) ≅ (Y,S). If θ conjugates T_U to S_V^{-1} instead, then (X,T) ≅ (Y,S^{-1}).

**Credit.** Folklore: it is the discrete form of "cohomologous roof functions give conjugate suspension flows". Towers
and induced systems go back to Kakutani, and to Herman–Putnam–Skau and Glasner–Weiss for Cantor minimal systems.
Novelty check: a grep of main only.

Full proof: `research/artifacts/sk-cartan-counterexample-2026-09-13-part1.md` §1.
