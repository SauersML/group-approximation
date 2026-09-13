---
rg: 2
id: thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2
kind: claim
title: Thompson's group F has no cobounded isometric action on a geodesic space quasi-isometric to H^2
distinct_from:
  thompson-f-has-no-cobounded-action-on-hyperbolic-plane: that claim is only about isometries of H^2 itself, proved by linearity; this claim is about all geodesic spaces quasi-isometric to H^2, whose isometry groups need not be linear, and needs quasi-action rigidity
---

For every geodesic metric space `X` quasi-isometric to the real hyperbolic plane `H^2`,
every isometric action of Thompson's group `F` on `X` has no coarsely dense orbit.
Equivalently: no hyperbolic structure on `F` (in the sense of Abbott–Balasubramanya–Osin)
is representable by an action on a space quasi-isometric to `H^2`. This is the last
sentence of Question 11.4 of arXiv:2406.12982 (Balasubramanya–Fournier-Facio–Zaremsky),
the source of Zaremsky Problem 2.18.

## Attempts

- **Reduction to Möbius rigidity (2026-09-13, lane z2-18-f-h2-action; not yet a proof).**
  Suppose `F` acts coboundedly on `X` and `φ: X → H^2` is a `(K,C)`-quasi-isometry.
  Conjugating by `φ` gives a quasi-action of `F` on `H^2` by `(K',C')`-quasi-isometries
  with uniform constants, still cobounded. Planned chain:
  1. (M1) boundary maps of `(K',C')`-quasi-isometries of `H^2` are `η`-quasisymmetric
     homeomorphisms of `S^1` with `η` depending only on `K', C'`; this gives a homomorphism
     `∂: F → Homeo(S^1)` onto a uniformly quasisymmetric group `Γ`.
  2. (M2) Markovic, *Quasisymmetric groups*, J. Amer. Math. Soc. 19 (2006): every uniformly
     quasisymmetric group of circle homeomorphisms is quasisymmetrically conjugate to a
     Möbius group. So `Γ` is isomorphic to a subgroup of `PGL_2(R)`, which is linear.
  3. The algebra of `thompson-f-has-no-cobounded-action-on-hyperbolic-plane-proof`
     (Tits alternative, simplicity of `[F,F]`) applies verbatim to `∂`, so `Γ` is abelian.
  4. (M3) extend the conjugating quasisymmetric map to a quasi-isometry of `H^2`
     (Beurling–Ahlfors or Douady–Earle extension); after conjugation each element is a
     uniform quasi-isometry with Möbius boundary map `m_g`.
  5. (M4) a `(K,C)`-quasi-isometry of `H^2` with the same boundary map as an isometry `m` is
     within `D(K,C)` of `m`. Provable: every point is uniformly close to all three sides of
     some ideal triangle, and by stability of quasi-geodesics the images of the sides stay
     within `M(K,C)` of the sides of the image triangle.
  6. So the quasi-action is at uniformly bounded distance from the isometric action of the
     abelian group `{m_g}`, which has no coarsely dense orbit by
     `abelian-isometry-groups-of-h2-are-not-cobounded`. Contradiction.
  **Where it stands:** (M1)–(M3) are standard, but their exact statements and theorem
  numbers have not been read from sources (no web search this session). Step 2 in particular
  must be checked for orientation-reversing maps (pass to the orientation-preserving
  subgroup of index at most 2; the kernel of `∂` lies in it and is normal in `F`, so Step 3
  still gives an abelian image).
- **Structure check (consistent with the reduction).** A cobounded action on such an `X` has
  limit set `∂X = S^1`, so it is neither elliptic, horocyclic nor lineal; it is not of general
  type because `F` has no free subgroups. By arXiv:2406.12982 Theorem A it is quasi-parabolic,
  attached to an endpoint character. The claim says none of these quasi-parabolic structures
  is quasi-isometric to `H^2`, the way the "real place" structure of `BS(1,2)` is.
