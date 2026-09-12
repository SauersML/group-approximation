---
rg: 2
id: k0-hahn-banach-for-boundary-singular-classes
kind: claim
title: Boundary singular K_0-classes of nuclear quasidiagonal algebras with quasidiagonal traces are killed by faithful models
distinct_from:
  stw07-sign-changing-qd-trace-values-kill-class: that is the established case where the class takes both strict signs on quasidiagonal traces; this is the remaining boundary case, where it vanishes on a nonempty face and is one-signed elsewhere.
  moutzouris-qd-extensions-y-class: that proves the embedding property for explicit classes by classification; this asks for the boundary case in every nuclear quasidiagonal algebra all of whose traces are quasidiagonal.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**OPEN.**  Let `A` be separable, unital, nuclear and quasidiagonal, with
every tracial state quasidiagonal.  Let `x in K_0(A)` satisfy
`Zx cap K_0^+(A) = {0}` and `(Tr tensor tau)(x) >= 0` for all tracial states,
with equality on a nonempty face.  Then some faithful model of `A` has
`K_0`-value `0` on `x`.

Together with `stw07-sign-changing-qd-trace-values-kill-class` and
`stw07-singular-classes-change-sign-or-sit-on-boundary`, this is exactly the
K_0-Hahn--Banach property for such `A`.  That covers infinitesimal classes
(`x^` identically zero) and classes supported on proper trace faces.

## Attempts

- **Balancing by trace models: insufficient.**  Models tracking a zero-face
  trace have values `o(k_n)` of undetermined sign.  Every positive
  homomorphism `K_0(A) -> R` is a multiple of a state, hence a trace, hence
  `>= 0` on `x`.  So negative values must come from non-archimedean model
  data, never from traces.
- **Finite rank data: consistent.**  Artifact Lemma 3: on every finite window
  a positive rank functional with value `-1` (or `0`) on `x` and value `>= 1`
  on prescribed nonzero projections exists.  The hinge is realisation by an
  actual asymptotically multiplicative model, i.e. an existence theorem for
  models with prescribed local `K_0` data.
- **Known realisations.**  Finite-dimensional stages (AF), point
  evaluations and Voiculescu-type almost commuting pairs (`C(X) tensor K`,
  Brown--Dadarlat), the suspension flip `t -> -t` negating values on
  `K_0(SB)`, and Moutzouris' classification-based maps for the class `Y`.
  No general mechanism is recorded.
- **Next attack: K-homology realisation.**  Under the UCT a positive local
  rank functional lifts to a K-homology class.  The hinge is then whether
  classes positive on `K_0^+` are realised by discrete asymptotic
  representations `A -> M_(k_n)`.  The candidate inputs are Dadarlat--Loring,
  *K-homology, asymptotic representations, and unsuspended E-theory*,
  J. Funct. Anal. 126 (1994), and Gabe's unsuspension criterion (Corollary E
  of arXiv:1804.08095).  Note that `Prim(A)` of a unital `A` is compact, so
  unsuspension fails there.  Neither source has been read for this claim yet.
