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

- **Not a reduction (2026-09-11).**  By
  `stw07-trace-invisible-classes-carry-hahn-banach`, applying this claim to
  `(A tensor K)~` kills every singular class of every separable nuclear
  quasidiagonal `A`.  So this claim is equivalent to
  `every-separable-nuclear-qd-algebra-has-k0-hahn-banach`.  The sharpened
  residual below applies only to algebras whose traces see their ideals.

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
- **Sharpened residual (2026-09-11).**
  `stw07-quotient-trace-zero-nontorsion-class-is-killed` kills `x` whenever
  some zero trace has a UCT kernel quotient in which `x` is non-torsion.
  Under UCT for trace-kernel quotients, what survives is exactly (artifact
  Section 8): a class supported on the ideal `J_F`, the intersection of the
  zero-face kernels, which is positive on every bounded trace that sees `J_F`
  and nonpositive only on unbounded or corner traces of `J_F`.  Negative
  models exist on corners of `J_F`.  The open step is extending ideal models
  to asymptotically multiplicative models of `A`, as in Moutzouris
  Propositions 3.1--3.2.
- **Next attack: K-homology realisation.**  Under the UCT a positive local
  rank functional lifts to a K-homology class.  The hinge is then whether
  classes positive on `K_0^+` are realised by discrete asymptotic
  representations `A -> M_(k_n)`.  The candidate inputs are Dadarlat--Loring,
  *K-homology, asymptotic representations, and unsuspended E-theory*,
  J. Funct. Anal. 126 (1994), and Gabe's unsuspension criterion (Corollary E
  of arXiv:1804.08095).  Note that `Prim(A)` of a unital `A` is compact, so
  unsuspension fails there.  Neither source has been read for this claim yet.
