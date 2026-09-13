---
rg: 2
id: archimedean-trace-pushouts-give-qd-killing
kind: claim
title: In real rank zero, projection traces that see every projection and have quasidiagonal co-ideal quotients give a killing quasidiagonal embedding
distinct_from:
  rr0-projection-traces-give-qd-killing: that is the open claim with only the trace condition at each projection; this adds the archimedean positivity at every projection and quasidiagonality of the quotients by projection-generated ideals, and proves killing.
  bk-radical-traces-vanishing-on-boundary-are-zero: that treats one densely finite trace on the whole radical; this uses many traces finite only on projection-generated ideals and glues their pushouts.
  bk-projection-generated-ideals-with-uct-quotients-force-qd: that needs a full projection in every ideal; this allows infinitely many ideals under archimedean positivity and quasidiagonal quotients.
artifacts:
  - research/artifacts/bk-rr0-trace-pushout-killing-part2-2026-09-13.md
---

**ESTABLISHED (Theorem D of the artifact; lane proof, not externally reviewed).**
Let `A` be separable, nuclear, of real rank zero, with every quotient UCT, and
`G ⊆ K_0(A)` singular.  Suppose that for every finitely generated `G_0 ⊆ G`
and every nonzero projection `Q ∈ A` there are a projection `P ∈ A` and a
lower semicontinuous trace `σ` such that:
- **(H1)** `Q ∈ I_P`, and `G_0 ⊆ im(K_0(I_P) -> K_0(A))`.  Also `σ(P) = 1`,
  `σ` is finite exactly on `I_P`, it annihilates `G_0` on `I_P`, and
  `σ(Q) > 0`.
- **(H2)** `A/I_P` is quasidiagonal.

Then some faithful \*-homomorphism of `A` into a quasidiagonal algebra kills `G`.

Mechanism.
- *Proposition R2.*  Kill the subgroup on the corner of `I_P/ker σ` by
  Schafhauser's realisation.  Then pull the extension back over `A/I_P` to get
  zero boundary, and apply Brown–Dadarlat Theorem 3.4.  The result is a map with
  kernel `ker σ` killing `G_0`.
- *Separation.*  `σ(Q) > 0` makes these kernels separate `A`, since every
  nonzero ideal contains such a `Q`.
- *Gluing.*  `separating-killing-quotients-give-faithful-qd-killing` glues the
  maps.

Residual hinges for `rr0-projection-traces-give-qd-killing`:
- (H1) fails exactly at projections infinitesimal modulo `G` relative to every
  larger projection, the non-archimedean exhaustions;
- (H2) asks the quotients by projection-generated ideals to be quasidiagonal.
