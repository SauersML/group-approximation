---
rg: 2
id: hyperoctahedral-reflection-q-overlap-groupifier
kind: claim
title: Close only the balanced overlap cycles on the common hyperoctahedral accepting corner
distinct_from:
  standard-reflection-sector-bcs-groupifier: that leaves both predicate placement and overlaps in one standard symmetric-group complement; here every predicate and every edgewise rank match is explicit and only cycle closure remains.
  signed-hecke-block-escaping-cycle-holonomy: this fixes the accepting corner to the arbitrarily high-density complement of one coordinate reflection.
---

**OPEN.**  Starting from the exact common-`q` context packets and incidence
permutations of `hyperoctahedral-reflection-common-q-context-atlas`, realize
the residual cycle transports by finite-support algebraic unitaries in
`q C[Gamma] q` so that all shared-variable signed marginals become literally
equal, while at least one context block leaves `q C[K_N] q` and one exact
marked representation survives.

The open content is precisely the signed-Hecke block-escaping cycle.  By
`common-reflection-defect-is-holonomy-spectator`, the rank-one complement
cannot participate in or repair the accepting-corner return map.  Thus this
claim is a density-normalized specialization of
`signed-hecke-block-escaping-cycle-holonomy`, not an independent mechanism.

## Attempts

- Conjugate every context partition by a free-phase unitary fixing `e`:
  edgewise binary marginals are preserved exactly, but compression to `q`
  is the old one-marginal free-phase cell and the first cycle retains its
  unconstrained return.
- Let a context transporter mix `e` and `q`: impossible for a complete
  context PVM with unit `q`, because equality of the transported and target
  partition sums forces `WqW^*=q`.
- Use one literal group-word conjugator preserving `q` for each context:
  `hyperoctahedral-corner-support-forces-packet-normalizer` shows
  that `supp(q)` generates the full finite packet.  Any such conjugator must
  therefore normalize `K_N`, so every transported context remains in the
  original finite root corner and exact overlap closure gives a forbidden
  finite-dimensional strategy.  The required return must be a genuinely
  multi-piece algebraic corner unitary, not `qgq` for one group element `g`.
- Allow arbitrary finite-support multi-piece unitaries: this is the genuinely
  surviving case, but `primitive-packet-corner-is-matrix-over-hecke-atom`
  gives its exact normal form.  The common packet corner is a full matrix
  algebra over one rank-one Hecke atom.  A unitary fixing already closed
  marginals is block diagonal over that Hecke algebra on their joint sign
  fibers; singleton fibers are immovable, and every possible escape lies in
  a nonsingleton collision block.  Thus the open cycle equation has no
  additional hidden normalizer freedom: it is precisely a coupled unitary
  equation over those rank-one Hecke blocks.
