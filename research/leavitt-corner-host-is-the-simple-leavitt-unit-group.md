---
rg: 2
id: leavitt-corner-host-is-the-simple-leavitt-unit-group
kind: claim
title: The negative-root corner host is the simple Leavitt unit group, so the corner diagram and hyperlinearity of L^x exclude each other
distinct_from:
  leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity: that treats characters of the support group <X,z> and reduces trace certificates on the Toeplitz class to hyperlinearity of EL_20(J); this treats characters of the whole host, identifies it with L^x, and shows trace certificates against every support are exactly hyperlinearity of L^x, using simplicity of the host in place of the finitary-kernel analysis.
  leavitt-steinberg-map-iso-from-rank-three: that imports St_r(R) = GL_r(R) for r >= 3 and records the rank-five consequence; this applies it at rank twenty to the corner host and derives the mutual exclusion with the open unit-group hyperlinearity claim.
  binary-leavitt-unit-group-hyperlinear: that is the open hyperlinearity target; this proves that closing the negative-root corner refutes it, and that refuting the corner by any embeddable character proves it.
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that makes any unital corner model of a no-CE-trace BCS force its host group to be nonhyperlinear; this identifies the host of LNC3 with L^x and adds the converse for trace certificates.
artifacts:
  - research/leavitt-corner-host-simple-unit-group-proof.md
---

**ESTABLISHED.**  Let `R=L_(F_2)(1,2)`, `Delta=St_20(R)`, `q=s_1t_1`,
`z=x_13(q)`, and let `LNC3` be the diagram of
`agent-leavitt-not-bcs-negative-root-corner`.

1. **Host.**  `Delta ~= GL_20(R) = E_20(R) ~= R^x`.  This group is simple and
   perfect, and by `openai-leavitt-unit-nonsofic` it is nonsofic.
2. **Certificates.**  A Connes-embeddable character `tau` of `Delta` with
   `tau(z) != 1` exists if and only if `R^x` is hyperlinear.
3. **Mutual exclusion.**
   - If `LNC3` holds for any support, then `binary-leavitt-unit-group-hyperlinear`
     is false.
   - If `R^x` is hyperlinear, then `LNC3` fails for every support.  Every
     such refutation that goes through embeddable traces is equivalent to
     hyperlinearity of `R^x`.

**Consequences for the frontier.**

- **Two branches.**  The hole and the open claim
  `binary-leavitt-unit-group-hyperlinear` cannot both close.  Each branch
  ends at a flagship result:
  - the corner branch gives a finitely presented nonhyperlinear simple group;
  - the hyperlinear branch, together with `openai-leavitt-unit-nonsofic`,
    gives a hyperlinear nonsofic group, which is the route
    `hyperlinear-nonsofic-from-leavitt-unit-group`.
- **No intermediate trace refutation.**  No intermediate trace refutation of
  the hole exists.  Its weakest trace obstruction already proves hyperlinearity
  of `R^x`.
- **The earlier decision point is a consequence.**  `EL_20(J) <= Delta`, so
  hyperlinearity of `R^x` implies the decision point of
  `leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity`.
