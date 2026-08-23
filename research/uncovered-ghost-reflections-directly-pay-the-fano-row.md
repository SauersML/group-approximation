---
rg: 2
id: uncovered-ghost-reflections-directly-pay-the-fano-row
kind: claim
title: Uncovered-ghost reflections directly pay the Fano row without a Julia block encoding
distinct_from:
  fano-uncovered-ghost-energy-is-one-julia-commutator: that stacks all uncovered rows and Julia-dilates the resulting contraction; this uses the existing common D8 source reflection and reduces the same energy to finitely many ordinary commutators, with no colligation authentication.
  free-julia-grading-carries-one-gram-at-canonical-quarter-mass: that gives the general block-row inequality for an arbitrary grading-preserving involution; this identifies the special uncovered-ghost involution and tracks the exact Fano normalization and completeness condition.
  ghost-completed-fano-naimark-wordizes-one-local-predicate: that wordizes the ghost projection in one selected local context type; this shows the only remaining wordization is the hybrid uncovered reflection, not the row contraction or a coherent context register.
  finite-packet-central-sign-cannot-enforce-nonlinear-support: that rules out arbitrary nonlinear support selection on a marked finite-packet sector; this gives the positive direct payment if the particular uncovered reflection is supplied and identifies exactly why central signs cannot supply it.
---

ESTABLISHED REDUCTION AND FINITE-REGISTER FIREWALL. Let `z,j` be the common
D8 grading and reflection, and put

```text
P_+=(1+z)/2,       P_-=(1-z)/2,       S=P_+jP_-.       (UGR1)
```

For each Fano context let `P_c,F_c` be commuting projections on the positive
grading half and put

```text
Q_c=(1-P_c)F_c <=P_+,
r_c=1-2Q_c.                                             (UGR2)
```

Then `r_c` is a self-adjoint unitary commuting with `z`, and the ordinary
word `v_c=r_c j r_c j` satisfies

```text
8||Q_cS||_2^2 <= ||v_c-1||_2^2                         (UGR3)
```

in the normalized trace of the whole D8 grading. If the two grading halves
have the same matrix dimension and the Fano norm is normalized on one half,
this becomes

```text
4||(1-P_c)F_cS||_(2,H)^2
 <=||v_c-1||_(2,H direct-sum H)^2.                     (UGR4)
```

Consequently

```text
L_forb <=(1/4)sum_c mu_c||v_c-1||_2^2.                 (UGR5)
```

Thus the special row in `(FGJ1)` needs neither a coherent LCU prepare state
nor an ordinary-word block encoding. It also needs no corner return, no
selected controller orientation, and no authentication of a literal block
against the representation-dependent stacked operator `T`. Finitely many
direct commutator rows are strictly smaller than the aggregate Julia target.

Exact perfect completeness is preserved. In the common partial-swap model,
`Q_cS=0` implies `Q_cSS^*=SS^*Q_c=0`; hence `r_c` commutes with both the
off-diagonal block and the defect projection, so `v_c=1`.

Write `p_c=1-2P_c` and `f_c=1-2F_c`. The reflection `r_c` is `-1` exactly
on the joint character `p_c=+1,f_c=-1`, and is `+1` on the other three.
This one-point Boolean indicator is not a character. No ordinary word in
commuting selector signs and additional central signs can equal `r_c`.

An arbitrary fixed nonabelian finite controller can realize this truth table
in one chosen representation but cannot authenticate it in all
representations. The induced ghost sector of
`ghost-finite-router-induced-sector-or-perfect-corner` retains that sector
while satisfying the finite router table exactly; equivalently
`finite-packet-central-sign-cannot-enforce-nonlinear-support` applies. Thus a
central-sign finite register does not evade the firewall. The sole remaining
target is to authenticate `1-2(1-P_c)F_c` by a non-finite-packet mechanism.
The existing D8 anchor can fix its relative grading orientation once it
exists; orientation itself is not missing.

The direct infinite ordinary-group version is now also fenced.
`fano-hybrid-reflection-has-a-universal-regular-hs-gap` computes in the
faithful regular marked corner that every group word stays at squared
normalized-HS distance at least `1` from the hybrid reflection. This applies
to arbitrary HNN, self-similar, Leavitt-derived, or solution-group actors.
Moreover, if the three honest scalar sectors `(P,F)=(0,0),(1,0),(1,1)` are
separately finitely realizable with output `+1`, their odd tensor product is
the exact wrong sector `(0,1,+1)`. Thus an infinite actuator can survive only
as a matrix/canonical-trace-specific, sector-entangled mechanism: it must
exclude the regular trace and cannot split completeness into independently
tensorable scalar selector representations.
