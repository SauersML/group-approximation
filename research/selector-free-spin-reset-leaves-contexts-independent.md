---
rg: 2
id: selector-free-spin-reset-leaves-contexts-independent
kind: claim
title: Amalgamation over the common spin packet leaves old and fresh selectors independent
artifacts:
  - experiments/selector_reset_commutant_freedom.py
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that gives a simultaneous positive regular type flow for every finite graph of finite groups; this identifies the local multiplicity-commutant freedom already present in one selector-renewal edge.
  fanizza-radical-charts-admit-common-symplectic-reset-subgroups: that constructs the unique common spin type; this proves that sharing only that type cannot couple the old and fresh selector semantics.
---

Let `E` be the common symplectic reset packet and let `sigma` be its unique
marked spin representation.  Suppose an old chart group `G_0` and a proposed
fresh-selector group `G_1` contain `E`, and each has two equal-dimensional
extensions of `sigma`, denoted

```text
rho_-, rho_+ in Irr(G_0),       eta_-, eta_+ in Irr(G_1),
Res_E rho_a = sigma = Res_E eta_b.                         (SFI1)
```

Then every pair `(a,b) in {-,+}^2` occurs in an exact finite-dimensional
representation of the amalgam `G_0 *_E G_1`.  Indeed, choose unitary models of
`rho_a` and `eta_b` on the same space `V_sigma` whose restrictions to `E` are
literally `sigma`.  The universal property of the amalgam gives the required
representation.  More generally, after amplification on
`V_sigma tensor C^n`, the two overgroups may act by independently chosen
unitaries in the full multiplicity commutant `M_n(C)`.

Consequently the two restriction matrices are both

```text
                  -   +
Res_E = sigma  [  1   1  ],                                (SFI2)
```

and the complete representation-ring incidence equation is only

```text
m_-^old + m_+^old = m_-^fresh + m_+^fresh.                 (SFI3)
```

Equation `(SFI3)` preserves the spin scale, but it neither transports a
selector value nor constrains any old/fresh correlation.  The same conclusion
holds for `k` selector bits: all `2^(2k)` pairs of old and fresh characters are
exact solutions while restriction records only equality of total
multiplicity.

Thus a stable symplectic congruence followed only by amalgamation or HNN
transport of the common spin subgroup cannot prove the Fanizza transition
law.  A valid renewal cell must add a relation acting nontrivially on the
multiplicity commutant (or an equivalent two-cell/compressor); merely moving
the old selector center to private generators and adjoining fresh commuting
selectors leaves the two contexts exactly independent.
