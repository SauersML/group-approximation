---
rg: 2
id: balanced-schur-finite-depth-reuse-is-regular-absorbed
kind: claim
title: Finite-depth balanced Schur reuse by packet edges is absorbed by a marked regular model
distinct_from:
  agent-first-hit-finite-fresh-tree-has-marked-matrix-model: that treats fresh structural copies, finite role packets, and finite-subgroup covariance with no predicate holonomy; this verifies that the established balanced Schur square and proper-corner dressing remain finite vertex-packet data and hence do not escape the same regular construction after level reuse.
  agent-first-hit-one-schur-two-cell-is-regular-absorbed: that absorbs one Schur predicate square in a finite semidirect packet; this treats an arbitrary fixed-depth chain of those squares together with Reynolds proper sections, full-child reuse edges, and first-hit address transports.
  companion-free-prefix-return-has-exponential-regular-capacity: that bounds exact functorial return through independent positive prefixes in the canonical group trace; this gives an exact finite-dimensional marked countermodel even when the first-hit destinations are arbitrary orthogonal finite character atoms rather than independent prefix halves.
---

**ESTABLISHED.**

This is a finite-depth firewall.  Fix a depth `N`.  Consider any
ordinary presentation assembled from the following currently established
pieces:

1. finitely many structural shared-BCS groups, finite Schur/reset packets,
   and finite role or first-hit address packets, with one common central
   payload sign `K`;
2. the balanced Schur square words of
   `schur-flip-square-exposes-payload-root-word` and the auxiliary central
   companion split of
   `two-sign-reynolds-companion-splits-one-assignment-atom`;
3. Reynolds proper-section HNN edges between marked finite subgroups;
4. full-child-chart or full-index-two HNN edges used to declare a retained
   child chart to be the next source chart; and
5. prefix-preserving or character-address HNN edges used to put the finitely
   many companion exits in orthogonal first-hit atoms.

Assume that no further relation couples two different HNN intertwiners on
their external multiplicity spaces.  Enlarging one associated subgroup so
that the same edge also conjugates a source sign, prefix involution, or whole
finite child chart is allowed.

Then the presentation has an exact finite-dimensional unitary
representation with

```text
K=-I.                                                   (BFR1)
```

In particular, merely concatenating the established proper-corner charged
section through finitely many full-chart/prefix HNN rows cannot imply a
dimension-independent normalized-HS floor for the marked payload.

## Proof

The only point needing verification beyond
`agent-first-hit-finite-fresh-tree-has-marked-matrix-model` is the balanced
Schur charge.  The two packet flips are commuting finite automorphisms, so
their implementers and the word

```text
d_a=P_a Q_a u_a v_a
```

belong to the finite semidirect packet

```text
B_f rtimes (C_2 times C_2).                            (BFR2)
```

The identity `A_a d_a^2=K A_a` is already an identity inside this finite
vertex packet.  Dressing a Reynolds path from `tp` to `td_ap` introduces no
new stable letter and no relation between distinct edge intertwiners.  The
auxiliary sign flip is another finite semidirect extension.  Hence every
level, including its charged square, is still one finite vertex packet once
the structural BCS variables are passed to their finite elementary-abelian
quotient.

Let the resulting finite marked vertex groups be `F_v`.  They include every
finite source and target subgroup occurring in the proper-section, child
reuse, and first-hit HNN rows.  Choose `L` divisible by every `|F_v|` and put

```text
V_v=(L/|F_v|) lambda^-_(F_v),                          (BFR3)
```

where `lambda^-` is the negative `K` corner of the regular representation.
For every marked finite edge group `E` incident to `v`,

```text
Res_E V_v ~= (L/|E|) lambda^-_E,                       (BFR4)
```

independently of the endpoint.  Thus every amalgam may be identified and
every HNN row has an exact unitary intertwiner.  Distinct stable letters can
be chosen independently because, by hypothesis, there is no cross-edge
multiplicity relation.  This proves `(BFR1)`.

The model is not vacuous on the intended payload ledger.  The abelianized
structural quotient contains every Boolean valuation in its negative
regular corner, while `(BFR2)` contains every Schur and companion type with
positive regular multiplicity.  Thus forbidden Reynolds sources, their two
balanced child signs, and all finite first-hit target characters occur with
positive multiplicity.  The regular multiplicities simply rescale so that
all edge restrictions match; this is the stationary compensation which the
proposed reuse was intended to remove.

Consequently, if the listed packet/HNN relations really implied all four
incidences in `balanced-schur-active-child-is-next-prefix-source`, the exact
model above would satisfy the zero-error form of the branching/first-hit
ledger while retaining `K=-I`, contradicting its scalar capacity conclusion.
Therefore at least one claimed incidence is not a consequence of those
relations.  The missing ingredient is not another finite-depth chart edge:
it must be a genuine relation between edge intertwiners (or an equivalent
matrix-coordinate support constraint) which acts on external multiplicity,
is triggered by the forbidden payload, and cannot be absorbed into a larger
finite semidirect vertex packet.

This does not rule out such a cross-edge relation, nor a matrix-only adaptive
support selection.  It rules out the proposed fixed-depth concatenation when
"the retained child is the next source" and "the exits are first-hit" are
implemented solely by enlarging finite associated subgroups and adding
ordinary independent HNN covariance rows.
