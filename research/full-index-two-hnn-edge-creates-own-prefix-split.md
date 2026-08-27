---
rg: 2
id: full-index-two-hnn-edge-creates-own-prefix-split
kind: claim
title: A full index-two HNN edge creates its own exact successor-prefix split
distinct_from:
  index-two-reynolds-hnn-is-a-proper-corner-section: That uses only the smaller associated subgroup and obtains a one-sided section; this extends the same edge over the full index-two source and identifies its conjugated sign with the successor prefix.
  agent-free-compressor-chart-edge-has-multiplicity-gauge: That shows a chart-only edge leaves the prefix multiplicity gauge free; this includes the non-scalar prefix involution in the same associated-subgroup isomorphism and computes the resulting split.
  balanced-schur-active-child-is-next-prefix-source: That must assemble all retained child types and inactive sectors; this proves the exact one-source incidence cell it may use.
---

**ESTABLISHED.**  Let `H_0<C_0` and `H_1<C_1` be marked index-two
inclusions of finite groups with

```text
C_0=<H_0,J>,                 C_1=<H_1,B>,
[J,H_0]=[B,H_1]=1,
```

and let `theta:C_0->C_1` be an isomorphism satisfying
`theta(H_0)=H_1` and `theta(J)=B`.  Form the HNN extension

```text
Gamma=<G,u | u c u^(-1)=theta(c), c in C_0>.            (FIP1)
```

In every unitary representation put

```text
p=e_(C_0),        q=e_(H_1),        r=u p u^*.           (FIP2)
```

Then

```text
r=e_(C_1)=q(1+B)/2,
q-r=q(1-B)/2.                                             (FIP3)
```

Thus the same edge which transports the Reynolds source also transports the
non-scalar source sign `J` to the literal target sign `B`.  Its retained
range lies in the positive `B` prefix, and the whole unused index-two
companion is the negative `B` first-hit piece.  There is no independent
`U(m)` multiplicity gauge between these two statements.

The identity survives all commuting cuts that the edge fixes.  Namely, let
`K,D_0,...,D_(n-1)` be commuting involutions centralizing both marked pairs,
and extend `theta` by fixing them.  With

```text
Q_-=(1-K)/2,
C_n=product_(j<n)(1+D_j)/2,
p_n=C_n Q_- e_(C_0),
```

one has

```text
u p_n u^*=C_n Q_- e_(H_1)(1+B)/2 <= C_n(1+B)/2,         (FIP4)
```

while its companion is

```text
C_n Q_- e_(H_1)(1-B)/2.                                 (FIP5)
```

Consequently, if `B` is declared to be the next pulse sign, `(FIP5)` lies
in the genuine first-hit layer

```text
C_n(1-B)/2.
```

The proof is immediate from Reynolds averages.  HNN covariance gives
`u e_(C_0)u^*=e_(C_1)`.  Since `C_1=H_1 times <B>` with `B` central and
outside `H_1`,

```text
e_(C_1)=e_(H_1)(1+B)/2,
```

and subtracting from `e_(H_1)` gives `(FIP3)`.  Fixed prefix cuts commute
through `u`, proving `(FIP4)--(FIP5)`.

There is a dimension-independent normalized-HS version.  After exactifying
the two fixed finite groups, if

```text
epsilon_c=||U pi(c)U^*-pi'(theta(c))||_2,
```

then

```text
||U pi(e_(C_0))U^*-pi'(e_(C_1))||_2
 <= |C_0|^(-1) sum_(c in C_0) epsilon_c.                (FIP6)
```

The fixed prefix commutation rows add only their ordinary telescoping loss.
Hence active leakage into the negative prefix and companion leakage into the
positive prefix are bounded by a fixed constant times the square root of the
presentation energy, independently of matrix dimension.

This cell does not by itself prove the global balanced-child incidence.
That step must still express the complete retained child family as sources
of full marked index-two edges sharing one target `B`, while returning the
inactive sectors without losing a baseline copy.  The point here is narrower:
once such source charts are supplied, the same-edge mixed-prefix relation is
an ordinary full-pair HNN isomorphism, not an additional analytic rigidity
theorem.

## Attempts

- **Use only the smaller subgroup edge.**  Then `J` is not in the associated
  subgroup and `uJu^(-1)` is not tied to a prescribed target prefix.  The
  multiplicity gauge of `agent-free-compressor-chart-edge-has-multiplicity-gauge`
  remains.
- **Use a separate prefix edge.**  Its implementer has an independent
  commutant gauge.  Extending the original edge from `H_0` to the full
  `C_0` and mapping `J` to `B` is what produces `(FIP3)`.
- **Claim the global compiler from one cell.**  This is not valid: the
  allowed/inactive type ledger and the common shared-BCS carrier still have
  to be assembled without spending half of every baseline type.
