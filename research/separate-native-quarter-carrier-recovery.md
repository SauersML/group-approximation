---
rg: 2
id: separate-native-quarter-carrier-recovery
kind: claim
title: Recover the two native D8 quarter carriers in commuting descendants
distinct_from:
  same-orbit-closure: that closes every Leavitt child on one source-sized paired orbit; this asks only for two fixed packet projections to enter two commuting returned algebras.
  balanced-router-pauli-holonomy-interface: that promotes the projection reflections to ordinary group words; this leaves them as fixed group-algebra expressions and recovers their projections instead.
  pauli-carrier-membership-decoder: that puts the transported branch carrier under one raw binary carrier and immediately creates a rank-capacity contradiction; this asks only for membership in one of two commuting descendant algebras.
---

OPEN.  Let `F` be the trace-quarter common product of the two transported
coefficient corners, and let `G` be the distinct trace-quarter
comb-transported branch-transfer carrier.  In every finite-dimensional
canonical-trace microstate of the mixed rank-five atlas, recover commuting
finite descendant algebras `A_raw,A_comb` such that

```text
dist_2(F,A_raw)+dist_2(G,A_comb)
 <= C (sqrt(def(U))+sep_F(U)),                         (SNQ1)
```

for one fixed finite moment window and a dimension-independent constant.
The roles of `F,G` may be swapped.

This is sufficient.  Their canonical moments give

```text
||R_F R_G R_F R_G-1||_2^2=1/2,
```

whereas
`separate-d8-carriers-cannot-recover-in-commuting-descendants` gives the
finite floor

```text
dist_2(F,A_raw)+dist_2(G,A_comb) >= 1/8.               (SNQ2)
```

Thus `(SNQ1)` cannot hold at vanishing defect and canonical trace separation.

The claim is strictly weaker than the previous transverse endpoint.  It
does not recover the same projection twice, close a whole rectangular label
space, construct a common classical coupling, or promote either reflection
to a group word.  Both projections are already fixed finite Hecke expressions
in the exact packet; only their finite-matrix descendant placement is sought.

## Finite-matrix firewall

This cannot be a functorial consequence valid in every tracial
representation.  The left regular exact model has the displayed D8
holonomy, so no two commuting descendant algebras can contain both carriers
there.  The proof must use the finite coordinate/multiplicity content of the
mixed raw/comb return: a rectangular label enlargement must either place the
two native carriers in transverse commuting factors or pay its boundary mass.

## Concrete audit target

The exact formulas already locate the two candidates before return:

```text
F=(T_0 q T_0)(T_1 q T_1),
G=comb^* Q_P comb.
```

The next calculation should track these two expressions—not arbitrary
isotypic projections—through the named mixed rank-five multiplication
triangles.  It is enough to show that their conditional expectations onto
the two returned finite-coordinate algebras retain all but `O(sqrt(def))`
of their `L^2` mass.  Spectral rounding and the D8 floor are already proved.

This audit is now finite and explicit.  Exact prefix reduction gives 37
support words of coefficient mass `11/4` for `F` and four support words of
coefficient mass `1` for `G`.  By
`forty-one-word-native-carrier-transport-certificate`, transporting every
one of these words with error `eta` would force `eta>=1/30`.  The open task is
therefore to extract the finite-matrix returned algebras/reservoir from the
mixed rank-five multiplication triangles and then control these 41
target-algebra placements.  The extraction cannot be replaced by literal
word identities: those would also apply to the regular exact model.

## Falsification gate

An argument using only their traces, the compulsory `5/32` overlap, or the
finite packet character tables is invalid: the exact atlas model has all of
those data.  The proof must use a mixed return relation that the standalone
packet does not satisfy, and it must be tested against `rectangular-escape`.
