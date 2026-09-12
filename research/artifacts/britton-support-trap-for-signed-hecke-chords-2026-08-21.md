# Britton support trap for exact signed-Hecke chord literalization

**Date:** 2026-08-21  
**Status:** Exact no-go theorem proved; no non-hyperlinear group is claimed.

## Result

For an HNN extension `G=<B,t | tAt^-1=C>`, conjugation by `t` can send an
element of the base group algebra back into the base group algebra only when
every group-basis coefficient of that element is supported on `A`.  This is
not merely a sufficient condition: it follows coefficientwise from Britton
normal form and linear independence of the group basis.

The escaped signed-Hecke packet has an unexpectedly rigid generic case.  In
the effective base

```text
B_D=K_D times L_D,
K_D=(C_2)^D semidirect S_D,
L_D=<a_2,...,a_D>,  a_1=1,
```

put `W=sum_i a_iE_ii`.  If a corner matrix `Y=(y_ij)` has no zero entry and
`Tr(Y)-2y_rr` is nonzero for every `r`, then the group support of `WYW*`
generates all of `B_D`.  The latter inequalities put the coordinate sign
flips in the Fourier support; a transposition viewed on a fixed coordinate
recovers the permutation itself; viewing the same transposition on a moved
coordinate recovers every free difference `a_s a_r^-1`.  These conditions
hold on a nonempty Zariski-open set in every nontrivial involution signature
class.

Therefore an exact one-stable-letter equation

```text
t(WY_0W*)t^-1=WY_1W*
```

between two dense escaped marginals forces both associated subgroups to be
the whole effective base.  The HNN extension is then an automorphism mapping
torus, hence hyperlinear by the height-kernel and amenable-extension theorem.

## Consequence for the first cycle

This rules out the most direct proposed infinite-edge repair of the first
signed-Hecke chord: “put the entire escaped marginal into the edge subgroup
and impose its additive equality by HNN conjugation.”  For a generic
nontrivial marginal, the phrase “the entire marginal” already means the
entire effective packet group.

The surviving HNN possibility must exploit genuine sparsity relative to the
separator blocks, transport several pieces with a coupled non-graphical
edge, or leave the single-HNN framework.  Dense endpoint regauging does not
create a proper nonamenable edge.

This is wired as `britton-support-traps-dense-free-phase-chord`, proved by
`britton-support-trap-proof`.
