# SSA self-Kunneth and XIV(2): exact intermediate theorems (2026-08-31)

## Verdict

Neither self-Kunneth for all strongly self-absorbing algebras nor STW
Problem XIV(2) is solved. This pass establishes two exact intermediate
theorems and corrects one overstatement in the previous reduction.

## Correction: K1-injectivity is not K1-vanishing

The earlier `ssa-kunneth-forces-solid-k-theory` text called `K_1(D)=0`
unconditional. The cited chain does not prove that. Automatic
`K_1`-injectivity says that unitary components inject into `K_1`; it does not
say that the group is zero.

Toms--Winter, *Strongly self-absorbing C*-algebras*,
arXiv:math/0502211, Proposition 5.1, derive `K_1(D)=0` after invoking the UCT
Kunneth sequences. Dadarlat--Winter, *On the KK-theory of strongly
self-absorbing C*-algebras*, arXiv:0704.0583, use `K_1`-injectivity for
asymptotic unitary equivalence, not K-group vanishing. STW,
arXiv:2506.10902, likewise list `K_1=0` among the restrictions obtained from
UCT/Kunneth near Problems XIV--XVI.

The affected Cairn theorem remains true after correction: under
self-Kunneth, `K_1(D)=0`, now derived from the graded unit-insertion map.

## Exact self-Kunneth criterion

For every SSA `D`, the external product

```text
alpha:K_*(D) tensor K_*(D) -> K_*(D tensor D)
```

is already split-surjective, because the first-factor K-isomorphism factors as
`alpha(x tensor [1])`. Hence there is no surjectivity gate. The Kunneth
sequence holds exactly when the always split-injective unit insertion
`x |-> x tensor [1]` is also surjective and the graded self-`Tor` term
vanishes. Grading then forces
`K_1(D)=0`; self-Tor vanishing is equivalent to torsion-freeness, so the even
group is exactly a torsion-free solid ring. Thus universal SSA self-Kunneth
is equivalent to that purely K-theoretic profile for every SSA algebra.

Every possible failure is therefore either a nonzero kernel of the external
product or a nonzero self-`Tor` term. No UCT-phantom can be claimed until one
of these is realized by an actual strongly self-absorbing algebra.

## XIV(2) rational profile

### Unit-class consistency check

The standard Cuntz algebra has

```text
K_0(O_infinity)=Z,       [1_(O_infinity)]=1,
K_1(O_infinity)=0,
```

not zero unit class. This follows from Toms--Winter,
arXiv:math/0502211, Proposition 5.1: an SSA UCT algebra with `K_0=Z` has unit
a generator. Consequently `Q tensor O_infinity` has `K_0=Q` with unit `1`.
The rational-profile proof's unit normalization and its identification of
rationalized multiplication with `Q tensor_Q Q -> Q` are therefore valid.

If `B=Q tensor O_infinity` absorbs `D`, continuity through the UHF limit and
the KK-equivalence `O_infinity ~_KK C` give

```text
K_0(D) tensor Q ~= Q       (unit to 1),
K_1(D) tensor Q = 0.
```

This is a UCT-free necessary condition for XIV(2), not a sufficient one:
rational K-theory contains neither an embedding nor the central-sequence data
needed for absorption.

Combining it with the exact self-Kunneth criterion shows more: for an
XIV(2)-embeddable SSA algebra the rationalized external product is an
isomorphism. Its kernel, `K_1(D)`, and every possible self-Kunneth defect are
therefore torsion. The residual XV gate is genuinely integral; rational
methods cannot finish it.

## Status

- `ssa-self-kunneth-exact-k-theory-criterion`: ESTABLISHED.
- `ssa-qoinfty-absorption-forces-rational-k-profile`: ESTABLISHED.
- `embeddable-ssa-self-kunneth-obstruction-is-purely-torsion`: ESTABLISHED.
- universal SSA self-Kunneth: OPEN.
- STW XIV(2), XIII--XVI, and general UCT Problem II: OPEN.
