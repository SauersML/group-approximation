# Kun--Thom literal-return / normalizer-separation audit

**Date:** 2026-08-26

## Question audited

Can the literal mixed word

```text
x=T^* phi(gamma) T
```

be authenticated, after subtracting its edge expectation and polar
correction, as the same cyclic vector that implements the strict compressor
normalizer correspondence?

## Result

No.  The mixed word authenticates the opposite conclusion.

Choose a fixed `delta in Gamma` such that

```text
h^(-1)delta h notin Gamma.
```

Existence follows from the already established infinite degree of the marked
double coset.  With `B=C*(phi(Gamma))`, `a=phi(delta)`, and

```text
r=||E_B(x^*ax)||_2,
```

the canonical relative moments and fixed-word multiplicativity give
`r->0`.  But if `w` normalizes `B`, then `w^*aw` is a unitary of `B` and
therefore has conditional-expectation norm one.  Contractivity gives

```text
1-r <= 2||w-x||_2.
```

Thus `dist_2(x,N(B))>=1/2-o(1)`.

For the standard correction `y=x-E_B(x)`, choose a closest unitary polar
extension `v`.  If `s=||E_B(x)||_2`, then

```text
||v-x||_2<=2s,
dist_2(v,N(B))>=1/2-o(1)-2s.
```

When the fixed exterior return has `s->0`, the corrected vector remains a
half-unit away from every normalizer gauge.

## Interpretation

The earlier right-module result is not weakened: `yB` still has right
dimension tending to one and lies orthogonal to `B`.  What fails is the
attempt to promote that right module to the compressor's index-one
correspondence.  Left multiplication sees the full marked double coset, whose
degree is infinite.  The literal occurrence is therefore intrinsically the
wrong gauge for an index-one compressor correspondence.

This is stronger than the separate-gauges finite-quotient countermodel.  It
uses the literal word and supplies a padding-stable, dimension-free numerical
separation.  A future positive argument must couple a distinct compressor
gauge to the returned word by new holonomy data; correction/extraction alone
cannot co-locate them.

## Cairn duplication check

Searched for `normalizer distance conditional expectation returned root` and
`return word compressor gauge`.  Existing nearby nodes concern abstract
module authentication, separate exact gauges, or the marked double-coset
index.  None states this mixed-word conditional-expectation inequality.
