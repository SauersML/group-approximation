---
rg: 2
id: leavitt-trace-balanced-nested-idempotents
kind: claim
title: A proper nested Leavitt pair is invisible to augmentation and every conjugacy-class trace
artifacts:
  - research/artifacts/kaplansky-cross-atlas-affine-lift-2026-09-07.md
distinct_from:
  group-algebra-coefficient-trace-separates-leavitt-corners: that refutes a proposed equivalence because the identity coefficients differ; this constructs a new proper nested pair for which the entire universal group-algebra trace agrees.
  leavitt-corner-idempotent-unital-surjection: that constructs the outer idempotent mapping to one; this adds an explicit proper sub-idempotent with all degree-zero trace obstructions balanced.
  leavitt-corner-one-sided-lift-exists: that asks for a one-sided inverse by correcting arbitrary quotient lifts; this reduces the target to equivalence of one canonical nested projective-module pair.
---

Let `R=L_(F_2)(1,2)`, `Q=R^x`, `S=F_2[Q]`, and let
`pi:S -> R` be evaluation.  There are explicit commuting units `g,h in Q`,
both of order three, such that

```text
g+g^(-1)=1,                 h+h^(-1)=p,                 (TBN1)
```

where `p` is a nonzero proper idempotent of `R`.  Put

```text
e=[g]+[g^(-1)],     c=[h]+[h^(-1)],     f=e c.           (TBN2)
```

Then

```text
e^2=e, c^2=c, f^2=f,       ef=fe=f,       0!=f!=e,      (TBN3)
pi(e)=1,                    pi(f)=p.                     (TBN4)
```

The two images are Murray--von Neumann equivalent in `R`: transporting
`diag(t_0,t_0)` and `diag(s_0,s_0)` through `M_2(R)~=R` gives
`T U=1` and `U T=p`.

Moreover both `e` and `f` have augmentation zero and have zero image in the
group-algebra cocenter

```text
S/[S,S] ~= direct_sum_(conjugacy classes C in Q) F_2 [C].   (TBN5)
```

Consequently every conjugacy-class coefficient trace takes the same value on
`e` and `f` (namely zero), while their quotient images already have the
required equivalence.  This removes not only the canonical coefficient-trace
obstruction that killed the earlier pair, but the universal additive trace
obstruction for a group algebra.

The proposed next gate was a single projective-module equivalence:

```text
eS ~= fS.                                                (TBN6)
```

Equivalently, find `x in eSf` and `y in fSe` with `xy=e`, `yx=f`.  Since
`f!=e`, such a pair would make `eSe`, hence `S`, not directly finite.  Explicit
padding gives

```text
X=x+(1-e),       Y=y+(1-e),       XY=1,       YX=f+(1-e)!=1.
```

The equivalence itself, `leavitt-nested-idempotent-corner-module-equivalence`,
is now refuted by `leavitt-balanced-corners-separated-modulo-four`.
The construction and all characteristic-two trace calculations above
remain valid. However, lifted traces distinguish the two projectives:
their 2-adic values are 2/3 and 4/9, and modulo-four lifts already have
distinct identity coefficients. Thus characteristic-two trace balance
does not remove all additive projective-module obstructions.
