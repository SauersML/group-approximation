---
rg: 2
id: amenable-base-l-presentations-have-recursive-locus
kind: claim
title: Amenable-base finite L-presentations and raw simulators have recursive amenability loci
distinct_from:
  genuine-hnn-switches-over-amenable-bases-are-sigma1: that treats genuine one-edge HNN extensions and endomorphism mapping tori; this treats arbitrary finite substitution-orbit relators and raw non-genuine simulators with any finite number of substitution letters.
  finite-graphs-of-amenable-groups-have-sigma1-locus: that classifies genuine finite Bass--Serre assemblies; here the substitutions need not descend to injective edge maps before the presentation kills their stable kernels.
  amenability-of-finite-presentations-is-pi2-complete: that is the open hardness root; this closes the direct finite-L-presentation and raw substitution-letter routes from an amenable base.
---

**ESTABLISHED.** Let

```text
B_e=<X_e | Q_e>
```

be a computable family of finite presentations, all presenting amenable
groups. For each `e`, let `Sigma_e` be a finite list
`sigma_(e,1),...,sigma_(e,s(e))` of endomorphisms of the free group
`F(X_e)`, supplied by their values on `X_e`, and let
`R_e subset F(X_e)` be finite.

First form the finite L-presentation

```text
L_e=F(X_e)/
    << Q_e union {sigma(r): sigma in Sigma_e^*, r in R_e} >>.      (LNS1)
```

Then every `L_e` is amenable: it is a quotient of `B_e`. Thus the
amenable locus of the family `(L_e)` is all indices, independently of
every substitution orbit or stable kernel.

The direct finite stable-letter simulator is

```text
T_e=<X_e,t_1,...,t_(s(e)) |
     Q_e,R_e,
     t_i^(-1) x t_i=sigma_(e,i)(x)
     (x in X_e, 1<=i<=s(e))>.                              (LNS2)
```

No invariance or injectivity hypothesis is needed. Its exact amenability
criterion is

```text
T_e is amenable  iff  s(e)<=1.                             (LNS3)
```

For `s(e)=0`, the group `T_e` is a quotient of the amenable group
`B_e`. For `s(e)=1`, let `A_e` be the image of `B_e` in
`T_e`. It is amenable, and the defining relations give

```text
t^(-1) A_e t <= A_e.
```

Hence

```text
N_e=union_(n>=0) t^n A_e t^(-n)
```

is an amenable directed union, is normal in `T_e`, and `T_e/N_e` is
cyclic. Thus `T_e` is amenable even when the substitution has a
nontrivial stable kernel or does not descend to an endomorphism of `B_e`
before that kernel is killed.

For `s(e)>=2`, killing every `x in X_e` defines an epimorphism

```text
T_e ->> F(t_1,...,t_(s(e))).
```

Therefore `T_e` is nonamenable. Consequently the amenable index set of
every computable family `(T_e)` is the syntactic set

```text
{e:s(e)<=1},
```

which is recursive, while the amenable index set of `(L_e)` is constant.
Neither can be the nonrecursive `Pi^0_2`-complete set `TOT`.

This remains true when the amenable base is a fixed finitely presented
solvable group with undecidable word problem: undecidable equality changes
neither quotient closure nor the free quotient in (LNS2). A possible
`Pi^0_2`-hardness construction must therefore leave this class. In
particular, it must introduce relations among the controller letters that
destroy the free quotient, start before stable closure from a nonamenable
base, or use a finite-presentation mechanism not expressible as an
amenable-base quotient or a raw substitution-letter simulator.

DERIVATION
[[amenable-base-l-presentation-locus-proof]]
