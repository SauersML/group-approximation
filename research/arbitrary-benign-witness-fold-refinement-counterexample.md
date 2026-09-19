---
rg: 2
id: arbitrary-benign-witness-fold-refinement-counterexample
kind: claim
title: An ordinary benign witness need not separate or refine its fold in finite quotients
distinct_from:
  quotient-benign-witness-forces-finite-presentation: that obstructs one global quotient-compatible map from the benign ambient; this gives a direct finite-quotient counterexample to the stronger universal profinite conclusion from benignness alone.
  positive-rope-profinite-edge-synchronization: that asks for a specially constructed positive-branch witness with extra profinite data; this counterexample does not rule out such a construction.
---

**ESTABLISHED.**  There are a finite-rank free group `F`, a normal subgroup
`N`, and an ordinary finitely presented benign witness `(K,e,L)` for `N<=F`
with `F/N` residually finite, for which both conclusions `(i)` and `(ii)` of
[[benign-witness-finite-quotients-refine-the-fold]] fail.

Take Thompson's finitely presented infinite simple group `V`, choose a
nonabelian free subgroup `e(F_2)<=V`, and put

```text
F=F_2,                 N=1,                 K=V,                 L=1.
```

Then `e(F) cap L=1=e(N)`, so this is benign-witness data in exactly the sense
assumed by the refuted claim, and `F/N=F_2` is residually finite.  But every
homomorphism from `V` to a finite group is trivial.  Consequently every finite
quotient of

```text
Gamma=<V,v | [v,L]=1>=V*<v>
```

kills `e(F)` and `v e(F) v^-1`, hence kills

```text
S=<e(F),v e(F)v^-1>.
```

Choose any proper finite-index normal subgroup `F'` of `F`.  The fold modulo
`F'` is nontrivial on the first copy of `F`, whereas the restriction to `S`
of every finite quotient of `Gamma` is trivial.  Thus

```text
S cap ker(alpha)=S  not<=  <<F'_1,F_2>>_S
```

for every finite quotient `alpha` of `Gamma`, disproving `(ii)`.

The same example disproves `(i)`.  The embedded `F_2` is proper in `V`
(`V` is simple, while `F_2` is not), so choose `k in V\e(F)`.  The retraction
`V*<v> -> V` which kills `v` maps `S` onto `e(F)`; hence `k notin S`.  On the
other hand every finite quotient kills `k`, so its image is the identity and
therefore lies in the image of `S`.  Hence `k` lies in the profinite closure
of `S` in `Gamma`, and `S` is not closed.

This refutes only the implication from ordinary benignness to the two
profinite conclusions.  It leaves open whether the compiler's particular
Higman witness can be constructed with additional relative separability or
finite-congruence-extension data.
