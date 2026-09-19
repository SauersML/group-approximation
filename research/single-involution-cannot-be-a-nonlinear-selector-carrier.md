---
rg: 2
id: single-involution-cannot-be-a-nonlinear-selector-carrier
kind: claim
title: One group involution either has regular mass on every selector atom or cuts only an affine half-space
artifacts:
  - research/artifacts/reverse-kleene-multiplicity-holonomy-audit-2026-08-20.md
distinct_from:
  augmentation-one-corner-retains-a-character: that rules out a trivial-type Hecke corner using augmentation; this computes the canonical L2 mass of a proposed marked-word carrier against every finite selector character.
  regular-trace-blocks-exact-local-predicate-return: that rules out universal exact projection return by canonical-trace dimension accounting; this is the local one-involution obstruction before any return network is installed.
---

Let `A<=Gamma` be a finite elementary abelian `2`-subgroup, let `d in Gamma`
be an involution, and set `p=(1-d)/2`.  For each character `chi in A^*`, let

```text
e_chi=|A|^(-1) sum_(a in A) chi(a) a.                  (SIC1)
```

If `d notin A`, then in the canonical group trace

```text
tau_Gamma(d e_chi)=0,
tau_Gamma(p e_chi)=1/(2|A|),
||p e_chi||_2^2=1/(2|A|)>0.                            (SIC2)
```

Consequently no universal relator-energy estimate can force `p` to vanish on
even one selected `A`-atom: an exact left-regular representation has zero
relator energy and the positive mass `(SIC2)`.

If `d in A` and `d!=1`, then `p` is diagonal in the selector algebra and

```text
p e_chi = e_chi  iff chi(d)=-1,
p e_chi = 0      iff chi(d)=+1.                        (SIC3)
```

The selected characters form one affine half-space of `A^*`.  If `d=1`, then
`p=0` and it carries no selector information at all.  Thus one marked
group involution cannot itself be the carrier of an arbitrary nonlinear
Fanizza predicate: outside the selector subgroup it sees every regular atom,
and inside it sees only an affine parity cut.
