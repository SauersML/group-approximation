---
rg: 2
id: finite-character-one-sided-stabilizer-is-its-normalizer
kind: claim
title: A one-sided finite-character stabilizer word already normalizes the whole packet
invalidates:
  - exact-hnn-word-stabilizes-character-without-normalizer
distinct_from:
  finite-character-idempotents-have-exact-hnn-transport: that positively transports matched character atoms between two finite subgroups; this proves a return to the same atom cannot be a proper one-sided transport and is exactly packet normalization.
  subgroup-hecke-hnn-is-a-regular-safe-rank-actuator: that succeeds by mapping a smaller Reynolds source into a genuinely larger fixed-space target; this proves the equal-source/equal-target specialization loses the proper corner and collapses to a normalizer.
  c3-payload-defeats-selector-normalizer-correctors: that gives a matrix payload for which no selector normalizer can serve as the involutive corrector; this proves every exact group-word stabilizer of a finite character atom is necessarily such a normalizer before the payload is considered.
---

**ESTABLISHED.**  Let `H` be a finite subgroup of a group `G`, let `chi` be a
one-dimensional unitary character of `H`, and put

```text
q=e_(H,chi)=|H|^(-1) sum_(h in H) conjugate(chi(h))h.    (FCS1)
```

For every group element `g in G`, the following are equivalent:

```text
q g q=g q;                                               (FCS2)
g q g^-1=q;                                              (FCS3)
g H g^-1=H and chi(g^-1 h g)=chi(h) for every h in H.   (FCS4)
```

The adjoint one-sided identity `qgq=qg` is equivalent to the same conditions
with `g` replaced by `g^-1`.  Consequently a group word which exactly
stabilizes one finite-character atom, even if presented only through the
one-sided corner relation `(FCS2)`, already normalizes the whole finite
subgroup and preserves its character.

## Proof

Let

```text
I=H intersect g H g^-1.
```

By `finite-character-hecke-intersection-formula`,

```text
||q g q||_2^2 = |I|/|H|^2                              (FCS5)
```

when the two transported characters agree on `I`, and the norm is zero
otherwise.  If `(FCS2)` holds, then

```text
||q g q||_2^2=||gq||_2^2=tau(q)=1/|H|.                 (FCS6)
```

Equations `(FCS5)--(FCS6)` force character agreement and `|I|=|H|`.  Since
`H` and `gHg^-1` have the same finite order, this is exactly `(FCS4)`.
Condition `(FCS4)` gives `(FCS3)` by conjugating the finite Fourier sum
`(FCS1)`, and `(FCS3)` gives `(FCS2)` immediately.

There is also a support-only proof of the two-sided step: every coefficient
of `(FCS1)` is nonzero, so `supp(q)=H`; equality `(FCS3)` forces
`gHg^-1=H` and then equality of coefficients forces character preservation.
The Hecke argument is stronger because it shows that the ostensibly weaker
one-sided proper-corner identity already has the same consequence.

## Boundary for the charged proper-corner lane

This theorem does not obstruct an HNN section

```text
p=e_H  --->  r<=q=e_K
```

with a genuinely larger target `q`, as in
`index-two-reynolds-hnn-is-a-proper-corner-section`; unequal source and
target are exactly why that construction retains an exit complement.  It
does obstruct closing such a section into an **exact group-word unitary
return on the same finite character atom** while claiming to avoid packet
normalization.  Any such exact loop is back inside the normalizer lane.

Accordingly the one-sided charged/typewise nontransport readout must retain
one of the features already present in its statement: a proper larger target
with a paid complement, a trace-cyclic product of more than one partial
section, or a return inferred only after finite-matrix rank/HS correction.
It cannot be replaced by an exact same-atom Bass--Serre stabilizer word.
