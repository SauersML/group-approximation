---
rg: 2
id: central-c2-hecke-mask-has-an-ambient-delabeling-word
kind: claim
title: A central C2 Hecke mask recovers the payload only by exposing an ambient delabeling word
distinct_from:
  free-label-orthogonalization-erases-payload-trace: that gives the general free-label erasure dichotomy; this computes the tempting finite central-sign Hecke mask and its unavoidable literal delabeling word.
  finite-graph-packet-compression-wandering-no-go: that separates vertex-corner compressions from wandering Bass-Serre words; this obstruction already occurs inside one central C2 label packet.
  one-round-v4-lamps-wordize-a-bcs-losing-projection: that wordizes an intended losing reflection with coordinate lamps; this shows why pairing each payload label with its central-sign mate does not preserve the canonical ambient trace.
---

**ESTABLISHED.**  Let `H` contain a nontrivial central involution `k` and
elements `x_i`.  Put `p=(1+k)/2 in L(H)`.  For payload unitaries `u_i in M`,
define in `M tensor L(H)`

```text
V_i=u_i tensor lambda(x_i),
W_i=1 tensor lambda(x_i k),
P=1 tensor p.                                                       (CHM1)
```

Since `k` is central, the two compressed label operators agree, and

```text
(P V_i P)(P W_i P)^*=u_i tensor p.                                 (CHM2)
```

So the Hecke corner recovers the payload exactly.  However the ordinary
ambient word

```text
V_i W_i^-1 k^-1=u_i tensor 1                                      (CHM3)
```

also recovers it, and hence has trace `tau(u_i)`.  The mask therefore cannot
simultaneously make the ambient character canonical and keep the payload
readable.  Omitting `k^-1` only postpones the problem: `k` is itself a named
group word, so `(CHM3)` remains in the generated group.

