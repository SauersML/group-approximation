---
rg: 2
id: one-bit-selector-local-fejer-proof
kind: route
title: Reduce the local selector subgroup to a four-term Clifford normal form
target: one-bit-selector-local-words-are-fejer-subcritical
requires:
  - one-bit-clifford-selector-halves-a-chosen-bcs-atom
  - selector-product-is-a-payload-corner-square-root
  - finite-clock-fejer-threshold-is-sharp
  - canonical-moments-bound-projective-fixed-carrier-density
---

The context group `H` is elementary abelian.  It centralizes `p,q`, and
`qp=r pq` with `r in H`.  Moving all context letters left and then moving
all `q` letters to the right gives the normal form

```text
h p^epsilon q^delta,          h in H, epsilon,delta in {0,1}.  (SLP1)
```

On `E`, every `h in H` is the scalar assignment character, while `r=-1`.
Thus `p,q` anticommute on `E`.  Conjugation by `q` exchanges the two
`p`-eigenspaces, and conjugation by `p` exchanges the two `q`-eigenspaces,
so both splits have equal trace.  Also `(pq)^2=r=-1` on `E`, and multiplication
by `p` exchanges its `+i` and `-i` eigenspaces.  This proves `(SLF4)` and the
equal-phase assertions.

If `epsilon=delta=0`, the word lies in `H` and has order at most two.  If
exactly one exponent is nonzero, its compression has two equal sign phases;
if both are nonzero, its compression has two equal fourth-root phases.  The
canonical Reynolds calculation gives `(SLF6)`.  Combining these phase masses
with the sharp order-two and order-four bounds from the Fejer claims gives
`(SLF5)`.

Fixed finite-group exactification and fixed-word telescoping change all of
these traces and compressed word relations by `o(1)` in a canonical
microstate sequence, so no strict supercritical inequality can appear in the
limit.
