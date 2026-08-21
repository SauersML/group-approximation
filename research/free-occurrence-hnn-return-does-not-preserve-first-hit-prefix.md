---
rg: 2
id: free-occurrence-hnn-return-does-not-preserve-first-hit-prefix
kind: claim
title: A free-occurrence HNN return does not preserve the first-hit survivor prefix
invalidates:
  - mixed-cnot-allowed-active-return-via-free-occurrences
distinct_from:
  s3-affine-hnn-transports-the-active-vector: that correctly transports all four endpoint atoms between two charts; this shows that such transport supplies no relation between the returned active union and an independent first-hit pulse.
  reset-ray-hnn-return-is-stationary: that rules out Schur multiplicity contraction under type-preserving return; this is the earlier logical failure that the returned carrier need not lie below the next survivor prefix at all.
---

Let `A'` and `X'` be the active three-atom union and exit atom in the fresh
endpoint occurrence obtained by HNN transport.  Let `B_n` be the independent
binary pulse used by the Thompson first-hit reservoir, and put

```text
C_(n+1)=C_n(I+B_n)/2.                                  (FHP1)
```

The free-occurrence and HNN relations impose no covariance between the fresh
endpoint chart and `B_n`.  Hence they do not imply

```text
A'<=C_(n+1).                                           (FHP2)
```

This is not a missing estimate.  It is false for the stated presentation.
The HNN relations may be represented with `A'` nonzero while the independent
site packet is represented with `B_n=-I` on that summand.  All endpoint
transport equations remain exact, whereas `(I+B_n)/2=0` there.  Equivalently,
free amalgamation permits the pulse representation to be chosen independently
after fixing the marked endpoint representation.

Transporting a separate copy of `X` into the first-hit reservoir does not
repair `(FHP2)`: the same source mass can still reappear in the fresh HNN
image, and the next active carrier is not certified to exclude the mass
already charged as an exit.  Thus the prefix hypothesis used by
`thompson-site-pulses-localize-hard-exits` and
`branching-plus-first-hit-exits-forces-hs-floor` is absent.

The minimal repair needs a site-local partition whose exit atom is the
charged first-hit event and whose complementary union contains the returned
three active endpoint atoms.  A single binary pulse cannot do this because
the complement is a nonlinear three-versus-one predicate.  The two-bit tag
construction in `two-bit-tag-routing-splits-s3-exit-and-survivor` supplies
the correct local partition.
