---
rg: 2
id: steinberg-separated-support-imposes-only-matching-zeros
kind: claim
title: Separated X support imposes exactly one perfect matching of zeros
invalidates:
  - steinberg-zero-marginal-via-iterated-separated-support
artifacts:
  - research/steinberg-separated-support-firewall-proof.md
distinct_from:
  steinberg-x-row-splits-zero-marginal-tree-sectors: that proves the derivative summands have separated support; this computes the exact information carried by support separation alone.
---

**ESTABLISHED FIREWALL.**  In the biaffine circulation space `W`, let
`W_P` be the cycles avoiding all point vertices with `a=1/2`, and let `W_L`
be the cycles avoiding all line vertices with `c=1`.  Let

```text
M={(1/2,b,1):b in F_p}                                 (SSPF1)
```

be the `p` chord edges joining those two deleted vertex sets.  Then

```text
W_P+W_L=ker(res_M:W -> F_p^M),                         (SSPF2)
dim(W_P+W_L)=dim(W)-p.                                 (SSPF3)
```

The split in `(SXTS1)` places its two summands in `W_P` and `W_L`, so its
support-only consequence is exactly the matching vanishing `(SXTS3)`.  The
kernel in `(SSPF2)` is still large.  Iterating the identity while retaining
only outer-letter support cannot create another slice: the individual
expanded words can carry tree mass, and only their outer-letter sums are the
two separated circulations.  Closure must use the specific derivative
constraints `A(1-q)F`, `B(1-s)F`, their integrability, or the `Y` row.

DERIVATION
steinberg-separated-support-firewall-proof
