---
rg: 2
id: same-range-dressed-reynolds-sections-expose-raw-source-unitary
kind: claim
title: Two dressed Reynolds sections with one range expose a literal raw source unitary
distinct_from:
  index-two-reynolds-hnn-is-a-proper-corner-section: That constructs one proper section and its exit complement; this compares two source dressings of that section and reads their raw relative phase.
  packet-dressed-shared-implementer-requires-one-outer-class: That dresses a packet normalizer on a full isotypic carrier and retains one multiplicity implementer; this works with a one-sided section and does not require the dressing to implement a packet outer automorphism.
  central-square-orients-transverse-ledger: That consumes a raw lift satisfying a central square; this proves the lift is literally visible from two same-range section words.
---

**ESTABLISHED.**  Let `p,q` be projections in a finite tracial algebra, let
`u,d` be unitaries, and assume

```text
q u p=u p,                 dp=pd.                       (DRS1)
```

Put

```text
v_0=u p,                   v_1=u d p.                   (DRS2)
```

Then both are source-full partial isometries with the **same** final support:

```text
v_0^*v_0=v_1^*v_1=p,
v_0v_0^*=v_1v_1^*=u p u^*<=q.                          (DRS3)
```

Their relative corner is the literal, charged source unitary

```text
W=v_0^*v_1=p d p=d p.                                  (DRS4)
```

In particular, if `J` is central, commutes with `p,d`, and `d^2=J`, then

```text
W^2=Jp.                                                 (DRS5)
```

No phase quotient occurs in `(DRS4)`: replacing `d` by `lambda d` changes
the recovered `W` by the same scalar.  Nor do the two paths complete the
target to a Morita equivalence; their common range is still `upu^*`, so the
unused projection `q-upu^*` from the Reynolds section is untouched.

The statement is robust under normalized-HS perturbation.  If `(DRS1)` has
total error `epsilon`, replace `qup` by its source polar correction and use
the same corrected outgoing section in both paths.  Fixed-word telescoping
gives `(DRS3)--(DRS5)` with `O(sqrt(epsilon))` error, with no dependence on
ambient dimension.

Thus the remaining issue is not how to read a raw lift from a proper
section.  It is to construct a payload word `d` which preserves the selected
source and whose central square is the predicate sign while the two dressed
paths are the actual Schur/Fanizza returns.
