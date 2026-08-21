---
rg: 2
id: weak-soficity-survives-every-corpus-obstruction
kind: claim
title: Every obstruction mechanism in this corpus is realized inside a weakly sofic group
distinct_from:
  weakly-sofic-not-sofic: that is one instance — the nonsofic mechanism realized weakly soficly — and it is the input here; this is the closure of that observation over the corpus's other five mechanisms, and its conclusion is a constraint on future arguments rather than a class separation
  kun-thom-clifford-cover-weakly-sofic: that proves the Clifford cover is weakly sofic and nonsofic; this collects that together with the non-MF, non-residually-finite, finite-quotient-kill and quasi-identity mechanisms into the single statement that none of them can obstruct weak soficity
  literal-mark-conjugacy-width-unbounded: that is the quantitative form for one mechanism on one group, counting conjugacy factors; this is the qualitative sweep across mechanisms and proves only that each is realizable, not how it fails
artifacts:
  - research/artifacts/non-weakly-sofic-audit-2026-08-17.md
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

Each of the following mechanisms, all of which this corpus builds and uses,
holds in some group that is provably weakly sofic.  Hence none of them
implies failure of weak soficity, and none can be the engine of
`non-weakly-sofic-group`.

```text
mechanism                                    realized weakly soficly by
-----------------------------------------    --------------------------
non-MF (operator-norm microstate failure)    E          (sofic)
failure of residual finiteness               E          (sofic)
a nontrivial element killed by every         E's mark   (sofic)
  homomorphism to a finite group
violating a finite quasi-identity valid      E          (sofic)
  in every finite group
nonsoficity (permutation/Hamming failure)    Kun--Thom wreath W
the anticommuting Clifford / commutant wall  E_S        (Clifford cover)
```

## Why each realization is not a coincidence

The first four all rest on `E` being sofic, hence weakly sofic — a sofic
model is already a model into a finite group with a bi-invariant metric.  So
every property `E` has is compatible with weak soficity, and `E` has a lot of
them.  This is worth stating flatly because the strength of the non-MF
programme makes the opposite inference tempting: the marked word of `E` dies
in every finite quotient, violates a finite quasi-identity valid in all
finite groups, and blocks every operator-norm microstate — and all of that
happens inside a weakly sofic group.

The last two rest on Glebsky's 2023 permanence theorem, already carried by
`weakly-sofic-not-sofic` and `kun-thom-clifford-cover-weakly-sofic`: a
locally finite (or residually finite) kernel with residually finite quotient
gives a weakly sofic extension, with no hypothesis on the coset action.

## The constraint this places on future arguments

Two of the corpus's structural instincts are ruled out as engines here:

1. **Universal Horn / quasi-identity arguments cannot work.**  A weakly sofic
   group is a subgroup of a *quotient* of a direct product of finite groups
   (Glebsky's Lemma 1.2, recorded on
   `glebsky-weak-soficity-is-metric-free`).  Quasi-identities are preserved by
   subgroups and direct products but **not** by quotients, and the quotient
   step is exactly where approximate relators become exact while the marked
   word survives.
2. **Purely group-theoretic wall arguments cannot work.**  The full Clifford
   wall is realized in a metric ultraproduct of finite groups with
   bi-invariant metrics, with the radical word surviving.  So any no-go must
   use a metric inequality valid for **every** bi-invariant metric on **every**
   finite group.  Traces and Pimsner--Popa indices are not such tools; the
   `compressor-growth-index-homomorphism` machinery needs structure a metric
   ultraproduct of finite groups does not carry.

What is left is `non-weakly-sofic-word-certificate`: a fixed-width profinite
escape, which is a finite-group theorem about conjugacy width, not an
approximation-theoretic obstruction at all.
