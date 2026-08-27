---
rg: 2
id: fixed-separation-hamming-is-not-weak-soficity
kind: claim
title: The formalized WeakSoficModel is fixed-separation soficity, strictly stronger than weak soficity
distinct_from:
  weakly-sofic-not-sofic: that is the mathematical separation of the two classes, witnessed by a group; this is the statement that the repository's `WeakSoficModel` sits on the sofic side of that separation, so the name collides with the literature's notion
  glebsky-rivera-w-sofic-criterion: that characterizes the genuine weak-sofic class in profinite terms; this identifies which class the corpus has actually formalized, and it is the other one
  glebsky-fin-case-instantiation: that explains why weak soficity is stuck with the generic capped conjugate-word length while soficity gets Hamming plus a covering theorem; this is the corresponding fact about the Lean development, namely that only the Hamming side is formalized
artifacts:
  - GroupApproximation/Sofic/SoficAmplification.lean
  - GroupApproximation/Sofic/Sofic.lean
  - research/artifacts/non-weakly-sofic-audit-2026-08-17.md
---

The structure `WeakSoficModel` of `GroupApproximation/Sofic/SoficAmplification.lean`
and its predicate `IsSoficWeak G δ` are **ordinary soficity with the
separation constant pinned**, not weak soficity in the sense of
Glebsky--Rivera.  Concretely:

```text
WeakSoficModel G F δ ε   has   map : G → Equiv.Perm carrier
                               multiplicative / separated  measured in
                                 normalized hammingDistance
```

— the same target and the same metric as `SoficModel`, differing only in
`1 - ε` being replaced by a fixed `δ` in the separation clause.  The file
then proves `isSofic_iff_weak` (for `0 < δ < 1`), `isSofic_iff_weakLocal` and
`isSofic_iff_weak_quarter`: the predicate is *equivalent* to `IsSofic`, by
tensor-power amplification.

Weak soficity as defined by Glebsky--Rivera quantifies over **all finite
groups with all bi-invariant metrics**.  By `weakly-sofic-not-sofic` that
class is strictly larger than the sofic class.  Hence

```text
IsSoficWeak G δ   <=>   IsSofic G   =>   G weakly sofic,
```

with the last implication strict.  No declaration in the development
formalizes the Glebsky--Rivera target class.

## What is and is not wrong here

The Lean is correct and its docstring is honest — it says "the textbook
convention" for the *separation constant*, and the amplification theorems are
exactly right for that reading.  The defect is a **name collision with the
literature**, and it is live rather than cosmetic, because the graph does
discuss genuine weak soficity (`weakly-sofic-not-sofic`,
`kun-thom-clifford-cover-weakly-sofic`, `glebsky-weak-soficity-is-metric-free`,
`glebsky-rivera-w-sofic-criterion`).  A reader moving between the Lean and the
research nodes will meet the same word denoting two different classes, one
strictly inside the other.

The failure mode this creates is the one
`badge-claim-strength` names elsewhere in this corpus: a true theorem cited
for a claim it does not make.  `nonsofic_groups_exist` plus a structure named
`WeakSoficModel` invites the reading "the repository has a non-weakly-sofic
endpoint", and `non-weakly-sofic-group` records that no such endpoint exists
anywhere.

## The rename, and the definition that would be needed

`FixedSeparationSoficModel` / `isSofic_iff_fixedSeparation` would state what
the file proves.  A genuine `GRWeakSoficModel` needs a target bundling a
finite group with a bi-invariant metric — `dist` plus left and right
invariance plus the usual metric axioms — with the model conditions read in
that `dist`, and the bridge `IsSofic G → IsWeaklySoficGR G` instantiated at
symmetric groups with Hamming metric.  Section 10 of the audit artifact
sketches the full API, including a topology-free `InProfiniteClosure` by its
finite-quotient universal property and `conjClassProduct` on a `List`, so that
`glebsky-rivera-w-sofic-criterion` could be stated and proved through the
finite-separability route.  None of that is written; this node records the
gap, not a plan.
