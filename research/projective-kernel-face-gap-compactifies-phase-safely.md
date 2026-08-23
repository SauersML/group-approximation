---
rg: 2
id: projective-kernel-face-gap-compactifies-phase-safely
kind: claim
title: A finite-phase projective-kernel face gap has a finite phase-safe witness
artifacts:
  - research/artifacts/monomial-toric-factor-clause-audit-2026-08-23.md
distinct_from:
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that proves a non-CE trace need not have any projective-kernel face gap; this assumes the whole face gap and proves finite extraction plus normal phase safety.
  toric-gap-is-a-relative-fd-central-word-face: that characterizes a finite toric game's clause face; this starts with a possibly infinite normal projective kernel and compactifies it to a finite binomial witness.
  monomial-finite-phase-projective-kernel-face-separator: that asks for the missing source-specific face gap and finite-game testability; this proves the two formal consequences once that gap exists.
---

**ESTABLISHED.**  Let `K normal G` and let
`chi:K -> mu_q` be a conjugation-invariant character.  If

```text
F_(K,chi) intersect closure(S_fd(G))=empty,             (PKC1)
```

then there is a finite subset `F subset K` such that the face cut out by

```text
phi(conjugate(chi(k))k)=1,       k in F,                (PKC2)
```

is already disjoint from `closure(S_fd(G))`.

For each `k`, the equality in `(PKC2)` defines a weak-star closed face.  If
no finite subset worked, these faces would have the finite-intersection
property inside the compact space `closure(S_fd(G))`, contradicting `(PKC1)`.

The graph subgroup

```text
C_chi={(chi(k)^(-1),k):k in K} <= mu_q x G             (PKC3)
```

is normal because `K` is normal and `chi` is conjugation invariant.  Hence
the normal closure of the finite graph clauses from `F` is contained in
`C_chi`, and

```text
normalClosure({(chi(k)^(-1),k):k in F}) intersect mu_q
   ={1}.                                                (PKC4)
```

Thus a genuine finite-phase projective-kernel face gap automatically has a
finite separator whose scalar phase survives normal closure.  The theorem
does not turn those binomials into the determining set of a finite nonlocal
game, and it does not infer `(PKC1)` from one non-Connes-embeddable trace.
