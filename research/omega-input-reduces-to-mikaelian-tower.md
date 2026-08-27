---
rg: 2
id: omega-input-reduces-to-mikaelian-tower
kind: claim
title: The omega-operation input becomes a statement about Mikaelian's tower, and reading his notation correctly makes every stage an HNN extension
distinct_from:
  mikaelian-rho-tau-shortcuts-fail: that records a REFUTATION -- his rho and tau clauses fail on an explicit two-letter witness; this records a successful reading of a different part of the same section, and the two corrections are independent.
  higman-theorem-three-reduces-to-enumerated-range: that reduces Higman's Section 2, the combinatorial input; this reduces one of the six operation closures of his Section 4, the group-theoretic input.
artifacts:
  - GroupApproximation/Higman/OmegaTower.lean
  - GroupApproximation/Higman/OmegaTowerStages.lean
  - GroupApproximation/Higman/OmegaClosure.lean
---

`Omega.OmegaInput` --- benignness is preserved by the block operation
`omega_m` --- is now derived from

```text
OmegaTowerInput:
  for m > 0 and B containing 0 with A_B benign,
    there is a tower T with TowerClosure T B,
```

where `TowerClosure` splits into a benignness obligation on the tower's
subgroup `W T B` and a normal-form obligation: `T.emb x` lies in `W T B` only
if `x` lies in `A_(omega_m B)`.  The reduction is `omegaInput_of`.

The gain is not logical strength but buildability: the group is named, the
subgroup is named, and the two obligations are separated into one about
benignness and one about normal forms.

## Three source corrections, all load-bearing

**1.  Which `rho`.**  Mikaelian's `omega`-paragraph (arXiv:1908.10153v8, §4)
writes `Omega = Pi *_rho r` with `rho = shiftAut^m`, the `m`-shift
`a, b, c |-> a, b^(c^m), c`.  This is **not** the reversal his §4 calls `rho`
elsewhere in the same section.  Following the wrong `rho` builds the wrong
group.

**2.  What `*_P` means.**  His `*_P` in §2.4 is a **multiple HNN extension** --
several new generators each centralizing the same subgroup `P` of the base --
and not an amalgamated product.  With the correct reading every stage of the
tower is an HNN extension, so the repository's existing `Higman.CentHNN`
covers it verbatim and **no pushout machinery is needed on this lane at all**.
That is the difference between reusing a proved permanence theorem and building
an amalgam theory.

**3.  Which source to follow.**  Higman's own §4 leaves this step to the reader
(p. 472), and his `M * K` construction should not be followed; the three-stage
normal-form analysis of the modern write-up is the route.

## The caution that goes with it

Mikaelian's §4 is reliable here and not everywhere: his shortcuts for the
reversing and swap closures **fail**, on an explicit two-letter witness, as
[[mikaelian-rho-tau-shortcuts-fail]] records.  So "follow Mikaelian" is not a
blanket instruction; it is correct for `omega_m` and wrong for `rho` and `tau`.
