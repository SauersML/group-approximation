---
rg: 2
id: selector-free-transverse-completion-has-fixed-radical
kind: claim
title: A transverse completion which forgets the selector center has selector-independent radical data
distinct_from:
  nested-schur-multiplicity-wire-globalizes-selectors: that puts the whole next packet in the preceding packet commutant; this treats a smaller endpoint generated from the q-MASA and arbitrary transverse packet words.
  full-q-masa-forgets-selectors-retains-branches: that keeps the selector-dependent corrected words as characters of an abelian endpoint; this proves why restoring a full fixed-scale spin packet around that endpoint recovers selector phases or loses those words.
---

Let `D=<J,z_1,...,z_k>` be the central selector subgroup of a class-two Schur
packet and let `K=<J,q_1,...,q_m>` be its full commuting q-MASA.  Let `E` be
any class-two subgroup containing `K` and any collection of transverse packet
words.  If

```text
E intersect D=<J>,                                               (SFT1)
```

then the commutator form of `E` on the marked sector is independent of the
selector character `x`.

Indeed every commutator of elements of `E` lies in `E intersect D`, hence is
`1` or `J`.  Evaluating `J=-1` therefore gives one fixed binary alternating
form at every `x`.  Its rank, radical, simple dimensions, and restriction
matrices are all selector-independent.

Consequently, if the corrected child directions

```text
Q_x=q_m product_j q_j^(v_j(x))                                  (SFT2)
```

span different lines of the q-space for two selector assignments, no `E`
satisfying `(SFT1)` can make those varying lines the radicals of a fixed-scale
transverse completion.  Any class-two completion which reconstructs the
genuine child spin factors must instead have

```text
E intersect D strictly contains <J>;                            (SFT3)
```

the selector dependence reappears as literal central commutator words.

Thus the flip-free q-MASA can forget selectors while it remains abelian, but
a finite Pauli completion around it cannot simultaneously preserve a varying
corrected branch and keep those selectors forgotten.  A viable fixed-scale
return must use a proper corner, projective/two-dimensional holonomy, or a
matrix-only comparison not realized as one class-two subgroup completion.
