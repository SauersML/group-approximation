---
rg: 2
id: free-lamp-sofic-class-action-is-sofic-set-action
kind: claim
title: For a free lamp group the Alekseev--Bradford sofic class-action condition is equivalent to soficity of the underlying set action, so the Kun--Thom free-lamp action is not a sofic hyperlinear action
distinct_from:
  coordinate-action-not-sofic: that is Kun--Thom Corollary D, the nonsoficity of the coset action in the Gao--Kunnawalkam Elayavalli--Patchell sense; this shows the Alekseev--Bradford automorphism-action notion adds nothing for free lamps, so that corollary also kills the free-lamp permanence route.
  kt-free-lamp-hnn-group-is-hyperlinear: that is the open hyperlinearity of the free-lamp HNN group; this closes one specific mechanism for it (semidirect-product permanence) and leaves the group question open.
  sofic-action-permanence: that dead route invoked wreath permanence theorems needing a sofic coset action; this proves that the newer automorphism-action permanence needs exactly the same input when the lamp group is free.
---

Let `G` act on a set `X` and on the free group `Delta = F(X)` by permuting
the basis, and let `C` be any class of groups containing the finitely
generated free groups (sofic, hyperlinear, linear sofic, weakly sofic).

**Theorem.**  The basis-permuting action `G -> Aut(F(X))` is a sofic
`C`-action by automorphisms in the sense of Alekseev--Bradford (arXiv:2601.18742,
Definition 4.23, read from the arXiv HTML on 2026-08-26) if and only if
`G -> Sym(X)` is a sofic action on a set in the sense of Gao--Kunnawalkam
Elayavalli--Patchell (their Definition 4.16, same source).

**Consequence.**  For the Kun--Thom pair, `G` acting on `X = G/Gamma` is not
a sofic action (`coordinate-action-not-sofic`, Kun--Thom Corollary D), so
the free-lamp action `G -> Aut(F(G/Gamma))` is **not** a sofic hyperlinear
action, and Alekseev--Bradford's Corollary 5.2(c) cannot be applied to
`H = F(G/Gamma) x| G`.  The "Certificate B" of the 2026-08-26 attack
notebook -- prove the free-lamp action sofic hyperlinear although the coset
action is not sofic -- is impossible as stated.  The group `H` may still be
hyperlinear (`kt-free-lamp-hnn-group-is-hyperlinear` stays open), but not
through this permanence theorem, whose hypothesis is exactly the coset
soficity that Kun--Thom refute.

**Why the auxiliary group buys nothing for free lamps.**  A chart of a free
group is determined by its values on a basis; injectivity and equivariance
are conditions on those values alone, and a finite set of values in any
group is just a finite set.  The group structure of `Lambda` could only
matter for lamp groups with relations.
