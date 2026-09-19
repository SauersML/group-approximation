---
rg: 2
id: leavitt-resolvent-derived-units-mod-centre-not-fp-simple
kind: claim
title: For the Leavitt resolvent ring R_L, the derived unit group modulo its centre is not finitely presented and perfect, so it is not a finitely presented simple group
distinct_from:
  leavitt-resolvent-derived-units-mod-centre-fp-simple: that is the positive statement, refuted here.
  leavitt-central-units-lie-in-derived-normal-subgroups: that is the general theorem for every ring with a Leavitt family; this is its instance for R_L, with P = [R_L^x, R_L^x] and C = Z(P).
---

**ESTABLISHED** by `leavitt-resolvent-units-not-fp-simple-proof` (elementary; not
independently reviewed).

Let `R_L` be the ring of `leavitt-resolvent-ring-is-fp-simple-of-char-zero`,
`D = [R_L^x, R_L^x]`, and `Z(D)` its centre. Then:
1. `Q^x ≤ [D, D] ∩ Z(D)`;
2. `D/Z(D)` is not a finitely presented perfect group, and in particular it is not a
   finitely presented simple group.

So `leavitt-resolvent-derived-units-mod-centre-fp-simple` is false, and the route
`gl-n-q-bh-via-leavitt-resolvent-units` cannot fire.

The argument needs none of the inputs listed as unproved in Attempt 3 of the refuted
claim: no `K_1 = U^ab` theorem, no purely infinite simplicity, no exact sequence, and no
perfectness of `D`. It uses only that `R_L` is a nonzero ring with a Leavitt family and
with `Q` in its centre.

It says nothing against other subquotients of `R_L^x`. Subgroups that are not normal,
normal subgroups meeting `V` trivially, and quotients by non-central subgroups are not
excluded. That includes the weaker target in Attempt 2 of the refuted claim.
