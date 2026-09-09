---
rg: 2
id: terminated-digit-fiber-stabilizer-repairs-shell-action
kind: claim
title: Enlarging to the full fiber stabilizer gives a faithful finite-rank action of the digit host
artifacts:
  - research/artifacts/boone-higman-enlarged-digit-fiber-stabilizer-2026-09-08.md
---

Let H=H_(h,r), F=union_i i*{1,...,h}^N, and K=Stab_H(F).
Then K is finitely generated, core_H(K)=1, and K has at most
h^3 double cosets in H. Hence the H action on its orbit of F,
equivalently H/K, has type (A).

This orbit is exactly the set of nonempty finite unions of boundary
tiles whose tile count is r modulo h-1.

For every fixed-base shell embedding E_nu<=H supplied by the
terminated-digit construction,

    K intersect E_nu = (E_nu)_p = S.

Thus the orbit of F under E_nu is the original shell orbit E_nu/S
inside the larger faithful action. Moreover [K:S] is infinite.
The enlargement repairs the infinite-bi-index obstruction for S
by genuinely enlarging the stabilizer, not merely the actor.

This provides an explicit alternative type (A) action for these
contracting hosts. It does not supply a host for arbitrary
decidable inputs or make their shell envelopes finitely presented.
