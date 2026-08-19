---
rg: 2
id: literal-witness-kernel-free
kind: claim
title: The kernel to the Clifford witness is free of infinite rank, hence non-amenable
invalidates: [literal-sofic-via-amenable-kernel]
distinct_from:
  literal-witness-kernel-amenable: That claim asserts the kernel is amenable; this claim computes the kernel and finds a nonabelian free group, so the two are contradictory and this one refutes the other.
  literal-lamp-kernel-clifford-block-amalgam: That claim describes the lamp kernel of `E` over the telescope quotient `V`; this one describes the smaller kernel of the witness map `E -> W`.
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
  - non_mf_groups_exist.tex
---

The kernel of the canonical surjection `E -> W = ClLamp(X) x| V` from the
literal finitely presented group to its Clifford witness is a **free group of
countably infinite rank**.  It is therefore not amenable, and
`literal-witness-kernel-amenable` is FALSE.

The map is an isomorphism on the telescope quotients, so the kernel equals
`ker(N_E -> ClLamp(X))`, the kernel of the collapse of the block amalgam onto
the group in which all distinct sites anticommute.  Every block and the centre
inject, so the kernel acts freely on the Bass-Serre tree of the amalgam; it is
nontrivial and non-finitely-generated because `[c_x, c_y] w` lies in it for
sites `x, y` in different blocks.  Equivalently: `E` is *free-by-sofic*.

The refuted route also used extension permanence in the direction "amenable
kernel and sofic quotient imply sofic".  Elek--Szabo prove the opposite
direction (sofic kernel, amenable quotient); the direction used there is an
instance of the open extension problem for sofic groups, so the route was
unsound independently of this computation.
