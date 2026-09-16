---
rg: 2
id: decidable-inputs-have-fp-one-singularity-shell-stabilizer
kind: claim
title: A decidable infinite finite presentation admits an enumeration whose one-singularity shell stabilizer is finitely presented
distinct_from:
  decidable-inputs-have-fp-shell-stabilizers: that demands three finitely presented stabilizers A_1, A_12, A_2; this demands only A_1. They are equivalent, but only through the separate implication `shell-one-singularity-fp-forces-two-point-stabilizers-fp`, so this is the strictly smaller statement a construction must prove.
  shell-fp-stabilizer-forces-fp-germ-group: that is a necessary condition for any enumeration (A_1 FP implies Q FP); this is the open existence problem for A_1 itself.
artifacts:
  - research/artifacts/shell-one-singularity-stabilizer-reduction-2026-09-16.md
  - research/artifacts/boone-higman-shell-normal-core-criterion-2026-09-08.md
---

For every infinite finitely presented group P with decidable word
problem, there is a bijection nu:P->N such that, in the shell group
E_nu=<V,hat(P)> of `shell-cantor-embeddings-are-finite-germ-extensions`
with p=0^infinity and singularities relative to V, the subgroup

    A_1 = {e in E_nu: sing(e) subset {p}, e(p)=p}

is finitely presented.

This is an OPEN construction problem. By
`shell-one-singularity-fp-forces-two-point-stabilizers-fp` it is
equivalent to `decidable-inputs-have-fp-shell-stabilizers`. The route
`decidable-shell-stabilizers-via-one-singularity-clause` records one
direction. The other is trivial.

## Attempts

Positive control. `virtually-cyclic-inputs-have-fp-shell-stabilizers`
settles virtually cyclic inputs. Its proof uses a central shift power
in the germ group. By `shell-prefix-core-detects-finite-ray-enumerations`,
such a power exists only for virtually cyclic inputs.

Necessary conditions. A finitely presented A_1 forces a finitely
presented germ group Q (`shell-fp-stabilizer-forces-fp-germ-group`).
That is equivalent to a finitely presented fiber product
R_nu x_Z R_nu (`shell-germ-group-has-index-two-fiber-product`). It is
also equivalent to R_nu being finitely presented together with the
ascending HNN gate (`shell-germ-fp-is-an-ascending-hnn-gate`). The
square spiral enumeration of Z^2 fails because R_nu is metabelian and
not finitely presented
(`square-spiral-z2-near-shift-group-is-not-finitely-presented`). For
one-ended inputs the regular copy can never serve as the HNN base
(`one-ended-shell-inputs-admit-no-shift-normalizing-enumeration`).

Lifting from Q to A_1 (2026-09-16, dies). Write A_1=<G_p,Fix_V(p)>,
where G_p is the subgroup supported in 0C, isomorphic to A_1 by the
localization of the reduction artifact. The calculus that presents A_2
from A_1 then only yields a fixed-point presentation of A_1 in terms of
itself. Normality of the neighborhood kernel K would need the commutator
relations between the deep copies G_(0^n) and V(C minus 0^n C) for all n.
These are s^n conjugates of one finite relation set. Rewriting an
arbitrary lift of a germ generator in the required form h s^n u s^-n,
with u in G_p, however, already uses relations of A_1.

The purely abstract principle "finitely presented quotient plus a
finitely presented subgroup mapping onto it" is false. Take the fiber product G=F_2 x_Z F_2 over an epimorphism F_2->Z. The
quotient G/(ker x 1) is F_2, and the diagonal copy of F_2 maps onto it.
Yet G is not finitely presented (classical Baumslag--Roseblade theorem
on subgroups of products of free groups; not re-fetched here). No finite
presentation of A_1 is known for any input that is not virtually cyclic.
