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
  - research/artifacts/shell-tail-structure-brown-calibration-2026-09-18.md
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

Window zero through the cofinal class P_0*Z (2026-09-17, dies). The route
only needs a cofinal class of inputs. Every finitely presented decidable
P_0 sits in P_0*Z, which is infinitely ended. The one-ended obstruction does
not apply there. A shift-normalizing enumeration (window N=0) would make
R_nu an ascending HNN extension of the regular copy, hence finitely
presented, and would pass the gate, so Q would be finitely presented. This
dies at the index count
(`accessible-shell-inputs-admit-no-shift-normalizing-enumeration`). On each
infinite component the shift is `y -> phi(y) c_i`. Pulling the pieces back
coset by coset gives k=[P:phi(P)] near-partitions by right translates. An
end Euler measure
(`accessible-non-virtually-cyclic-groups-carry-end-euler-measures`, which
exists for every accessible non-virtually-cyclic P) then forces
(k^n - 1) mu(Pbar) = mn for all n, which is impossible. So N=0 is excluded
for every finitely presented non-virtually-cyclic input, and any germ-level
witness needs a window N >= 1 with a larger base B.

Entropy-measure transplant (2026-09-17, dies). Density and local-statistics
invariants of the enumeration cannot see the obstruction. The near index
eta, and the finitary and density-zero supports of s^-eps lambda(P) s^eps
versus W_N, are invisible to any shift-invariant density. The
square-spiral limit already has its extra germ on density-zero lines. The
invariant that does detect window zero is finitely additive and
point-counting (the end Euler measure), not a density.

Brown's criterion over the germ map (2026-09-17, dies at the edge stabilizers). The attempt
lets A_1 act through d: A_1 -> Q on a simply connected cocompact complex. Cell stabilizers
are then A(Q_sigma) = d^-1(Q_sigma). The positive-control pieces are Q_v virtually <tau>, so
that A(Q_v) is commensurable with Fix_V(p).

The attempt dies at the edge clause.
- Brown's criterion needs finitely generated edge pieces.
- The kernel K = ker d is not finitely generated, so every Q_e must be infinite.
- Infinite edge stabilizers make all vertex stabilizers commensurable, so Q commensurates <tau>.
- The near index turns this into a central tau^a.
- `shell-prefix-core-detects-finite-ray-enumerations` then forces P to be virtually cyclic.

See `cyclic-germ-brown-complexes-force-virtually-cyclic-shell-input`. That claim also records
two necessary conditions on the pieces of any surviving decomposition:
- A(H) finitely generated forces H to have finitely many coarse orbits on N;
- in particular A(rho(P)) is not finitely generated.

So the vertex pieces must be groups A(H) with H not virtually <tau>, which are of the same
nature as A_1.

Tail-structure Brown complex (2026-09-18, dies at the vertex stabilizers). See
`research/artifacts/shell-tail-structure-brown-calibration-2026-09-18.md`.

Reframing. A_1 is the V-absorption V[Q] of its germ group Q. It is the group of
homeomorphisms that fix p, are locally V off p, and permute the rows 0^n 1 C
near p by a representative of a germ in Q.

The attempt lets A_1 act on a complex whose cells are tail row structures. The
stabilizer of the standard rows on 0^m C is

    S_m = V(C minus 0^m C) x Qtilde_m.

Here Qtilde_m consists of the bijections of N_{>=m} with germ in Q_0 = ker(eta|Q).
It is an FSym-absorption: 1 -> FSym -> Qtilde_m -> Q_0 -> 1.

- On the shell, Q_0 = ker(eta_R) x ker(eta_R). Brown's criterion with these
  vertex stabilizers therefore needs ker(eta_R) finitely generated. That is a
  two-sided Sigma^1 condition, strictly more than the ascending gate.
- Calibration.
  - The two-ray germ group Q_2 gives V[Q_2] = Stab_V({p,q}), which is finitely
    presented (`contracting-srn-rational-stabilizers-are-fp`).
  - Its tail stabilizers contain Houghton's group FSym(Z) x| Z with index at most 2.
    That group is not FP_2 over Q (`houghton-h2-is-not-fp2-over-q`).
  - So S_m is not finitely presented, and the method cannot certify a group that is
    finitely presented.

The invariant is the FSym-absorption of the index-zero germs. At the permutation
level it carries Houghton defects that V absorbs. The germ-map complex of
2026-09-17 has cells that are too large, since they contain the kernel K, which is
not finitely generated. Exact row structures give cells that are too small. A
surviving complex must mix finitely many rows by V (a Stein-Farley-type poset of row
splittings). An obstruction to A_1 FP cannot be read off at the FSym level alone.
