---
rg: 2
id: mf-group-with-finite-central-compression-defect
kind: claim
title: An MF group can carry a finite central subgroup inside the compression defect of an infinite cyclic subgroup
distinct_from:
  bare-self-copy-mf-calibration: that countermodel is torsion-free, and its surviving defect word has infinite order, so it says nothing about the finite-order refinements; this one puts a subgroup of order two in the defect, which is the case the averaging and reblocking arguments were built for.
  infinite-cyclic-compression-lamp-mf: that countermodel is a wreath product whose defect comes from integer lamps and is again of infinite order, and its compressed subgroup is an arbitrary finitely generated subgroup of a residually finite group; here the compressed subgroup is infinite cyclic and the defect subgroup is finite and central.
  finite-normal-compression-obstruction: that is the positive theorem — a finite normal subgroup inside the compression defect of a property-(T) subgroup is killed by every corona representation; this is the witness that its property-(T) hypothesis cannot be dropped, even for a central subgroup of order two.
  compression-defect-dies-in-finite-dimensions: that is the exact finite-dimensional half, which kills the defect in every honest finite-dimensional representation and is not contradicted here; this exhibits the same element surviving in a norm matrix corona, so it measures the gap between the two halves.
  compression-defect-dies-in-mf-under-mark-stability: that replaces property (T) by point-norm stability of the ambient group at the mark; this shows what happens when neither hypothesis is present, and so is the reason that node cannot weaken its hypothesis to the bare algebraic configuration.
  torsion-normal-generator-drops-ambient-property-t: that removes property (T) from the ambient group while keeping it on the compression subgroup L; this shows the remaining hypothesis on L is the load-bearing one and cannot be removed in turn.
artifacts:
  - research/artifacts/property-t-free-counterexamples-2026-09-07.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED.**  There are a countable group `G`, an infinite cyclic
subgroup `L = <a> <= G`, an element `u in Comp_G(L)` with

```text
u L u^(-1) = <a^2> < L
```

a proper subgroup, and an element `c in C_G(L)`, such that

```text
k = [u c u^(-1), a]
```

has order exactly two, is central in `G`, and is not the identity.  So

```text
1 != <k> ~= C_2 <| G,      <k> <= D_G(L),
```

a nontrivial finite central subgroup of the intrinsic compression defect —
**and `G` is MF.**

Two independent witnesses are recorded, in the two routes.  One is a finitely
generated solvable group, so its MF-ness is imported from the literature and
owes nothing to this program's machinery; the other is built directly inside a
norm matrix corona from explicit matrix sequences.  Each carries one extra
feature the other does not, stated in its own route.

## What this shows cannot be deleted

`finite-normal-compression-obstruction` and the transport corollary
`cor:defect-hs` of `non_mf_groups_exist.tex` both require property (T) of the
compressed subgroup `L`.  This claim shows that requirement is load-bearing
and that none of the following replaces it:

- finite generation, amenability, or residual finiteness of `L` — here
  `L ~= Z` has all three;
- properness of the compression — here `uLu^(-1)` is index two in `L`;
- finiteness, centrality, or property (T) **of the defect subgroup** — here
  `<k>` is central of order two and, being finite, has property (T);
- torsion of the marked element, and hence the finite-order reblocking of
  `torsion-normal-generator-has-full-support-corona-core`.  In the corona
  witness the defect is displaced from the identity by exactly `2` in
  operator norm *and* in normalized Hilbert--Schmidt norm, so it is not a
  vanishing-rank artifact that reblocking could repair;
- involutivity of the centralizing element `c` — the corona witness may be
  built with `c^2 = 1`.

It kills no route now in the graph: every live consumer of the compression
mechanism keeps either property (T) on `L`
(`normal-kazhdan-defect-non-mf`, `finite-normal-compression-obstruction`) or
point-norm stability of the ambient group
(`compression-defect-dies-in-mf-under-mark-stability`).  What it forecloses is
a class of routes not yet written: those which would delete the rigidity
hypothesis and keep only the algebraic compression configuration together with
torsion or finiteness of the defect.

## What it does not show

It does not show that no property-(T)-free non-MF construction exists.  It
constrains only the *transport* step.  The live property-(T)-free lane runs
through `binary-leavitt-atomic-morita-return` and the corner inequality
`atomic-leavitt-gap-on-nonzero-matrix-corner`, neither of which transports
anything; that lane is untouched.
