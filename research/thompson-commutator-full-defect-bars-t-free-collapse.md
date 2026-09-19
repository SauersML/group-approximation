---
rg: 2
id: thompson-commutator-full-defect-bars-t-free-collapse
kind: claim
title: Thompson's F' carries a full compression defect, so a Kazhdan-free full-defect collapse that applies to F' proves F non-amenable
artifacts:
  - experiments/thompson-full-defect-2026-09-17/check_defect.py
distinct_from:
  uniform-finitary-rank-compression-is-mf-compatible: that gives an MF group whose compression defect is a proper simple normal subgroup, which kills the normal-subgroup version of the criterion without property (T); this concerns the ambient version D_G(L)=G, which that example does not satisfy, and places it on Thompson's commutator subgroup.
  a-t-menable-groups-have-no-rigid-compression-defect: that shows rigid (Kazhdan) pairs inside a-T-menable groups are finite with trivial defect; this shows the plain compression defect of an interval subgroup of the a-T-menable group F' is the whole group, so the ambient hypothesis D_G(L)=G alone is satisfied there.
  compression-defects-die-in-rigid-targets: that shows finite and linear targets kill every compression defect without property (T); this shows that deciding the same statement for MF targets and ambient-full defects, uniformly over a class containing F', decides Thompson's amenability problem.
  model-spectral-gap-quantifier-ladder: that kills Kazhdan substitutes proved from the relations of G in every C-star representation; this bars substitutes that use only the combinatorial compression data (L, u, c, D_G(L)=G) together with any property of the pair (F', F[1/4,1/2]).
  thompson-f-is-not-amenable: that is the named open problem; this claim does not prove it, it proves that a Kazhdan-free full-defect collapse over a class containing F' would.
---

**ESTABLISHED (written proof, exact computer check of the cell; not
Lean-verified).**  This is an obstruction to a class of approaches.  It is
not a refutation of the goal, and the goal stays OPEN.

Notation follows `non_mf_groups_exist.tex`.  For a group `G` and a subgroup
`L`,

```text
D_G(L) = << [u c u^-1, l] : u in G, u L u^-1 <= L, c in C_G(L), l in L >>_G .
```

The manuscript criterion says that if `G` has property (T) and `D_G(L)=G`,
then every homomorphism from `G` to an MF group is trivial.  For a class `P`
of pairs `(G,L)`, write **(FDC_P)** for the Kazhdan-free full-defect collapse:
*every countable `G` with a subgroup `L` such that `(G,L)` is in `P` and
`D_G(L)=G` has `Rad_MF(G)=G`.*

Let `F` be Thompson's group, `F'=[F,F]` and `F[a,b]` the elements supported
in `[a,b]`.  Put `L=F[1/4,1/2]`, and let `u`, `c` and `l` be the following
elements of `F'`.

- `u` is the identity on `[0,1/4]` and on `[5/8,1]`.  It has slope `1/2` on
  `[1/4,1/2]`, mapping it onto `[1/4,3/8]`, and slope `2` on `[1/2,5/8]`,
  mapping it onto `[3/8,5/8]`.
- `c` is the dyadic affine copy of the generator `x_0` on `[1/2,5/8]`.
- `l` is the dyadic affine copy of `x_0` on `[3/8,1/2]`.

1. **Cell.**  `u L u^-1 = F[1/4,3/8]` is a proper subgroup of `L`, `c` lies
   in `C_F'(L)`, `l` lies in `L`, and `delta=[u c u^-1, l]` is a nontrivial
   element of `F'`.
2. **Full defect.**  `D_F'(L)=F'` and `D_F(L)=F'`.  Here `L` is isomorphic
   to `F`, so it is finitely presented.  `F'` is simple, torsion-free, has
   no finite quotients and is the directed union of the finitely presented
   groups `F[2^-n, 1-2^-n]`.
3. **Barrier.**  If `(F',F[1/4,1/2])` is in `P`, then (FDC_P) implies that
   `F` is not MF, hence not amenable.  Hence (FDC_P) implies
   `thompson-f-is-not-amenable`.  Contrapositively, if `F` is amenable, then
   (FDC_P) is false for every such `P`.
4. **The class it bars.**  Any Kazhdan-free proof of the
   `property-t-free-leavitt-full-mf-radical` endpoint that factors through
   the full-defect hypothesis `D_Delta(L)=Delta`, together with ambient
   simplicity, no finite quotients, torsion-freeness, proper one-sided
   compression, finite presentability of `L`, or any other property
   shared by `(F',F[1/4,1/2])`, is a proof that Thompson's `F` is not
   amenable.  The invariant is `(F',F[1/4,1/2])` itself.  Every member stops
   at the same step: specializing the collapse from `Delta` to `F'`.
   There it either stays conditional on Thompson's problem, or it
   solves that problem.

## Consequence for the Property-(T)-free program

The recorded Z-direct-factor kill posted on the live bus leaves only
survivors that use ambient simplicity or Leavitt data.  The present claim
removes ambient simplicity and the bare compression cell from the
unconditional list: they are shared with `F'`.  So a surviving argument
must use a hypothesis that fails for `(F',F[1/4,1/2])` and is not intrinsic
to `L`.  The candidates are:

- finite generation of the ambient group.  Thompson's `T` then plays the
  role of `F'` for the MF problem of `T` (remark in the proof route);
- a spectral input on `L` or on the models, which the goal forbids in its
  Kazhdan form;
- the ring data of `Delta`: the Steinberg relations of rank at least 3
  together with the rank-4 compression cell `u e_ij(a) u^-1 = e_ij(sat)`,
  which acts on root subgroups and not on interval supports.

Note that `F` is a-T-menable, so by
`a-t-menable-groups-have-no-rigid-compression-defect` the Kazhdan version of
the criterion cannot be applied to `F'` at all.  Both statements hold at
once.  With property (T), the criterion is vacuous on `F'`.  Without it, the
bare full-defect criterion is non-vacuous on `F'` and settles Thompson's
problem.

Proof route: `thompson-commutator-full-defect-bars-t-free-collapse-proof`.

## Attempts

- 2026-09-18 (swarm-0917-w10-w10-ptm-break): the "finite generation of the
  ambient group" survivor is closed **unconditionally** by
  `fg-mf-group-with-full-compression-defect`. That node gives a
  49-involution-generated subgroup `G` of a corona unitary group with
  `L = <a'>`, infinite cyclic and strictly compressed, and
  `D_G(L) = G`. `G` is MF, so (FDC_P) is false for every `P` containing
  that pair, with no amenability hypothesis. Survivors that remain:
  - finite presentability, torsion-freeness and simplicity of the ambient
    group;
  - property (T) for `L`;
  - a spectral input on the ambient group;
  - the ring data of `Delta`.
