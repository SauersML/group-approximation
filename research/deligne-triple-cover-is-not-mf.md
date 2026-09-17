---
rg: 2
id: deligne-triple-cover-is-not-mf
kind: claim
title: Deligne's triple cover of Sp4(Z) is not MF
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
  - research/artifacts/deligne-sector-tensor-camouflage-2026-08-21.md
distinct_from:
  deligne-central-mark-hs-collapse: that asks for normalized-Hilbert-Schmidt collapse and is equivalent to non-hyperlinearity of E_3; this asks only for failure of operator-norm MF approximation and is strictly the MF question.
  deligne-triple-cover-fd-central-invisibility: that concerns genuine finite-dimensional representations; this excludes faithful operator-norm asymptotic representations, which is the unproved upgrade.
---

For Deligne's central extension

```text
1 -> <z>=Z/3 -> E_3 -> Sp_4(Z) -> 1,
```

the group `E_3` is not MF in the norm-matrix-corona sense.

By `deligne-triple-cover-finite-residual-is-center` and
`universal-mf-quotient`, this is equivalent to each of

```text
z in Rad_MF(E_3),
Rad_MF(E_3) = <z> = C_3.                                (DMF1)
```

Indeed `Rad_MF(E_3) <= Res_fin(E_3)=C_3`, while a non-MF countable group has
nontrivial MF radical.  Since `C_3` has prime order, there is no intermediate
subgroup.

## Attempts

- **Exact representations stop one topology too early.**  Deligne plus
  Malcev proves that every genuine finite-dimensional representation kills
  `z`, but MF radical membership quantifies over operator-norm asymptotic
  representations.  `fd-mark-stability-forces-mf-invisibility` explains the
  missing stability hypothesis, and no such stability theorem is known here
  for `E_3`.
- **Do not substitute the HS endpoint.**  Universal normalized-HS collapse
  of `z` is `deligne-central-mark-hs-collapse`, which
  `deligne-sector-gap-is-exactly-nonhyperlinearity` identifies with the
  stronger open assertion that `E_3` is non-hyperlinear.  HS-small exceptional
  central sectors may still have operator norm one, so that claim cannot be
  silently used as an operator-norm proof.
- **Literature boundary.**  Bachner--Dogon--Lubotzky, *On L1-approximation of
  groups*, arXiv:2508.17392v3, Proposition 1.5, gives non-MF only under the
  additional operator--HS stability condition and explicitly presents it as
  a potential approach to the MF question.  No theorem in that source proves
  this fixed triple cover non-MF.
- **Siegel spectral separation is dead (swarm-0917, entropy-measure).**
  `deligne-sector-siegel-spectrum-is-full-torus` proves that in every unital
  representation of a nontrivial sector `A_omega` (exact, corona,
  ultraproduct, regular) the Siegel radical `Sym_2(Z)` has joint spectrum
  all of `T^3`, every long-root lift has spectrum `T`, and every trace
  induces Haar measure.  Invariant: (Siegel spectrum, trace measure).  Every
  congruence-torsion / Magee--de la Salle transplant, quasi-unipotent
  eigenvalue bound, or invariant-measure rigidity argument dies at the step
  "the model has non-full, atomic, or non-Haar Siegel data", which is false
  for every representation.  The finite branch is empty because it would
  give a finite quotient seeing `z` (Margulis NST plus the Deligne residual).
  Survivors: vector-state atoms (the induced representation from
  `s(NU) x <z>` has invariant vectors), relative-(T) corners, and the matrix
  origin of models.  Artifact: `research/artifacts/deligne-sector-siegel-spectrum-2026-09-17.md`.
- **Linear-characteristic separation is dead (swarm-0917, transplanter).**
  This covers determinants, trace-logs, Exel--Loring/Dadarlat winding
  numbers and K_0/K_1 pairings of words filling `H_2` classes.
  `deligne-sector-determinants-see-only-dimension-mod-three`
  proves the following:
  - **Twisted Dadarlat formula.**  The twisted form of Dadarlat's
    Theorem 1.1 holds for the order-three mark.
  - **Only surviving bound.**  Its whole output is
    `dist(d theta k_r, Z) <= d L_r delta / 4`.
  - **Exact data.**  The exact determinant data are consistent iff `3 | d`.
  - **Normalized data.**  The normalized (de la Harpe--Skandalis) value
    group in the corona is `R`.

  Every member dies at "the determinant constraints are inconsistent":
  - Unnormalized members die because `U_n tensor I_3` keeps the defect and
    makes `3 | d_n`.
  - Normalized members die because `tau(K_0(Q)) = R`.

  A uniform-stability variant also dies:
  - **The argument.**  Use the trace-log functional to show that an exact
    `c_theta` representation in a tracial ultraproduct cannot be close to
    a genuine representation.
  - **Where it dies.**  `corona-defect-is-not-uniform` removes the uniform
    input for coronas.  For tracial von Neumann targets, the twisted regular
    representation is already a uniform `2 pi |theta| ||b||_inf` almost
    representation, so the stability hypothesis itself is false.

  Survivors are unchanged:
  - non-multiplicative spectral-multiplicity data;
  - vector-state and relative-(T) mechanisms;
  - the matrix origin of models beyond determinants.
