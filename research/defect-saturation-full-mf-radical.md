---
rg: 2
id: defect-saturation-full-mf-radical
kind: claim
title: Defect saturation gives groups with full MF radical
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
  - research/artifacts/router-detector-torsion-free-non-mf-2026-08-22.md
  - research/artifacts/torsion-free-full-mf-radical-2026-08-19.md
  - GroupApproximation/Sofic/DefectSaturation.lean
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
  - GroupApproximation/Sofic/ManuscriptClosedWrappers.lean
---

There exists a two-generated finitely presented torsion-free property-(T)
acylindrically hyperbolic group `G` whose compression defect is all of `G` and
whose MF residual is all of `G`:

```text
Res_MF(G) = G.
```

Thus every homomorphism from `G` to an MF group is trivial, `G` itself is not
MF, and every nontrivial quotient of `G` again has full MF residual and is
non-MF.

The construction is the Fournier--Facio compression configuration followed by
the audited Hull--Osin routing quotient of
`defect-normally-generates-torsion-free-quotient`.  The Cairn route
`defect-saturation-full-mf-radical-proof` records exactly how those published
group-theoretic inputs feed the machine-checked normal-Kazhdan and residual
plumbing.

The 2026-08-22 router--detector artifact gives the complete proof in one
place, including the explicit algebraic identity `defectNormal = G`, the
normal-Kazhdan moving-corner argument, and the separation from every
central-sign, Clifford, and Hilbert-hotel mechanism.

The stronger hyperlinear-to-MF compiler artifact factors the same result
through an arbitrary op-to-HS killed subgroup.  On that route the
Fournier--Facio compression defect is only the explicit input; the reusable
theorem is `acylindrical-hyperlinear-saturation-compiler`.

**Trust boundary.**  The Hull/Osin existence step is source-verified and
paper-level, not formalized.  Once the routing data exist, defect saturation,
full MF residual, quotient heredity, and the CDE operator-MF consequences are
kernel-checked in `TorsionFreeFullMFRadical.lean` and its wrappers.

**Hyperlinear firewall.** Full MF residual is an operator-norm statement and
does not itself produce a hyperlinear-radical word. The established
`simple-sofic-total-mf-radical` gives the sharp abstract counterexample:
`Rad_MF(S)=S` can coexist with `Rad_hyp(S)=1`. For this finitely presented
group, total MF residual supplies an operator-norm collapse modulus, but the
HS conversion costs `sqrt(d)` and hyperlinearity supplies no defect-versus-
dimension rate. The concrete consequence that remains useful is
`full-mf-radical-hyperlinear-models-force-relator-outliers`: any hypothetical
regular hyperlinear models of this `G` must concentrate a fixed
operator-norm relator failure on a spectral corner of vanishing trace.
