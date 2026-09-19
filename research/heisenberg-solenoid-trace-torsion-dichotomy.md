---
rg: 2
id: heisenberg-solenoid-trace-torsion-dichotomy
kind: claim
title: Traces of the p-solenoidal Heisenberg group are canonical exactly off the torsion central sector
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
distinct_from:
  sl3-upper-unipotent-is-a-noncommutative-solenoid-field: that corrects the full SL3 carrier's spectral format and the diagonal transport between fibers; this is the fiberwise trace classification itself, with an exact torsion criterion.
  far-sector-is-solenoid-measure-rigidity: that is APPROXIMATE measure rigidity for one hyperbolic solenoid automorphism in the SL_2 far sector, where single-map rigidity fails; this is an EXACT trace classification whose rigidity comes from twisted-group-algebra symmetrizers, not from dynamics, and it is insensitive to the single-map obstruction.
  relative-t-heisenberg-adjoint-quantum-expansion: that turns finite irreducible Heisenberg quotients into quantum expanders via relative property (T); this classifies the infinite-level trace simplex of the discrete Z[1/p]-Heisenberg group itself.
---

Let `N = H_3(Z[1/p])` with center `c(Z[1/p])`, `S_p` the p-solenoid dual of
`Z[1/p]`, and `T_p ~= directsum_(q != p) Z(q^infty)` its countable torsion
subgroup.  Every trace `phi` of `N` has a central measure `mu` on `S_p`
(`phi(c(z)) = int zeta(z) dmu`).  Claim (established; proof route):

1. If `mu(T_p) = 0` then `phi` vanishes off the center:
   `phi(a(x)b(y)c(z)) = 0` for `(x,y) != (0,0)`.
2. Sharp converse: if `mu(T_p) > 0` there are non-canonical traces with
   central measure `mu`, supported on `(mZ[1/p])^2`-cosets over the torsion
   atoms.
3. Fiberwise: traces with central character `zeta` are the tracial states of
   the Latremoliere--Packer noncommutative solenoid `C*(Z[1/p]^2, sigma_zeta)`
   (arXiv:1110.6227, NYJM 24A (2018) 155-191); that algebra has a unique
   trace iff `zeta` is NONTORSION (= LP-aperiodic, their Thms 2.12/3.5/3.6),
   including all rational aperiodic `zeta` — strictly weaker than
   irrationality, and the leak-relevant sector `Ann(Z) ~= Z_p` is exactly
   rational aperiodic minus the point `1`.

Consequences wired elsewhere: components of any enemy restriction over any
window containing `N` are a.e. canonical
(`amenable-carrier-windows-are-character-transparent` uses this), and Haar,
or any atomless central measure, forces canonicality.
