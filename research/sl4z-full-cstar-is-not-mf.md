---
rg: 2
id: sl4z-full-cstar-is-not-mf
kind: claim
title: The full group C*-algebra of SL_4(Z) is not MF
artifacts:
  - research/artifacts/sl4z-thin-corona-gap-reduction-2026-09-16.md
distinct_from:
  sl4z-reduced-cstar-is-not-mf: that is the reduced algebra C*_r(SL_4(Z)), where the thin relative gap holds on every MF model; this is the maximal algebra, which contains the thin quasi-regular representation and is already known not to be RFD.
  kt-full-double-cstar-is-not-mf: that is a full double C*-algebra of a Kun--Thom construction; this is the maximal group C*-algebra of the lattice SL_4(Z) itself.
---

`C*(SL_4(Z))` admits no injective *-homomorphism into
`prod_n M_(k_n) / sum_n M_(k_n)` for any sequence `k`.

**Known nearby facts.**
- `C*(SL_n(Z))`, `n >= 3`, is not residually finite-dimensional.  This is Bekka's theorem,
  reproved with the explicit witness `x = mu(1-p)` in
  `sln-z-thin-quasiregular-not-weakly-contained-in-fd`.
- MF is strictly weaker than RFD in general.  For a Kazhdan group, non-RFD does not by
  itself rule out MF: an MF embedding need not factor through the finite-dimensional
  representations.

**Routes.**
- `sl4z-full-not-mf-from-thin-corona-gap` derives this claim from the corona crux
  `sl4z-corona-reps-have-thin-relative-spectral-gap`.
- The same argument shows that `sigma_C(C*(SL_4(Z)))` is not MF, where `sigma_C` is the thin
  quasi-regular representation.  It also shows that no `C*(Lambda)` with
  `Lambda >= SL_4(Z)` is MF.
- Point-norm matricial stability of `SL_4(Z)` would give this claim directly: every
  corona representation would factor through the RFD quotient, so an MF embedding would
  make `C*(SL_4(Z))` RFD.  That composite passes through the crux.

**Contrapositive use.**  An MF model of `C*(SL_4(Z))` would refute both the crux and
`sl4z-matricially-stable`.

## Attempts

- **Non-RFD directly.**  Theorem B gives a norm drop from `||x|| = 1` to
  `||x||_FD <= 1 - epsilon`.
  - A general MF embedding is an operator-norm corona representation, not a product of
    genuine representations, so the drop does not transfer without the crux.
- **Traces.**  The obstruction behind the crux lives on single top eigenvectors of lifts
  of `pi(x)`.  A normalized trace gives such vectors weight `1/k_n`, so trace-based
  arguments do not see it.
  - Bekka (Invent. Math. 169 (2007), arXiv:math/0609102) describes the tracial states of
    `C*(SL_n(Z))`.  Its abstract, checked 2026-09-16, says none is faithful.  The
    description itself was not re-read.
- **Via the reduced algebra.**  `C*_r(SL_4(Z))` is a quotient of `C*(SL_4(Z))`.
  - MF does not pass to quotients in general: every separable C*-algebra is a quotient of
    the RFD algebra `C*(F_infinity)`.  So `sl4z-reduced-cstar-is-not-mf` would not give
    this claim.
  - Non-MF of the full algebra says nothing about its quotients, so this claim does not
    give `sl4z-reduced-cstar-is-not-mf` either.
