---
rg: 2
id: dcglt-stabilizer-rounding-is-vacuous-at-torsion-free-index
kind: claim
title: The dCGLT p-adic covers have the same normalized sector profile as a torsion-free finite-index subcover whose building stabilizers are central
artifacts:
  - research/artifacts/solve-nh-dcglt-2026-09-13.md
distinct_from:
  twisted-factor-existence-is-equivalent-to-nonhyperlinearity: that is the general existential equivalence between non-CE twisted group algebras and nonhyperlinear groups; this fixes the de Chiffre--Glebsky--Lubotzky--Thom p-adic covers, pins their construction against the source, and shows that finite-index passage transfers the normalized sector profile in both directions.
  deligne-symplectic-covers-are-not-schatten-approximated: that concerns the real Deligne covers of Sp_2g(Z), whose building-free geometry has infinite stabilizers, and proves the Frobenius collapse; this concerns the p-adic dCGLT covers and proves only a two-sided transfer of the normalized sector profile along finite index.
  gowers-hatami-finite-group-hs-stability: that is the finite-group rounding theorem; this shows that rounding on the finite building stabilizers of a dCGLT cover cannot reduce the sector problem, because a torsion-free finite-index subcover has only central stabilizers and the same profile.
---

**ESTABLISHED** (`dcglt-stabilizer-rounding-vacuous-proof`). Unreviewed.

**Setting.** de Chiffre--Glebsky--Lubotzky--Thom, arXiv:1711.10238, Section
"Non-residually finite 2-Kazhdan groups" (TeX source lines 1038--1094, read on
MSI):

- `D` is the standard quaternion order over `Z`, `h` the canonical hermitian
  form on `D^n`, and `G = SU(n, D, h)`, absolutely almost simple, simply
  connected, of type `C_n`, with `G(R) = Sp(n)` compact and `G(Q_p) = Sp(2n, Q_p)`
  for `p >= 3`.
- `Gamma = G(Z[1/p])`, identified in the source with
  `U(2n) cap Sp(2n, Z[i, 1/p])`, is a cocompact lattice in `G(Q_p)`.
- `1 -> C(p) -> Gamma~ -> Gamma -> 1` is the restriction of the universal
  central extension of `G(Q_p)` (Prasad); `C(p)` is the cyclic group of roots of
  unity in `Q_p`, of order `p - 1`.
- The source Proposition: every finite-index subgroup of `Gamma~` contains the
  unique index-two subgroup of `C(p)`; for `p >= 5`, `Gamma~` is not residually
  finite.
- For `n >= 3` and `p >= q_0(n)` (Garland, Ballmann--Swiatkowski, source
  Theorem `higherkazhdan`) `Gamma~` is 2-Kazhdan, hence Frobenius stable
  (source Theorem `main2`) and not Frobenius-approximated (source Corollary
  `corka`).

Fix `p >= 5`, `n >= 3`, a generator `z` of `C(p)`, and `zeta` with
`zeta^(p-1) = 1`. For a group `E` containing `z` centrally and a finite
presentation `<S cup {z} | R>`, write

```text
sigma_E(d) = inf { max_(r in R) ||rho(r) - I||_HS : rho : S cup {z} -> U(d), rho(z) = zeta I },   (TF0)
```

with `||A||_HS = d^(-1/2) tr(A^* A)^(1/2)`, `rho` extended homomorphically to
words.

**Claim.**

```text
(TF1) Gamma has a torsion-free normal subgroup Lambda of finite index k.  Its preimage
      Lambda~ in Gamma~ contains C(p) centrally, and every finite-index subgroup of
      Lambda~ contains the index-two subgroup of C(p).  So Lambda~ is not residually finite.

(TF2) Lambda acts freely on the Bruhat--Tits building B of G(Q_p); Y = Lambda\B is a finite
      simplicial complex of dimension n with pi_1(Y) = Lambda.  In the action of Lambda~
      on B through Lambda, every cell stabilizer is exactly C(p).

(TF3) For fixed finite presentations of Gamma~ and Lambda~ and a fixed transversal there
      are constants N, N' >= 1 with, for every d >= 1,
          sigma_(Lambda~)(d)   <= N  sigma_(Gamma~)(d),
          sigma_(Gamma~)(k d)  <= N' sigma_(Lambda~)(d).

(TF4) Assume in addition p >= q_0(n) and zeta^2 != 1.  There is delta > 0 such that every
      rho : S cup {z} -> U(d) with rho(z) = zeta I has unnormalized Frobenius defect
      max_(r in R) ||rho(r) - I||_Frob >= delta, for every d.  Equivalently
          sigma_(Gamma~)(d) >= delta d^(-1/2).
```

So `Gamma~` has a dimension-independent sector-`zeta` floor iff `Lambda~` has
one. By `(TF2)`, the finite complex of finite stabilizers of `Gamma~` is
replaced by a complex whose stabilizers are the central group on which
`rho(z) = zeta I` already holds exactly. Gowers--Hatami rounding on building
stabilizers therefore carries no information that `Lambda~` does not already
see: every floor argument built from the finite local groups of `Gamma~` must
work verbatim for the free complex `Y`.

`(TF4)` is the p-adic analogue of `(SG1)` in
`deligne-symplectic-covers-are-not-schatten-approximated`: the same exponent
`1/2`, now for the dCGLT covers. By `(TF3)` it transfers to `Lambda~` with a
change of constants.

**Scope.** This decides no dimension-independent floor. It does not show that `Gamma~` is or is not
hyperlinear, and it is unrelated to the Frobenius collapse, which the source
proves. The remaining problem is the normalized sector problem for
`Lambda~`, a central extension of `pi_1(Y)` by `C(p)`; see the artifact for the
wall it meets.
