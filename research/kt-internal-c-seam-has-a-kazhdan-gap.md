---
rg: 2
id: kt-internal-c-seam-has-a-kazhdan-gap
kind: claim
title: The internal Kun--Thom C-seam has a uniform Kazhdan gap stable under finite amplification
distinct_from:
  kt-canonical-afp-seam-has-no-internal-gauge-correction: that qualitatively excludes a nonzero exact intertwiner; this gives a dimension-free lower bound for every approximate intertwiner and every finite diagonal amplification.
  kt-ab-normalizer-row-forces-wall-gauge-propagation: that bounds a two-copy wall by one mixed row; this applies the Kazhdan constant to the complete finite Gamma generating packet.
  kt-single-root-majorana-return-finite-countermodels: that shows one visible root row has exact finite countermodels; this uses a Kazhdan set for all of Gamma and therefore does not contradict that firewall.
---

**ESTABLISHED QUANTITATIVE INTERNAL NO-GO.**  In the notation

```text
M=R rtimes P_A,       N=ker(P_A->G),
v_gamma=u_(C gamma C^(-1)),   rho_gamma=u_(alpha_C(gamma)),
```

fix a Kazhdan pair `(Q,kappa)` for `Gamma`.  Then every
`xi in L^2(L(N))` satisfies

```text
max_(gamma in Q) ||xi v_gamma-rho_gamma xi||_2
 >= kappa ||xi||_2.                                    (KIG1)
```

The same inequality holds in
`L^2(M_m(C) tensor L(N))` for every finite `m`, with `v_gamma,rho_gamma`
amplified diagonally.  In particular every unitary internal gauge, at every
finite amplification, pays seam defect at least `kappa` on one row.

This rules out the formal finite-block shortcut.  The flip unitary does
intertwine

```text
v directSum rho       with       rho directSum v,
```

but it does not intertwine a diagonal amplification of the same pasted
`H_A` representation.  Using the mixed sum changes the `H_A` action from one
block to the next.  Making that change covariant under all of
`S=SL_3(Z)` is the usual induction over `S/<A>`, which is infinite because
`S` is not virtually cyclic.  The fact that `C^3=1` supplies only a
three-cycle of the Gamma automorphism; it does not turn `S/<A>` into a
three-point set or impose the remaining `A,C` relators.  Thus two- or
three-block symmetrization does not produce a lift of the mixed actor.

DERIVATION
kt-internal-c-seam-kazhdan-gap-proof
