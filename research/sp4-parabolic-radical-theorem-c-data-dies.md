---
rg: 2
id: sp4-parabolic-radical-theorem-c-data-dies
kind: claim
title: Operator-valued ISW Theorem C data never lives on a subgroup of either Sp4 parabolic radical, for any action
distinct_from:
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that kills SCALAR cocycles (Theorem A) on the full radicals via finite Levi-invariant H^2; this kills OPERATOR-VALUED cocycles in L^0(X,T) (Theorem C) on EVERY subgroup of either radical for EVERY p.m.p. action, where L^0-cohomology is huge (e.g. H^2(N,L^0) = H^1(N/mZ,L^0) for central-stabilizer Klingen actions) and finiteness is unavailable.
  klingen-center-kills-isw-condition-one: that is H^2(Z,T)=0 for a cyclic Lambda; this handles all Lambda <= radical, including Heisenberg subgroups whose L^0-cohomology is nonzero.
  sp4-isw-theorem-c-embeddable-twist-data-exists: that is Theorem C with Lambda = Gamma = Sp_4(Z); this closes Theorem C with Lambda inside a parabolic radical, the case where amenable-by-virtually-free-twisted-crossed-products-are-ce would have made the CE toll vanish.
  amenable-by-virtually-free-twisted-crossed-products-are-ce: that removes the embeddability toll on parabolics; this shows the cohomological half then fails on radical subgroups, isolating the surviving torsion-Levi residue.
  sp2g-z-full-c-star-algebra-has-llp: a fence on the Theorem C refutation mouth restricted to parabolics, not a decision of the root.
---

**ESTABLISHED.**  Let `P` be a finite-index subgroup of the Siegel parabolic
`P_S = Sym_2(Z) x| GL_2(Z)` or of the Klingen parabolic
`P_K = N_K x| ({+-1} x SL_2(Z))` of `Sp_4(Z)`.  Let `R` be `P` intersected with
the unipotent radical.  Let `Lambda <= R`, let `sigma : P ~> (X,mu)` be p.m.p.
with `sigma|Lambda` ergodic, and let `c_n in Z^2(P, L^0(X,T))` satisfy
`||c_n(g,h) - 1||_2 -> 0` for all `g,h`.  In the Klingen case assume in addition
that `(P,Lambda)` has relative property (T), as ISW Theorem C does.  Then

```text
c_n|Lambda is a 2-coboundary for all but finitely many n.        (RTC1)
```

So the hypotheses of Ioana--Spaas--Wiersma Theorem C (arXiv:2006.01874, p. 3)
are never met by `(P, Lambda)` with `Lambda <= R`.

**Where every member dies.**  The invariant is the stabilizer field
`x -> Stab_R(x)`.  Its law is a `P`-invariant probability on the countable set
`Sub(R)`, so it sits on finite conjugacy orbits.  By irreducibility of the Levi
modules and ergodicity, exactly one of three cases holds a.e.

- **(a) Free.**  `Stab_R = 1`.  Here `Lambda` is amenable and acts freely and
  ergodically, and `H^2(Lambda, L^0(X,T)) = 0` (ISW p. 3, citing [CFW81]).
- **(b) Central stabilizer `mZ`, `m >= 1`.**  This case occurs only for Klingen.
  If `z^k` generates `Lambda cap mZ`, then
  `gamma_n(g) = c_n(z^k,g) c_n(g,z^k)^{-1}` is a genuine 1-cocycle on all of
  `P`, because `z` is central and acts trivially.  Relative (T), applied to the
  direct sum of the twisted Koopman representations, makes `gamma_n|Lambda` a
  coboundary for large `n`.  This makes `u_{z^k}` central after a unitary
  change.  The class then descends to `Lambda/kZ`, which acts freely, and (a)
  kills it.
- **(c) Finite-index stabilizer.**  `X` is one finite orbit.  Shapiro's lemma
  moves the class to a scalar class on `Lambda_1 <= N_1 = R cap Stab(x_0)`.
  That class is the restriction of a `P_1`-invariant character of
  `H_2(N_1,Z)`.  Rationally `H_2(N_1)` is `Sym^2 (x) det` (Siegel) or the
  standard module (Klingen), which has no coinvariants, so only finitely many
  invariant characters exist.  Pointwise convergence then makes the class
  eventually trivial.

The route is `sp4-parabolic-radical-theorem-c-data-dies-proof`.

**Consequences.**

1. Together with `amenable-by-virtually-free-twisted-crossed-products-are-ce`:
   the moreover clause of Theorem C is free on parabolics, but the cohomological
   half fails for every radical subgroup.  Relative (T) of `(P,Lambda)` forces
   `Lambda` to have finite image in the a-T-menable Levi.  So parabolic
   Theorem C data can only exist in the **torsion-Levi residue**: `Lambda` not
   contained in `R`, with `d = [Lambda : Lambda cap R]` in `{2,...,12}`.  When
   `Lambda cap R` is ergodic, `(RTC1)` for `Lambda cap R` and
   corestriction-restriction show `[c_n|Lambda]` is `d`-torsion, lying in
   `ker(res^Lambda_{Lambda cap R})`.  This residue is OPEN.
2. For `Gamma = Sp_4(Z)` with `Lambda` inside a rational parabolic radical,
   restricting the data to the parabolic gives `(RTC1)` unconditionally in the
   Siegel case.  In the Klingen case it needs relative (T) of `(P_K, Lambda)`.
   That is the classical Heisenberg-by-`SL_2(Z)` relative (T); it is not
   recorded in this graph.
