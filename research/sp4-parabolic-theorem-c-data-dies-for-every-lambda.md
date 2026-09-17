---
rg: 2
id: sp4-parabolic-theorem-c-data-dies-for-every-lambda
kind: claim
title: ISW Theorem C data never exists on an Sp4 parabolic, for any relative-(T) subgroup and any action; the torsion-Levi residue is empty
distinct_from:
  sp4-parabolic-radical-theorem-c-data-dies: that kills Theorem C data only for Lambda inside the unipotent radical R and leaves open the torsion-Levi residue (Lambda not in R, finite nontrivial Levi image, d-torsion classes); this closes that residue for EVERY Lambda <= P with (P,Lambda) relative (T), by a new Levi-coset counting lemma showing that the full P-stabilizer field is central, which the radical-only argument never needed.
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that is the scalar Theorem A surface on the radicals; this is the operator-valued Theorem C surface on the whole parabolic.
  sp4-isw-theorem-c-embeddable-twist-data-exists: that is the surviving Theorem C mouth with Lambda not virtually in a parabolic (e.g. Lambda = Gamma = Sp_4(Z)); this proves the parabolic mouth is empty, so that one is now the only Theorem C mouth.
  amenable-by-virtually-free-twisted-crossed-products-are-ce: that removes the Connes-embeddability toll on parabolics; this shows the cohomological half of Theorem C is never available there, so the free toll buys nothing.
  sp2g-z-full-c-star-algebra-has-llp: a fence on one refutation mechanism (Theorem C through a parabolic), not a decision of the root.
---

**ESTABLISHED (route `sp4-parabolic-theorem-c-every-lambda-proof`).**  Let `P`
be a finite-index subgroup of the Siegel parabolic `P_S = Sym_2(Z) x| GL_2(Z)`
or of the Klingen parabolic `P_K = N_K x| ({+-1} x SL_2(Z))` of `Sp_4(Z)`, and
`R = P cap (unipotent radical)`.  Let `Lambda <= P` be ANY subgroup such that
`(P, Lambda)` has relative property (T).  Let `sigma : P ~> (X,mu)` be p.m.p.
with `sigma|Lambda` ergodic, and `c_n in Z^2(P, L^0(X,T))` with
`||c_n(g,h) - 1||_2 -> 0` for all `g, h`.  Then

```text
c_n|Lambda is a 2-coboundary for all but finitely many n.        (TC-P)
```

So the hypotheses of Ioana--Spaas--Wiersma Theorem C (arXiv:2006.01874, p. 3)
are never met by a pair `(P, Lambda)`.  The torsion-Levi residue left OPEN by
`sp4-parabolic-radical-theorem-c-data-dies` (Consequence 1) is empty.

**Where every member dies (the invariant).**  The invariant is the full
stabilizer field `x -> S_x = Stab_P(x)`, not only its radical part.

1. **Counting lemma.**  Put `V = R` (Siegel) or `V = R/Z_R` (Klingen).  If
   `S_x cap R = K` a.e., with `K = 1` (Siegel) or `K in {1, mZ_R}` (Klingen),
   then a.e. `S_x <= K . {1, -I_4}`, so `S_x` is central in `P` and a.e.
   constant.  Reason: `S_x` meets each coset `gR` in at most one `K`-coset.  The
   sets `Fix(r g r^{-1})`, `r in R`, have equal measure.  When the Levi image of
   `g` acts nontrivially on `V`, the `R`-conjugates of `gK` form an infinite
   family, so these sets are pairwise a.e. disjoint and have measure `0`.  The Levi kernel is `{+-I_4}`, and `(r_0 (-I_4))^2 = r_0^2 in K`
   forces `r_0 in K`.
2. **Central isotropy** (radical types free and `mZ_R`).  Every
   `w in W = Stab_Lambda` is central and acts trivially.  The commutator
   1-cocycle `g -> c_n(w,g) c_n(g,w)^{-1}` lives on all of `P`.  Relative (T)
   trivializes it on `Lambda`, and the class descends to `Lambda/W`.  That group
   is amenable (finite Levi image), acts freely and ergodically, and CFW gives
   `H^2 = 0`.
3. **Finite-orbit type.**  `X` is finite.  By Shapiro the class sits on
   `Lambda_1 = Stab_Lambda(x_0)`.  Its restriction to `Lambda_1 cap R` dies
   eventually by the finite invariant `H_2`-characters of the radical case.
   `ker(res: H^2(Lambda_1,T) -> H^2(Lambda_1 cap R, T))` is finite, because the
   Levi image `C` is finite and `H^1(C, torus)` and `H^2(C,T)` are finite.
   `B^2(Lambda_1,T)` is compact, so it is open in the finite-index overgroup of
   cocycles that are trivial on `Lambda_1 cap R`.  Pointwise convergence then
   forces eventual triviality.

**Consequences.**

1. **Parabolic Theorem C is dead as a class.**  Every attempt to refute the LLP
   of `C^*(P)`, and through `P <= Sp_4(Z)` that of `C^*(Sp_4(Z))`, by ISW
   Theorem C with the subgroup data inside a parabolic dies at step 1: the
   isotropy is central.  This holds whether or not `Lambda cap R` is ergodic
   and for every `d = [Lambda : Lambda cap R]`.
2. **For `Gamma = Sp_4(Z)`.**  Any Theorem C data `(Gamma, Lambda, sigma, c_n)`
   with `Lambda <= P` and `(P, Lambda)` relative (T) restricts to data on `P`,
   so it does not exist.  The remaining Theorem C mouth is
   `sp4-isw-theorem-c-embeddable-twist-data-exists`: `Lambda` with
   `(Sp_4(Z), Lambda)` relative (T), but with no parabolic `P >= Lambda` for
   which `(P, Lambda)` has relative (T).  This includes `Lambda = Gamma`, and
   amenable `Lambda <= P` with infinite (virtually cyclic) Levi image.
