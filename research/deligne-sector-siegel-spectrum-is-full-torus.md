---
rg: 2
id: deligne-sector-siegel-spectrum-is-full-torus
kind: claim
title: In every representation of a nontrivial Deligne sector the Siegel unipotent joint spectrum is the whole torus, and every trace induces Haar measure on it
artifacts:
  - research/artifacts/deligne-sector-siegel-spectrum-2026-09-17.md
distinct_from:
  sln-z-unipotent-spectrum-finite-or-full-torus: that is the untwisted SL_d(Z) dichotomy with a genuinely nonempty finite (congruence) branch; this is the Deligne-sector version for the Siegel radical of Sp_4(Z), where the finite branch is empty, so every representation, corona and regular alike, sits in the full-torus branch.
  deligne-triple-cover-fd-central-invisibility: that forbids finite-dimensional representations with z -> omega; this extends the invisibility from representations to the Siegel spectral invariant of arbitrary unital C*-representations, including corona and ultraproduct ones.
  sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full: that reduces the SL_4(Z) corona crux to its full-spectrum case with a nonempty other branch; this shows the transplanted reduction is vacuous in a Deligne sector because the non-full branch never occurs.
  deligne-maslov-sector-traces-are-central-regular: that classifies traces on the fibre; this reads off the consequence that the Siegel spectral measure of every trace, in every representation, is Haar.
---

**THEOREM.**  Let `E_3` be Deligne's triple cover of `Gamma = Sp_4(Z)`,
`p : E_3 -> Gamma`, `ker p = <z>`, fix `omega != 1` with `omega^3 = 1`, and
put `A_omega = C^*(E_3)/(z - omega)`, with canonical unitaries `u_g`.
In a symplectic basis ordered `e_1, e_2, f_1, f_2` let
`n(X) = [[I, X],[0, I]]`, `X in Sym_2(Z)`, be the Siegel radical `U = Z^3`
(`X = [[a,b],[b,c]] <-> (a,b,c)`) and `m(A) = diag(A, A^-T)`,
`A in GL_2(Z)`, its Levi.  Let `sigma : A_omega -> B` be any unital
*-homomorphism into a nonzero unital C*-algebra.  Using a character
`phi : p^-1(P_S) -> T` with `phi(z) = omega`
(`deligne-multiplier-trivial-on-sl2xsl2-and-parabolics`), put
`V(g) = conj(phi(g)) sigma(u_g)`; it descends to an honest unitary
representation of `P_S(Z)` in `B`.  Let `Y` be the joint spectrum of
`V(U)`, i.e. `C^*(V(U)) = C(Y)`, `Y` a closed subset of `T^3`.  Then:

```text
(S1) Y = T^3.
(S2) For every lift g in E_3 of a Siegel-radical element n(X), X != 0,
     spec sigma(u_g) = T.  Hence the same holds for every lift of an
     element of Gamma conjugate into U, e.g. every long root element.
(S3) For every tracial state tau on B, tau o sigma restricted to C(Y)
     is Haar measure on T^3.
```

`Y` does not depend on `phi` (two choices differ by a character of
`P_S(Z)`, which moves `Y` by a translation, and `T^3` is translation
invariant).

**Why it matters (class kill).**  Call a separation argument *Siegel
spectral* if its invariant is `Y`, a single long-root spectrum, or the
measure a trace induces on `Y`, and if it wins by producing a
representation of `A_omega` with finite, atomic, torsion, or non-Haar
Siegel data (the Magee--de la Salle / `sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full`
pattern: non-full unipotent spectrum -> congruence quotient -> finite-group
input).  Every such argument dies at its first step, "the representation
has non-full Siegel spectrum", because (S1) and (S3) hold for every
representation and every trace, simultaneously for `lambda_omega`, for
every corona model `A_omega -> prod M_n / sum M_n` of a putative MF
approximation, and for every tracial ultraproduct model.  In particular
MF models of `E_3` must have long-root matrices whose spectra become
dense in `T`: bounded quasi-unipotence is impossible in norm, not only in
rank (`deligne-bounded-rank-rung-anatomy-2026-09-17`, D5).

**What survives.**  Vector-level data is not rigid: the representation
induced from the character `1 x omega` of `s(NU) x <z>` (the Z/3 extension
splits over `P_S(Z)`) has a nonzero `s(NU)`-invariant vector, so atoms of
vector-state spectral measures, invariant-vector and relative-(T)
mechanisms are not killed by this theorem.

The proof is `deligne-sector-siegel-spectrum-full-torus-proof`.
