---
rg: 2
id: kt-no-sofic-central-cover-proof
kind: route
title: Hochschild--Serre for the semidirect product and the wreath, Mayer--Vietoris for the double, then the torsion-class lemma
target: kt-wreath-and-double-have-no-sofic-central-cover
requires:
  - sofic-central-covers-need-nontorsion-classes
---

**`H^2(G; Q) = 0`.**  Hochschild--Serre for `1 -> EL_r(R) -> G -> SL_d(Z) -> 1`
gives `H^2(G; Q)` a filtration with graded pieces subquotients of
`E_2^(0,2) = H^0(SL_d(Z); H^2(EL_r(R); Q))`,
`E_2^(1,1) = H^1(SL_d(Z); H^1(EL_r(R); Q))` and `E_2^(2,0) = H^2(SL_d(Z); Q)`.
`EL_r(R)` is perfect, so `H^1(EL_r(R); Q) = 0` and `E_2^(1,1) = 0`.
`E_2^(2,0) = 0` for `d >= 3` (Borel, Soule).  Finally
`H^2(EL_r(R); Q) = Hom(H_2(EL_r(R); Z), Q) = Hom(K_2(R), Q) = (Lambda^2 Q^d)^*`
in the stable range, and the `SL_d(Z)`-action on it is the natural one
(substitution automorphisms of `R` act on `K_2` and on `EL_r(R)`
compatibly); its invariants vanish for `d >= 3`.  So `H^2(G; Q) = 0`.

**`H^2(W; Q) = 0`.**  For `1 -> A -> W -> G -> 1` with `A = (+)_(G/Gamma) C_2`
torsion, `H^q(A; Q) = 0` for `q >= 1`, so the spectral sequence collapses to
`H^2(W; Q) = H^2(G; Q) = 0`.

**`H^2(D; Q) = 0`.**  Mayer--Vietoris for the amalgam `D = G *_Gamma G`:
`H^1(G; Q)^2 -> H^1(Gamma; Q) -> H^2(D; Q) -> H^2(G; Q)^2 -> H^2(Gamma; Q)`.
`Gamma` has property (T), so `H^1(Gamma; Q) = 0`, and `H^2(G; Q) = 0`; hence
`H^2(D; Q) = 0`.

**Conclusion.**  A central extension of `W` (or `D`) by `Z^k` has class in
`H^2(-; Z^k)`, whose rationalization vanishes, so the class is torsion in
each coordinate; by `sofic-central-covers-need-nontorsion-classes` (2) a
torsion class embeds the cover with finite index in `Z^k x W` (resp.
`Z^k x D`), which is nonsofic because `W` (resp. `D`) is
(`wreath-not-sofic`, `kt-pair-group-double-is-nonsofic`) and soficity passes
to subgroups and finite-index overgroups.  Finite central torsion is
removed first by (1) of the same lemma.
