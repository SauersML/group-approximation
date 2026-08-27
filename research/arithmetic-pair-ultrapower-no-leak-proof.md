---
rg: 2
id: arithmetic-pair-ultrapower-no-leak-proof
kind: route
title: Decompose the conjugation module over C-conjugacy orbits; abelian centralisers (n=2) or property (T) (n>=3) give the spectral gap
target: arithmetic-pair-group-factor-ultrapower-has-no-leak
requires: []
---

Throughout `C = SL_n(Z) <= A = SL_n(Z[1/p])`, `Z = Z(A)`, and
`L^2(L(A)) = l^2(A)` with `C` acting by conjugation
`c . delta_g = delta_(c g c^-1)`, which is the action `x -> u_c x u_c^*`
on `L^2(L(A))`.

**Step 1 (orbit decomposition).**  The conjugation action preserves
`l^2(Z)` (central elements are fixed) and its orthocomplement
`H = l^2(A) (-) l^2(Z)`, which is the orthogonal direct sum, over the
`C`-conjugacy orbits `O = {c g c^-1 : c in C}` of non-central `g in A`, of
the permutation modules `l^2(O) ~= l^2(C / C_C(g))`, where
`C_C(g) = {c in C : c g = g c}`.

**Step 2 (every orbit is infinite).**  For non-central `g in A`, the
centraliser `C_(SL_n)(g)` is a proper Zariski-closed subgroup of `SL_n`.
By Borel density `C = SL_n(Z)` is Zariski dense in `SL_n`, and so is every
finite-index subgroup of `C`; hence `C_C(g) = C cap C_(SL_n)(g)` has
infinite index in `C`, and every orbit `O` is infinite.  (This is the
relatively-icc observation already recorded in
`relative-commutant-collapse-for-sl2-pair`; it gives the exact statement
`L(C)' cap L(A) = L(Z)`.)

**Step 3 (spectral gap of `H`).**  We show the unitary representation of
`C` on `H` has no almost-invariant vectors, i.e. there are a finite
`S subset C` and `kappa > 0` with

```text
max_(s in S) || s . xi - xi ||  >=  kappa ||xi||      for all xi in H.   (UPLP1)
```

*Case `n >= 3`.*  `C = SL_n(Z)` has Kazhdan's property (T).  By Step 2 no
`l^2(C / C_C(g))` has a nonzero invariant vector (an invariant vector is
constant on the infinite orbit and square-summable, hence zero), so `H`
has no invariant vectors, and property (T) gives `(UPLP1)` with the
Kazhdan constant of any finite generating set `S`.

*Case `n = 2`.*  `C = SL_2(Z)` has no property (T), but every centraliser
is small: for non-central `g in SL_2(Z[1/p]) subset SL_2(Q)`, the
centraliser of `g` in `SL_2(bar Q)` is a maximal torus if `g` is
semisimple and the group `{+-(1 + t N)}` (`N` nilpotent) if `g` is not
semisimple; in both cases it is abelian, hence so is `C_C(g)`.  A
quasi-regular representation `l^2(C/H)` with `H` amenable is weakly
contained in the regular representation `lambda_C` (induce
`1_H prec lambda_H` from `H` to `C`), weak containment passes to direct
sums, so `H prec lambda_C`.  If `H` had almost-invariant vectors then
`1_C prec H prec lambda_C`, forcing `SL_2(Z)` to be amenable, which it is
not.  Hence `(UPLP1)` holds for some finite `S` and `kappa > 0`.

**Step 4 (from group elements to the algebra, and the ultrapower).**  Let
`x = (x_k)_k` represent an element of `L(C)' cap L(A)^omega`, with
`sup_k ||x_k|| < infinity` and `lim_omega ||u_c x_k - x_k u_c||_2 = 0` for
every `c in C`.  Write `x_k = z_k + y_k` with `z_k = E_(L(Z))(x_k)` the
orthogonal projection of `x_k` onto `l^2(Z)` and `y_k in H`; the
projection commutes with conjugation by `C`, so
`lim_omega ||s . y_k - y_k||_2 = 0` for each `s in S`, and `(UPLP1)` gives
`lim_omega ||y_k||_2 = 0`.  Therefore `x = (z_k)_k in L(Z)^omega`.  Since
`L(Z) = Z(L(A))` and `Z(L(A))^omega subseteq L(A)' cap L(A)^omega
subseteq L(C)' cap L(A)^omega`, all three algebras in `(UPL1)` coincide.

**Consequences.**  (1) With `M = L(A)^omega` the identity `(UPL1)` is
`(RCC)`; an embedding `L(G) -> L(A)^omega` over `L(A)` would send the
stable letter to a unitary of `L(C)' cap L(A)^omega = L(Z)^omega`, which
commutes with `L(A)`, contradicting `[t, a] != e` with regular trace `0`.
(2) Taking `x` to be a central sequence of `L(A)` in `(UPL1)` shows
`L(A)' cap L(A)^omega = L(Z)^omega`, i.e. `L(A)` is full modulo its
centre; the spectral-gap statement for the inclusion `L(C) subset L(A)`
is `(UPLP1)` restricted to `L^2(L(A)) (-) L^2(L(C))`.  (3) For a general
tracial `M supseteq L(A)`, `L^2(M) = L^2(L(A)) (+) K_M` is a `C`-invariant
orthogonal decomposition, the `C`-fixed vectors of `L^2(L(A))` are
`L^2(L(Z))` by Steps 1--3 (exact version: `L(C)' cap L(A) = L(Z)`), and
these are `A`-fixed; so a `C`-fixed vector `k` of `L^2(M)` is `A`-fixed iff
its `K_M`-component is, which is `(UPL2)`.

Literature used: Borel density (Borel 1960) for Step 2; Kazhdan's property
(T) for `SL_n(Z)`, `n >= 3`; weak containment of quasi-regular
representations with amenable stabilisers in the regular representation
and the Hulanicki--Reiter characterisation of amenability (Bekka--de la
Harpe--Valette, *Kazhdan's Property (T)*, App. G and Thm. G.3.2) for Step
3; Popa's notion of spectral gap for inclusions (Popa, *On the
superrigidity of malleable actions with spectral gap*, JAMS 2008) for the
terminology in (2).
