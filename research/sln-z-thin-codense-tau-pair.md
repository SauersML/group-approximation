---
rg: 2
id: sln-z-thin-codense-tau-pair
kind: claim
title: SL_n(Z) for n at least three has a thin finitely generated co-dense subgroup with property tau via Bourgain-Varju
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that is SL_2(Z) inside SL_2(Z[1/p]) with the FULL modular group as the subgroup and Selberg's gap; this is a THIN (infinite-index, Zariski-dense free) subgroup INSIDE the plain lattice SL_n(Z) itself, with Bourgain-Varju arbitrary-modulus expansion as the gap.
  sl3-pair-relative-commutant-route: that is SL_3(Z) inside SL_3(Z[1/2]); this takes the host to be SL_n(Z) itself with a thin subgroup, so the open hypothesis becomes flexible stability of the PLAIN lattice.
---

Let `n >= 3` and `A = SL_n(Z)`.  There is a four-generated free
Zariski-dense subgroup `C = <g_1,g_2,g_3,g_4> <= A` of infinite index (a thin
subgroup) that surjects onto `SL_n(Z/m)` for every `m` (saturated), and:

1. **Every finite-dimensional unitary representation of `A` factors through
   a congruence quotient `SL_n(Z/m)`.**  A unitary f.d. representation has
   compact image; by Margulis superrigidity a homomorphism of `SL_n(Z)`
   (`n >= 3`) to a compact Lie group has finite image, and by the
   Bass--Milnor--Serre congruence subgroup property every finite quotient of
   `SL_n(Z)` is a congruence quotient (recorded in Bekka's operator-algebraic
   superrigidity, Invent. Math. 169 (2007)).
2. **Co-density.**  `C` saturated surjects onto every `SL_n(Z/m)`, so for
   every finite-dimensional `rho` (factoring through some `SL_n(Z/m)`),
   `rho(C) = rho(A)`, hence `rho(C)' = rho(A)'`.  Existence is supplied
   directly by Aka--Gelander--Soifer, *Homogeneous number of free
   generators* (arXiv:1205.1140): for every `n>2`, `SL_n(Z)` contains a
   four-generated free subgroup dense in its profinite completion.  It is
   automatically Zariski dense, and it has infinite index because a
   finite-index subgroup of the Kazhdan group `SL_n(Z)` has property `(T)`,
   whereas a nonabelian free group does not.
3. **Uniform conjugation gap = property (tau).**  Bourgain--Varju,
   *Expansion in `SL_d(Z/qZ)`, `q` arbitrary* (Invent. Math. 188 (2012)
   151--173): for a Zariski-dense `C = <S> <= SL_n(Z)`, the Cayley graphs of
   `pi_m(C)` are uniform expanders over ARBITRARY modulus `m`.  Profinite
   density makes `pi_m(C)=SL_n(Z/m)` for every `m`.
   This is exactly property `(tau)` of `C` with respect to the family of
   congruence quotients through which all finite-dimensional representations
   of `A` factor -- the only input the `(tau)`-form of
   `hnn-over-codense-kazhdan-subgroup-not-hyperlinear` consumes.  (Square-free
   modulus, Salehi-Golsefidy--Varju, would not suffice; the arbitrary-modulus
   theorem is the needed input and it holds for `SL_n`.)

So `(A, C)` satisfies every hypothesis of the HNN theorem, and `a_1 in A \ C`
exists since `C` has infinite index; Britton gives `[t, a_1] != 1` in
`G = <SL_n(Z), t | [t, C] = 1>`.

**Explicit rank-two specialization.**  For `n=3`,
`explicit-sl3-thin-codense-tau-pair` supplies two displayed integer matrices
`a,b` generating a free profinitely dense subgroup, and the displayed
order-three matrix `r notin <a,b>`.  Thus the same endpoint can be written
literally as

```text
< SL_3(Z), t | [t,a]=1, [t,b]=1 >,
```

with marked word `[t,r]`.  The four-generator Aka--Gelander--Soifer theorem
remains the uniform existence result for every `n >= 3`; it is no longer
needed for explicitness in rank three.

**Why this host is new.**  Neither published route covers the plain lattice
`SL_n(Z)`: Dogon arXiv:2211.10492 needs a central extension by a torsion-free
`Z`, but `SL_n(Z)` has the congruence subgroup property so its universal
central extension has finite kernel (`K_2(Z) = Z/2`) and there is no Deligne
extension; Dogon--Vigdorovich Theorem 4.1 needs an archimedean factor with
`pi_1 = Z`, but `pi_1(SL_n(R)) = Z/2`.  The commutant/HNN route uses neither,
so `SL_n(Z)` is admissible, and the goal reduces to flexible HS-stability of
the most-studied lattice in the subject.  This is the exact HS analogue of
Bowen--Burton (flexible permutation stability of `PSL_d(Z)`, `d >= 5`, implies
a non-sofic group), now from `n = 3` via Bourgain--Varju + Britton.
