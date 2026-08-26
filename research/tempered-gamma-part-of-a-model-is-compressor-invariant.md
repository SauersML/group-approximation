---
rg: 2
id: tempered-gamma-part-of-a-model-is-compressor-invariant
kind: claim
title: The tempered part of the subgroup action on a model's standard space is compressor-invariant and central, and on it the subgroup carries a trace of its reduced C*-algebra, hence its regular character when the amenable radical is central
distinct_from:
  finite-dimensional-gamma-part-of-a-model-is-compression-blind: that isolates the closure of the finite-dimensional subrepresentations, on which compression is absorbed; this isolates the closure of the subrepresentations weakly contained in the regular representation, on which nothing is absorbed but the character of the subgroup is pinned to the regular one, so that every model of the Kun--Thom pair is the direct sum of an atomic corner, a regular-character corner, and a remainder with neither kind of subrepresentation.
  amenable-kazhdan-models-absorb-compression: that is a rigidity statement for amenable subgroup algebras; this is a decomposition statement for arbitrary models, one of whose corners is exactly the regular-character setting of every canonical route.
---

Let `Gamma <= G`, `t in G` with `t Gamma t^(-1) <= Gamma`, and let
`pi : G -> U(N)` be any homomorphism into a von Neumann algebra `(N, tau)`
with faithful normal tracial state.  Let `Gamma` act on `H = L^2(N)` by left
multiplication and put

```text
T_Gamma = closure of the sum of all closed L_Gamma-invariant subspaces of H
          whose Gamma-representation is weakly contained in the left regular
          representation lambda_Gamma,
```

the **tempered part** of the action, with projection `f = e_(T_Gamma)`.

**Theorem** (no hypothesis on `Gamma`, `G`, `pi` or the character).

1. `f in N`; `f` commutes with `pi(Gamma)`, with `pi(t)` for every compressor
   `t`, and with `pi(Gamma)' cap N`; and `T_Gamma = T_(t^(-1) Gamma t)`.
2. `f` is orthogonal to the finite-dimensional part `e` of
   `finite-dimensional-gamma-part-of-a-model-is-compression-blind` whenever
   `Gamma` is non-amenable.
3. On the corner `f N f` the normalized character
   `chi_f(gamma) = tau(pi(gamma) f) / tau(f)` is a tracial state of the
   reduced C*-algebra `C*_r(Gamma)`.
4. Consequently, if every tracial state of `C*_r(Gamma)` is supported on a
   finite central subgroup `Z` -- which by Breuillard--Kalantar--Kennedy--Ozawa
   (*C*-simplicity and the unique trace property for discrete groups*, Publ.
   Math. IHES 126 (2017); their theorem that tracial states of `C*_r` are
   supported on the amenable radical) holds as soon as the amenable radical
   of `Gamma` is a finite central subgroup `Z` -- then `chi_f` vanishes off
   `Z`, and `pi(Gamma)'' f` is a corner of `L(Gamma)` cut by a central
   projection of `L(Z)`: on the tempered corner the subgroup is represented
   with its **regular character modulo the finite center**.

**The Kun--Thom subgroup qualifies.**  For `Gamma = EL_r(F_q[x_1..x_d])`,
`r >= 3`, every subgroup normalized by `Gamma` is sandwiched between
`E_r(R_+, I)` and the congruence-type subgroup of a unique ideal `I`
(Vaserstein's sandwich theorem for `r >= 3` over commutative rings, *On the
normal subgroups of GL_n over a ring*, LNM 854 (1981)); for `I != 0` the
group `E_r(R_+, I)` contains `e_12(a), e_12(a'), e_21(b)` with
`a = c x_1`, `a' = c x_1^2`, `b = c x_1` for any nonzero `c in I`.  Viewed
in `SL_2(K)`, `K = F_q(x_2, ..., x_d)((x_1^(-1)))` a complete discretely
valued field, these act on the Bruhat--Tits tree of `SL_2(K)`: the products
`e_12(a) e_21(b)` and `e_12(a') e_21(b)` are hyperbolic with distinct axes
(`a != a'`), and the three generators fix no common end.  So they generate a
non-elementary group of tree automorphisms, which contains a free subgroup and
is non-amenable.  (Two generators do not suffice when `p = 2`: `e_12(a)` and
`e_21(b)` are then involutions generating an infinite dihedral group.)  Thus
the amenable radical of `Gamma` is its finite center, and (4) applies.

**What this buys.**  Together with the finite-dimensional part, every
unitary model of the Kun--Thom pair -- and, since the projections are
central for them, every model of the coset wreath `W`, the free-lamp group
`E` and the double `D` -- decomposes into three compressor-invariant corners:

```text
1 = e (+) f (+) (1 - e - f):
  e      atomic Gamma-algebra, compression absorbed, never faithful;
  f      regular character on Gamma mod center -- the canonical setting of
         every route into hyperlinear-wreath-model and the Kun--Thom double;
  1-e-f  the Gamma-action has no finite-dimensional and no tempered
         subrepresentation at all.
```

The abstract-embedding freedom of
`abstract-unitary-embedding-upgrades-to-hyperlinear` therefore adds exactly
one new regime to the canonical one: models whose `Gamma`-part is weakly
mixing and non-tempered (for example built from non-tempered
infinite-dimensional representations of `Gamma`), and nothing else.  A
character-rigidity theorem for `Gamma` in the sense of Bekka and Peterson
(every character finite-dimensional or regular) would make the remainder
corner carry a mixture of the two known characters and would be the natural
next fence; `Gamma` is not a lattice for `d >= 2`, so no such theorem is
available off the shelf.
