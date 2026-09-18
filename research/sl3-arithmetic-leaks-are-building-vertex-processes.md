---
rg: 2
id: sl3-arithmetic-leaks-are-building-vertex-processes
kind: claim
title: Every spherical leak for the SL3 arithmetic pair is a smooth SL3(Q_2)-covariant vertex process, commutative leaks are exactly invariant random vertex subsets of the building, and real-place dynamics carries none
distinct_from:
  hecke-far-commutator-defect-formula: that extends the coefficient of one leak to a K-biinvariant positive-definite function on L; this extends the whole generated tracial dynamical system to a smooth L-action on an algebra and classifies the commutative refuters as L-invariant random vertex subsets, which is information about the algebra, not one coefficient.
  no-spherical-leak-in-matrix-ultraproducts: that is the collapse statement; this is a normal form for its refuters (what any CE counterexample must look like), not a proof or refutation of it.
  homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse: that exhibits one refuter candidate (SH1); this shows every refuter has the same L-covariant shape, that SH1 and the coset Bernoulli firewall are two instances of one invariant-random-subset class, and that the finite C-fixed dimension of SH1 separates them.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that is the Bernoulli instance; this contains it as the product-measure point of the class of invariant random vertex subsets and proves it has infinite C-fixed dimension.
  sl3-homogeneous-quotient-crossed-product-is-connes-embeddable: that is the CE question for one instance; this names the whole instance class and kills the real-place and Gaussian-of-real-representation instances, but decides no CE question.
  homogeneous-quotient-soficity-gives-vertex-soficity: that transfers soficity between the quotient and vertex actions; this is about Connes-embeddable certificates and their L-covariance, with no soficity.
  howe-moore-lattice-nonsofic-action-transfers-to-mixing: that uses Howe-Moore at the real place to make a nonsofic action mixing; this uses Howe-Moore at the real place to show the C-fixed algebra of any real-place-extendable system is A-fixed, so such systems carry no leak.
---

**ESTABLISHED (proof in `sl3-arithmetic-leaks-are-building-vertex-processes-proof`).**
Notation: `A = SL_3(Z[1/2]) = <C, h>`, `C = SL_3(Z)`, `h = diag(2,1,1/2)`,
`L = SL_3(Q_2)`, `K = SL_3(Z_2)`, `V = L/K = A/C` (type-zero-class vertex set of
the Bruhat--Tits building, identified by `A cap K = C` and density of `A` in
`L`), base vertex `o = K`.  A **leak certificate** is a tracial von Neumann
algebra `(M, tau)`, a unitary representation `u` of `A` in `M` and a unitary
`U in u(C)' cap M` with `|tau(U u_h U^* u_h^*)| < 1`.  If `M` is Connes
embeddable, the lifting in item 4 of
`homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse` refutes
`(PTS1)` of `projective-trace-square-transfer-for-sl3-pair`, and conversely
that lifting uses only `M`, `u` and `U`.

**VP1 (smooth normal form).**  Let `alpha` be a `tau`-preserving action of
`A` on a tracial algebra `(N, tau)`.  Put
`N_inf = union over compact open subgroups W < L of N^(A cap W)`.  Then
`N_inf` is an `A`-invariant unital `*`-subalgebra, the formula
`alphabar_g(x) = alpha_a(x)` for `x in N^(A cap W)` and any `a in A cap gW`
is a well-defined `tau`-preserving action of `L` on `N_inf` extending
`alpha`, it extends to a point-`||.||_2`-continuous action on
`N_sm = N_inf''`, and

```text
N^C = (N_sm)^K,     N^A = (N_sm)^L.                                  (VP1)
```

For any leak certificate `(M, u, U)` the algebra
`N = W*(u_a U u_a^* : a in A)` with `alpha = Ad u` equals `N_sm`.  Hence every
certificate is an **L-covariant unitary vertex field**: unitaries
`U_v = alphabar_g(U)` (`v = gK`) indexed by `V`, with an `L`-invariant joint
`*`-distribution, `U_o` fixed by `K`, and `|tau(U_o U_(ho)^*)| < 1`, together
with a tracial covariant extension `M >= W*(N, u(A))` of the restriction of
the `L`-action to `A`.  No other kind of refuter exists.

**VP2 (commutative refuters are invariant random vertex subsets).**  Let
`A` act by measure-preserving maps on `(Y, mu)`.  Then
`L^infinity(Y) rtimes A` contains a leak certificate with `U` in
`L^infinity(Y)` iff some `C`-invariant set `P` has `mu(P Delta hP) > 0`.  For
such `P` the coding map `Phi(y)(aC) = 1_P(a^(-1) y)` pushes `mu` to an
`L`-invariant Borel probability `nu` on `2^V` with `nu(E Delta hE) = mu(P Delta hP)`,
`E = {omega : omega(o) = 1}`, and gives a trace-preserving embedding
`L^infinity(2^V, nu) rtimes A -> L^infinity(Y) rtimes A`.  Conversely, for an
`L`-invariant Borel probability `nu` on `2^V`, `U = 1_(E^c) + i 1_E` has
`tau(U u_h U^* u_h^*) = 1 - nu(E Delta hE)`, and `nu(E Delta hE) > 0` iff `nu`
is not supported on `{empty set, V}`.  Therefore:

```text
the commutative spherical leaks refuting (PTS1) exist
  iff  some L-invariant random subset of V, not a.s. empty or full,
       has Connes-embeddable coordinate crossed product
       L^infinity(2^V, nu) rtimes A.                                   (VP2)
```

Both recorded firewalls are points of this one class: `(SH1)` codes as the
`Lambda'`-orbit colouring `omega_(g Lambda')(aC) = 1_P(a^(-1) g Lambda')`,
and the coset Bernoulli firewall is a product measure on `B^V`.

**VP3 (real-place kill).**  Suppose the `A`-action on `(N, tau)` extends to a
point-`||.||_2`-continuous `tau`-preserving action of `G_R = SL_3(R)` (through
`A < SL_3(R)`), or of `G = SL_3(R) x L` through the diagonal embedding.  Then
`N^C <= N^(SL_3(R))`.  In the first case `N^C = N^A`, so the system carries no
leak in any tracial covariant extension; in the second, every leak lives in the
`L`-system `N^(SL_3(R))` and is already covered by VP1.  In particular real
homogeneous spaces `SL_3(R)/Gamma` and `(SL_3(R) x L)/Gamma`, Gaussian actions of
continuous orthogonal representations of `SL_3(R)`, and any system built
functorially from continuous `SL_3(R)`-dynamics produce no refuter, whatever their
Connes embeddability.  The same holds for the Koopman representation of any
measurable p.m.p. action of these groups.

**VP4 (the C-fixed dimension separates the firewalls).**
`d_C(N) = dim N^C` is monotone under `A`-equivariant trace-preserving
embeddings.  `d_C(L^infinity(L/Lambda')) = r < infinity` for `(SH1)`, while for the
coset Bernoulli shift `(B, tau_B)^(tensor V)` with any base `B != C`,
`d_C = infinity`: the `C`-orbits on `V` are the finite `K`-spheres, infinite in
number, and sphere sums of a centred base element are orthogonal nonzero
`C`-fixed elements.  Hence no Bernoulli coset shift embeds `A`-equivariantly
in `L^infinity(L/Lambda')` for any cocompact `Lambda'`, or in any system with finite
`d_C`, and Connes embeddability of `(SH1)` cannot be transported to the
Bernoulli firewall through base-algebra factor maps.

**VP5 (finite C-fixed dimension means random equitable colourings).**  If
`N = L^infinity(Y, mu)` and `d_C(N) = s < infinity`, let `P_1, ..., P_s` be the
atoms of `N^C`.  For each double coset `C lambda C` in `C \ A / C = K \ V`
(the relative positions of vertex pairs), with `D_lambda = |C lambda C / C|`
and Hecke sphere `S_lambda(v)`, there is an `s x s` stochastic matrix
`t^lambda` such that for `mu`-a.e. `y` the colouring
`omega_y(aC) = j iff a^(-1) y in P_j` satisfies

```text
#{ w in S_lambda(v) : omega_y(w) = j } = D_lambda t^lambda_(omega_y(v), j)
for all v in V, all lambda, all j.                                     (VP5)
```

So `omega_y` is an equitable partition of the building vertex set for every
Hecke relation, its law is `L`-invariant, and `L^infinity(Y) rtimes A` contains the
coordinate crossed product of this random colouring.  A leak exists iff
`d_C(N) > d_A(N)`, and for ergodic `mu` iff `s >= 2`.

**Consequences for the frontier.**
- A class-killing obstruction (VP3): no construction whose `C`-central
  element comes from a real-place (Archimedean) homogeneous or Gaussian
  system can refute `(PTS1)`.  Every refuter is `2`-adic building dynamics.
- A decomposition of the refutation side of `(PTS1)` into two gates that can
  fail independently (VP2, VP5): (a) Connes embeddability of the coordinate
  crossed products of `L`-invariant random vertex subsets of the `SL_3(Q_2)`
  building (commutative class), with its finite-`d_C` sub-gate the random
  equitable Hecke colourings, which contains every `(SH1)`; (b) genuinely
  noncommutative `L`-covariant unitary vertex fields (VP1), which are needed
  only if (a) fails for every invariant random subset.
- A proof of `(PTS1)` must show that **no** `L`-invariant random vertex subset
  of the building has Connes-embeddable crossed product, and at the same time
  exclude every noncommutative vertex field.

**Not claimed.**  Nothing here decides any Connes embeddability.  Whether every
`L`-invariant random finite equitable Hecke colouring is a factor of a
lattice-quotient colouring (a building analogue of Leighton's
common-covering theorem, which would collapse the finite-`d_C` commutative
gate onto `(SH1)` over all cocompact `Lambda'`) is open and not asserted.  The
converse separation (that `L^infinity(L/Lambda')` is not an `A`-factor of a
Bernoulli coset shift) would follow from the absence of `K`-spherical discrete
series in `l^2(V)`-type representations, via Macdonald's spherical Plancherel
theorem, but is not proved or imported here.
