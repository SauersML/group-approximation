---
rg: 2
id: homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse
kind: claim
title: Connes embeddability of the compact homogeneous-quotient crossed product refutes relative-commutant collapse for the arithmetic pair
distinct_from:
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that firewall uses the generalized Bernoulli shift over the countable coset space A/C, whose lamp coordinates are weakly mixing for C; this one uses the compact homogeneous quotient SL_n(Q_p)/Lambda' of a cocompact lattice, on which C acts profinitely, so the C-central leak is a K-orbit indicator and the crossed product restricted to C is an amplified profinite algebra.
  no-spherical-leak-in-matrix-ultraproducts: that is the collapse statement in spherical-component form; this is a concrete crossed product whose Connes embeddability would exhibit the excluded spherical leak, realized by Hecke eigenfunctions on a finite quotient of the Bruhat--Tits building.
  arithmetic-pair-group-factor-ultrapower-has-no-leak: that proves the leak is absent inside the ultrapower of the group factor L(A) itself; this exhibits the leak inside an explicit crossed product by A, and says the question is whether THAT algebra has matrix microstates.
  sl3-dyadic-building-vertex-action-is-sofic: that asks for soficity of the countable type-zero vertex action of A; this uses the compact quotient of the same p-adic group by a lattice and asks for Connes embeddability of a crossed product, with no soficity of any action.
---

**THEOREM (established here; proof in
`homogeneous-quotient-commutant-obstruction-proof`).**  Fix `n >= 2` and a
prime `p`, and put

```text
A = SL_n(Z[1/p]),  C = SL_n(Z),  L = SL_n(Q_p),  K = SL_n(Z_p).
```

Let `Lambda' <= L` be a torsion-free cocompact lattice, `X = L/Lambda'`
with the `L`-invariant probability measure `mu`, and

```text
r = |K \ L / Lambda'|  (= covolume of Lambda' in units of Haar(K)),   (HQ0)
```

which is finite, equals the number of `K`-orbits on `X`, and is multiplied by
the index on passing to a finite-index subgroup of `Lambda'`; assume
`r >= 2`.  Cocompact lattices exist in `SL_n(Q_p)` for every `n` and `p`
(arithmetic ones from a definite hermitian form over an imaginary quadratic
field in which `p` splits; for `n = 2` the unit groups of definite
quaternion orders split at `p`), and Selberg's lemma gives torsion-free
finite-index subgroups.  `A` acts on `X` through the dense inclusion
`A < L`.  Let

```text
M = L^infinity(X) rtimes A,   pi(a) = u_a.                            (HQ1)
```

Then:

1. **(regular trace, factor)** `tau(u_a) = 0` for `a != e`, so `pi` is a
   regular-trace representation of `A` into `M`; the action is ergodic and
   essentially free, so `M` is a II_1 factor.
2. **(the leak)** `L^infinity(X)^C = L^infinity(X)^K` is the `r`-dimensional
   algebra of functions constant on `K`-orbits.  Hence for one `K`-orbit
   `P subset X` (`mu(P) = 1/r`) the symmetry

   ```text
   U = 1 - 2 . 1_P   in  pi(C)' cap M                                 (HQ2)
   ```

   is a nonconstant unitary commuting with every `pi(c)`, `c in C`.
3. **(it is moved, non-scalarly)** For every subset `S subset A` with
   `<C, S> = A` there is `s in S` such that the unitary
   `W_s = U pi(s) U^* pi(s)^* = U . (U o s^-1) in L^infinity(X)` is not a
   scalar; equivalently

   ```text
   |tau(U pi(s) U^* pi(s)^*)| < 1.                                    (HQ3)
   ```

   For `n = 3` one may take `S = {h}`, `h = diag(p, 1, 1/p)`; for `n = 2`,
   `S = {e_21(1/p)}`.
4. **(consequence)** If `M` is Connes embeddable, then for any trace-preserving
   embedding `theta: M -> prod_U M_(d_k)` the map `theta o pi` is a
   regular-trace representation of `A` into a tracial matrix ultraproduct
   and `theta(U)` is a unitary in `(theta pi)(C)'` that is **not** in
   `(theta pi)(A)'`.  This refutes, for the pair `C < A`:
   - `sl3-pair-relative-commutant-route` (`(RC3)`, `n = 3`, `p = 2`),
     `sl3-p3-pair-relative-commutant-collapse` (`n = 3`, `p = 3`) and
     `relative-commutant-collapse-for-sl2-pair` (`n = 2`, `p = 2`);
   - `no-spherical-leak-in-matrix-ultraproducts` (stated for all `n`, `p`),
     since `||E_(pi(A)' cap M)(k)||_2 = 1` for a unitary `k` forces
     `k in pi(A)' cap M`;
   - the quantitative transfer `projective-trace-square-transfer-for-sl3-pair`
     `(PTS1)`: lifting `theta(U)` and `theta pi` to unitaries `U_k in U(d_k)`
     and an almost-representation `rho_k` of the fixed finite presentation of
     `A` gives `sum_(c in S_C) (1 - |tr[U_k, rho_k(c)]|^2) -> 0` while
     `1 - |tr[U_k, rho_k(h)]|^2 -> 1 - |tau(W_h)|^2 > 0`, so no constant `K`
     and modulus `eta(delta) -> 0` can satisfy `(PTS1)`.
5. **(structure of `M`)**  The restriction to `C` is an amplified profinite
   crossed product:

   ```text
   L^infinity(X) rtimes C  =  (+)_(j=1)^r  L^infinity(K) rtimes C,     (HQ4)
   ```

   each summand being the crossed product of the profinite completion
   `K` of `C` by left translation, i.e. the increasing union of
   `M_([K:K_m]) (x) L(C cap K_m)` over the principal congruence subgroups
   `K_m`; it is Connes embeddable.  For `n = 2`, Serre's amalgam
   `A = C *_D C'` with `C' = g C g^-1`, `g = diag(p, 1)`, and
   `D = C cap C' = {[[a,b],[c,d]] in SL_2(Z) : p | b}` (index `p+1`) has
   `C'` acting on `X` through the adjacent maximal compact `g K g^-1`, so

   ```text
   M = N_1 *_B N_2,   N_1 = L^infinity(X) rtimes C,  N_2 = L^infinity(X) rtimes C',
   B = L^infinity(X) rtimes D,                                          (HQ5)
   ```

   an amalgamated free product of two Connes-embeddable profinite algebras
   over a common finite-index (non-amenable) subalgebra.  For every `n`,
   `dense-s-arithmetic-translation-algebra-is-amplified-profinite` shows
   `M (x) B(l^2 Lambda')  =  (N (x) B(l^2)) rtimes Lambda'` with
   `N = L^infinity(K) rtimes C`: `M` is a II_1 corner of the crossed product
   of a Connes-embeddable II_infinity factor by the residually finite lattice
   `Lambda'`.

**What the leak is.**  The nonconstant `C`-invariant functions on `X` are
the `K`-spherical vectors of `L^2(X) (-) C`, i.e. Hecke eigenfunctions on
the finite quotient `K \ L / Lambda'` of the Bruhat--Tits building (a finite
`(p+1)`-regular Ramanujan graph for `n = 2`, a Ramanujan-type complex for
`n = 3`), lying in mixing (Howe--Moore) `L`-subrepresentations.  This is
exactly the `c_0` spherical component that
`no-spherical-leak-in-matrix-ultraproducts` must exclude, produced here by
an explicit p.m.p. action rather than sought abstractly inside a
commutant.

**Why this is a sharper firewall than the coset Bernoulli one.**  In
`coset-bernoulli-ce-refutes-relative-commutant-collapse` the leak lives in a
lamp algebra that is weakly mixing for `C` and the CE question is
`coset-wreath-is-hyperlinear`, a wreath group with no known matrix models.
Here every compact-subgroup piece of `A` acts profinitely, so the only
non-finite ingredient is the gluing by the single element `h` (resp. the
amalgamation over `D = C cap g C g^-1`); `M` restricted to `C` already has explicit
congruence microstates.  Conversely, any proof of the collapse must show
that this explicit algebra `M` has **no** matrix microstates: relative
commutant collapse for the arithmetic pair is at least as strong as
non-Connes-embeddability of `(HQ1)`.

**Scope.**  The theorem uses only: density of `C` in `K` and of `A` in `L`
(strong approximation), transitivity of `L` on `X`, torsion-freeness and
cocompactness of `Lambda'`, and that `L` has no proper open subgroup of
finite index.  Perfectness of `A` and the congruence subgroup property are
**not** used, which is why the `n = 2` pair is covered.  Nothing here decides
whether `M` is Connes embeddable; the two-sided open claims are
`sl3-homogeneous-quotient-crossed-product-is-connes-embeddable` and
`sl2-homogeneous-quotient-crossed-product-is-connes-embeddable`.
