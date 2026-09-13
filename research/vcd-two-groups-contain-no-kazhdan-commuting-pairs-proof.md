---
rg: 2
id: vcd-two-groups-contain-no-kazhdan-commuting-pairs-proof
kind: route
title: Product with Z raises cohomological dimension by one, and cohomological dimension one means free
target: vcd-two-groups-contain-no-kazhdan-commuting-pairs
requires: [titz-witzel-simple-kazhdan-cat0-lattices-exist, radu-bmw-lattice-embeds-in-titz-witzel-kernel]
---

All cohomological dimensions are over `Z`. The two required claims are used only for the
instances. The theorem itself uses the four standard facts below.

## Standard facts

- **(F1) Monotonicity.** `H <= G` implies `cd H <= cd G`. `ZG` is free as a `ZH`-module, so a
  projective resolution of `Z` over `ZG` is also one over `ZH`.
- **(F2) Swan's theorem** (R. G. Swan, *Groups of cohomological dimension one*, J. Algebra 12
  (1969); Stallings 1968 for finitely generated groups). A group with `cd <= 1` is free.
- **(F3) Torsion.** A group of finite cohomological dimension is torsion-free, since
  `cd(Z/p) = infinity`. A nontrivial group has `cd >= 1`.
- **(F4) Kazhdan groups.** They have finite abelianization. A nontrivial free group maps onto
  `Z`, so a free Kazhdan group is trivial. A finite-index subgroup of a Kazhdan group is Kazhdan.

## Lemma (product with Z)

If `cd A = d < infinity`, then `cd(A x Z) >= d + 1`.

*Proof.* Choose an `A`-module `M` with `H^d(A,M) != 0`. Write `Z = <t>`, and put
`W = directSum_(k in Z) M`, with `A` acting coordinatewise and `t` shifting coordinates. This is
a module over `A x Z`, and `t - 1` and the sum map `Sigma : W -> M` are `A`-module maps. The
sequence

```text
W --(t-1)--> W --Sigma--> M --> 0
```

is exact. A finitely supported sequence with total sum zero is `(t-1)` of a finitely supported
sequence.

Since `H^(d+1)(A,-) = 0`, the functor `H^d(A,-)` is right exact. Splitting the sequence at
`ker Sigma = im(t-1)` gives an exact sequence

```text
H^d(A,W) --(t-1)_*--> H^d(A,W) --> H^d(A,M) --> 0.
```

So `coker (t-1)_* ~= H^d(A,M) != 0`.

Now use the Lyndon--Hochschild--Serre spectral sequence of `A normal A x Z`:
`E_2^(p,q) = H^p(Z, H^q(A,W))`. Since `t` centralizes `A`, the quotient `Z` acts on
`H^q(A,W)` through the module map `t : W -> W`. As `cd Z = 1`, only the columns `p = 0, 1` are
nonzero, so the sequence degenerates at `E_2`. In total degree `d + 1` the `p = 0` term is
`H^0(Z, H^(d+1)(A,W)) = 0`. Hence

```text
H^(d+1)(A x Z, W) ~= H^1(Z, H^d(A,W)) = coker (t-1)_* != 0.
```

So `cd(A x Z) >= d + 1`. `QED`

## Proof of (CD1)

Let `A_0 = A cap G_0` and `B_0 = B cap G_0`. They have finite index in `A` and `B`, commute,
and meet trivially.
- `A_0` is infinite, so it contains an element `a != 1`. By (F3) `a` has infinite order, so
  `<B_0, a> ~= B_0 x Z`.
- By (F1), `cd(B_0 x Z) <= cd G_0 <= 2`, so `cd B_0 <= 2 < infinity`. The lemma gives
  `cd B_0 <= 1`.
- By (F2), `B_0` is free, so `B` is virtually free.

## Proof of (CD2)

Suppose `B` is infinite, and let `A_0, B_0` be as above.
- `B_0` is infinite, hence nontrivial. Applying the argument above with the roles of `A` and
  `B` exchanged, `A_0` is free.
- `A_0` has finite index in the Kazhdan group `A`, so it is Kazhdan and infinite. This
  contradicts (F4).

So `B` is finite.

## Proof of (CD3)

- **No `Z^3`.** If `Z^3 <= G`, then `Z^3 cap G_0` has finite index in `Z^3`, so it is again
  `~= Z^3`. Take `A = Z`, `B = Z^2` inside it. (CD1) makes `Z^2` virtually free, which it is
  not: its finite-index subgroups are `~= Z^2`.
- **Bounded finite subgroups.** Let `F <= G` be finite. By (F3), `F cap G_0 = 1`, so
  `f |-> f G_0` is injective on `F`, and `|F| <= [G:G_0]`.
- **Wreath products.** Let `L != 1`, `X` infinite, and suppose `L wr_X H` embeds in `G`. The
  base contains `L^n` for every `n`.
  - If `L` has an element of infinite order, it contains `Z^3`.
  - Otherwise `L` has an element of prime order `p`, and `(Z/p)^n` has order `p^n`, which is
    unbounded.

  Either way the previous two points are contradicted.

## Instances

- **Titz Mite--Witzel.** `titz-witzel-simple-kazhdan-cat0-lattices-exist` records that each
  `Gamma_i^q` acts freely and cocompactly on the contractible two-dimensional complex `X_i^q`.
  - Cell stabilizers are finite by properness and trivial by torsion-freeness. So the cellular
    chain complex of `X_i^q` is a free resolution of `Z` of length two, and `cd Gamma_i^q <= 2`.
  - The residuals are subgroups, so (F1) applies to them.
  - For `barGamma_1^2`, take `G_0 = Gamma_1^2`, of index two.
- **Radu's lattice.** `radu-bmw-lattice-embeds-in-titz-witzel-kernel` gives `pi_1(S_R)` of
  index four in `Gamma_R`. It is the fundamental group of a finite square complex with universal
  cover `T_3 x T_3`, which is contractible and two-dimensional, so `cd pi_1(S_R) <= 2`.

## Consequences for the certificates

- **Expander-matching criterion.** The hypotheses `[Gamma,J] = 1` and `Gamma cap J = 1`, with
  `Gamma` infinite and Kazhdan, give `J` finite by (CD2). In the formalized `CompressionSetup`
  the commuting subgroup is the compressed copy `q Gamma q^-1`. It is isomorphic to `Gamma`, so
  it is infinite and Kazhdan, and the same conclusion holds.
- **Kun--Thom wreath products.** The infinite-index argument for infranormal, non-normal
  subgroups is in the claim body. The wreath product then has an infinite lamp set and is
  excluded by (CD3).
- **Fournier--Facio.** The simple factor `S` is infinite and torsion-free, so it contains `Z`.
  Hence `S^(Z)` contains `Z^3`, and the configuration is excluded by (CD3).
