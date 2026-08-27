# Exact first-homology torsion in five square projective charts

Date: 2026-08-12

## 1. Outcome

The integral first-homology torsion of the five computed square-level
projective cellular complexes is now determined exactly:

```text
Tor H_1(X_9;Z)   = 0,
Tor H_1(X_25;Z)  ~= C_25,
Tor H_1(X_49;Z)  ~= C_49,
Tor H_1(X_121;Z) ~= C_831875 = C_(5^4 11^3),
Tor H_1(X_169;Z) ~= C_13.                              (SHT1)
```

These are not inferred from a few modular dimensions.  Their orders are
exact row-lattice saturation indices, and the modular rank drop at each
prime divisor is one, proving that every primary part is cyclic.

The result matters directly for TRUE because these groups classify the
finite arithmetic directions missing when an ambient dual lift is reduced
only by literal coboundary rows.  At level `169` there is exactly one such
direction, of order `13`; it is the explicit vector `v_13` certified in
`TRUE_SQUARE_LEVEL_INTEGRAL_PACKET_INDICES.md`.

## 2. General theorem

Let

```text
C_2 --d_2--> C_1 --d_1--> C_0                         (SHT2)
```

be a chain complex of finitely generated free abelian groups.  Put
`R=im(d_2) subset C_1` and let `R_sat=(R tensor Q) intersect C_1`.

**Theorem 1.**  There are canonical isomorphisms

```text
R_sat/R ~= Tor(coker(d_2)) ~= Tor(H_1).                (SHT3)
```

If `r=rank_Q(d_2)`, then

```text
|Tor(H_1)|=[R_sat:R],                                  (SHT4)
```

and for every prime `ell`,

```text
minimum number of generators of Tor(H_1)_(ell)
 = r-rank_(F_ell)(d_2 mod ell).                        (SHT5)
```

### Proof

The torsion subgroup of `C_1/R` consists exactly of classes represented by
vectors `x` such that `m x in R` for some nonzero integer `m`.  These are
precisely the classes in `R_sat/R`, proving the first isomorphism in
`(SHT3)`.

There is an exact sequence

```text
0 -> H_1=ker(d_1)/R -> C_1/R -> im(d_1) -> 0.          (SHT6)
```

The last term is a subgroup of the free group `C_0`, hence is free.  It has
no torsion, so `(SHT6)` proves the second isomorphism in `(SHT3)`.  Equation
`(SHT4)` follows by taking orders.

Write the nonzero Smith invariants of `d_2` as `s_1|...|s_r`.  Reduction
modulo `ell` loses one rank for each `s_i` divisible by `ell`.  The same
number is the number of cyclic factors in the `ell`-primary part of
`Tor(coker(d_2))`, proving `(SHT5)`.  End proof.

This proof also shows why an exact order plus modular rank drops determines
the invariant factors in `(SHT1)`: each relevant primary part needs only one
generator, so it is cyclic; primary cyclic groups of coprime orders combine
to one cyclic group.

## 3. Exact calculations

For each level, sparse unit elimination and the determinant of the tiny
residual column HNF compute `[R_sat:R]`.  No full Smith transformation of
the large boundary matrix is constructed.

### Level 9

```text
rank_Q(d_2)=6,
[R_sat:R]=1.                                          (SHT7)
```

Thus `H_1` is torsion-free at the first square level.  In particular, a
formula assigning the factor `C_(p^2)` at every level `p^2` already fails
at `p=3`.

### Level 25

```text
rank_Q(d_2)=56,
[R_sat:R]=25=5^2,
rank_(F_5)(d_2)=55.                                   (SHT8)
```

The `5`-primary part has order `5^2` and one generator, hence is `C_25`.

### Level 49

```text
rank_Q(d_2)=218,
[R_sat:R]=49=7^2,
rank_(F_7)(d_2)=217.                                  (SHT9)
```

The `7`-primary part has order `7^2` and one generator, hence is `C_49`.

### Level 121

```text
rank_Q(d_2)=1308,
[R_sat:R]=831875=5^4 11^3,
rank_(F_5)(d_2)=rank_(F_11)(d_2)=1307.                (SHT10)
```

Both primary parts have one generator.  Hence they are `C_(5^4)` and
`C_(11^3)`, whose direct sum is cyclic of order `831875`.

The extra prime `5` is important: square level `11^2` does not have torsion
supported only at its level prime.  Any family theorem must account for
small stabilizer primes as well as the congruence prime.

### Level 169

```text
rank_Q(d_2)=2530,
[R_sat:R]=13,
rank_(F_13)(d_2)=2529.                                (SHT11)
```

Thus the torsion is exactly `C_13`.  The vector `v_13` already extracted
from the unique modular dependence generates the corresponding saturated
annihilator quotient.

## 4. Consequence for the dual decoder

Let `K=ker(d_2)` in the ambient degree-two chain lattice.  The affine space
of integral extensions of a fixed functional on `K` is a coset of

```text
Ann_Z(K)=Sat(Row_Z(d_2^T)).                            (SHT12)
```

The quotient of `(SHT12)` by raw coboundary rows is `Ext^1(H_1,Z)`, which
has the same invariant factors as `(SHT1)`.  Therefore:

1. at level `9`, raw coboundary rows are already saturated;
2. at level `25`, a complete raw-row reducer needs one order-`25` direction;
3. at level `49`, it needs one order-`49` direction;
4. at level `121`, it needs one order-`831875` direction, with distinct
   `5`- and `11`-primary depths; and
5. at level `169`, it needs only the one explicit order-`13` direction.

This explains exactly what arithmetic a quantitative dual-lift algorithm
must add.  It also separates two issues that were previously conflated:
qualitative dual lifts exist once the primal packet is unimodular, while
shortening a generic lift requires navigation of the finite group `(SHT1)`.

## 5. Certificates

```text
experiments/projective-cellular-n9-h1-torsion.json
SHA-256 184aa66d9bc54c9d9b3c48bd4421f7ef9cb3f354c2e1c37f3c82219578ef223b

experiments/projective-cellular-n25-h1-torsion.json
SHA-256 4e91404163ec85db2122514154428d2f570a97901ca15e8758c222d76ca3b779

experiments/projective-cellular-n49-h1-torsion.json
SHA-256 8996d3560e92cda9e4556cd2337ad75d989e7c9a49936e77b2ec71539794ab7c

experiments/projective-cellular-n121-h1-torsion.json
SHA-256 d82684f421eae9f595070f4068fd4300c9c0be0c31affebf7f9e138544115337

experiments/projective-cellular-n169-h1-torsion.json
SHA-256 b02eb2bbe0c937a70910f7164c1849c14c9325d984f92a2f97e0c46c591ddf04

experiments/sl3_projective_h1_torsion.py
```

Each certificate records the exact saturation-index elimination, its prime
factorization, every relevant modular rank, and the resulting invariant
factor.
