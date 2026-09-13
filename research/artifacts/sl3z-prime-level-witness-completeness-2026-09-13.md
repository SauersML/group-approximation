# At prime levels the invariant-vector witnesses of SL_3(Z) are complete

Lane `ex-sl3z-purely-matricial`, 2026-09-13.  Unreviewed.

Notation.  `p` is an odd prime.  `B_2` is the block `SL_2(F_p)` in coordinates
`1,2`.  `Omega = Sym^2(SL_2(F_p)) = PSL_2(F_p) <= SL_3(F_p)` is the principal
`SL_2`.  For `t in F_p^x` put `d_t = diag(t,1,1)` and `Omega^(t) = d_t Omega d_t^(-1)`.
Also `e_ij = I + E_ij`, `U_row = <e_12, e_13>` (unipotent radical of the line
stabilizer `P_(1,2)`), and `U_col = <e_13, e_23>`.

`Omega^(t)` depends, up to `SL_3(F_p)`-conjugacy, only on the class of `t` in
`C_p = F_p^x / (F_p^x)^3`.  Indeed
`d_(s^3) = (s I) diag(s^2, s^(-1), s^(-1))` lies in `Z . SL_3(F_p)`.
`C_p` has order 3 if `p == 1 mod 3` and order 1 otherwise.

## Theorem E

Every nontrivial irreducible representation `rho` of `SL_3(F_p)` has a nonzero
vector fixed by `B_2` or by some `Omega^(t)`.  More precisely:

1. **(non-cuspidal)** If `rho` is not cuspidal, then `rho^(B_2) != 0`.
2. **(cuspidal, irreducible restriction)** If `rho = pi|_(SL_3)` for a cuspidal
   `pi` of `GL_3(F_p)`, then `dim rho^(Omega^(t)) = 2` for every `t`.
3. **(cuspidal, split restriction)** If `pi|_(SL_3) = rho_1 (+) rho_2 (+) rho_3`
   (possible only for `p == 1 mod 3`, when `pi = pi (x) (chi o det)` for a cubic
   `chi`), then `sum_(c in C_p) dim rho_j^(Omega^(c)) = 2` for each `j`.  So
   each `rho_j` has `Omega^(c)`-fixed vectors for at least one class `c`, and
   misses at most two classes.

### Proof of 1

A non-cuspidal irreducible `rho` has a nonzero Jacquet module for `P_(1,2)` or
for `P_(2,1)`.  The transpose-inverse automorphism, followed by conjugation
with the antidiagonal permutation matrix, exchanges the two parabolics and
maps `B_2` to a conjugate of `B_2`.  So assume `W = rho^(U_row) != 0`.  `W` is
a representation of the Levi subgroup, which contains `SL_2(F_p)` in
coordinates `2,3`, and in particular `e_23`.

* *`e_23` acts trivially on `W`.*  The normal closure of a transvection in
  `SL_2(F_p)` is `SL_2(F_p)`, so the coordinate-`(2,3)` `SL_2` fixes `W`
  pointwise.  That group is conjugate to `B_2`.
* *`e_23` acts on some `v in W` by a nontrivial character `psi`.*  Then `v` is an
  eigenvector of `U_col`: `e_13` fixes `v` (it lies in `U_row`), and `e_23` acts
  by `psi`.  `B_2` acts on the characters of `U_col` through the column action
  on `(u_13, u_23)`.  The stabilizer of the character `u -> psi(u_23)` is
  `N = {e_12(b)}`, and `N <= U_row` fixes `v`.  For cosets `gN != g'N` the
  translates `rho(g)v`, `rho(g')v` are `U_col`-eigenvectors with different
  characters, hence orthogonal.  So `sum_(g in B_2/N) rho(g) v` is nonzero and
  `B_2`-invariant.  This is Magee--de la Salle's Step 3 (arXiv:2312.03220v2,
  Section 2.4) in rank 3.

### Proof of 2 and 3

**Character values.**  A cuspidal `pi` of `GL_3(F_p)` is `+- R_T^theta` with
`T = F_(p^3)^x` anisotropic.  By the Deligne--Lusztig character formula,
`chi_pi(su) = 0` unless the semisimple part `s` is conjugate into `T`.  A
non-central `s` in `T` has no eigenvalue in `F_p`.  The Green function values
on unipotent classes are `(p-1)(p^2-1)`, `1-p` and `1` at types `(1,1,1)`,
`(2,1)` and `(3)`.

Every nonidentity element of `Omega` is a regular unipotent (`p^2 - 1` of
them) or has eigenvalues `(a^2, 1, a^(-2))`, which is semisimple, non-central
and has eigenvalue 1.  Hence

```text
dim pi|_(SL_3)^(Omega) = [ (p-1)(p^2-1) + (p^2-1) * 1 ] / ( p(p^2-1)/2 ) = 2.
```

This is Lemma 1 of `deligne-sl3-representations-have-principal-sl2-invariants`.
The count uses only the values above, so it holds for every cuspidal `pi`,
including the cubic-twist-invariant ones.  `pi` extends to `GL_3`, so it is
stable under `Ad(d_t)`, and `dim pi^(Omega^(t)) = 2` for all `t`.  That proves 2.

For 3, `GL_3(F_p)` permutes the constituents by conjugation.  `Z . SL_3(F_p)`
acts trivially, and by Clifford theory the quotient `GL_3 / (Z . SL_3) = C_p`
acts simply transitively on `{rho_1, rho_2, rho_3}`.  So `rho_j o Ad(d_t)` is
`rho_(sigma_t(j))`, and

```text
sum_(c in C_p) dim rho_j^(Omega^(c)) = sum_(c) dim (rho_j o Ad d_c)^(Omega)
                                     = sum_(j') dim rho_(j')^(Omega) = 2.     QED
```

## Integral witnesses

For `m >= 1` put `H_m = d_m Sym^2(SL_2(Z)) d_m^(-1) cap SL_3(Z)`.  It contains
`d_m Sym^2(Gamma(m)) d_m^(-1)`: off-diagonal entries of `Sym^2(g)` are `== 0 mod m`
when `g == I mod m`.  So `H_m` is nonamenable and finitely generated.

For `p` not dividing `2m` its reduction is exactly `Omega^(m mod p)`:

- `Gamma(m) -> SL_2(F_p)` is onto;
- elements of `H_m` are `d_m Sym^2(g) d_m^(-1)` with `g` `p`-integral.

`H_1 = Sym^2(SL_2(Z))` is the principal witness of the earlier lane.

## Corollary F: prime-level strong convergence runs along cubic Chebotarev primes

**Corollary F.**  Let `rho_i` be nontrivial irreducible representations of
`SL_3(F_(p_i))`, pulled back to `SL_3(Z)`, with `p_i -> infinity`, and suppose
`rho_i -> lambda_(SL_3(Z))` strongly.  Then for every `M >= 1` and all large `i`:

- (a) `p_i == 1 mod 3`;
- (b) `rho_i` is a constituent of the restriction of a cubic-twist-invariant
  cuspidal representation of `GL_3(F_(p_i))`;
- (c) every integer `1 <= m <= M` is a cube mod `p_i`.

Equivalently, `p_i` eventually splits completely in
`Q(zeta_3, 2^(1/3), ..., M^(1/3))` for each `M`.

*Proof.*  Fix `M`.  Let

```text
y_M = diag( L_(B_2(Z))/4 ,  L_(H_m)/|S_m|  (1 <= m <= M^2) )
```

in `M_(M^2+1)(C[SL_3(Z)])`, where `L_H` is the sum of a symmetric generating set
`S_H` of `H`.  Then `||lambda(y_M)|| < 1`, by Kesten and because `lambda` restricted
to `H` is a multiple of `lambda_H`.  But `||rho(y_M)|| = 1` whenever `rho` fixes a
vector of `B_2(Z)` or of some `H_m`.  Strong convergence holds with matrix
coefficients, so for large `i` the representation `rho_i` fixes no such vector.

- By Theorem E.1, `rho_i` is cuspidal.
- By Theorem E.2 with `H_1`, the restriction is split, so `p_i == 1 mod 3`.

Let `E_i` be the set of classes `c` with `rho_i^(Omega^(c)) = 0`.  By Theorem E.3,
`E_i` is not all of `C_(p_i)`, and every class of `m <= M^2` lies in `E_i` (take
`p_i > 2M^2`).  If some `m <= M` were a non-cube mod `p_i`, the classes of `1`,
`m` and `m^2` would be `0`, `c` and `2c`, which is all of `C_(p_i)`.  QED

## Census check at `p = 7` (exact computation, MSI, 2026-09-13)

Program `experiments/sl3z-purely-matricial/dist3.c` extends the earlier
`experiments/mf-kazhdan-cstar/dist.c` to the conjugates `Omega^(t)`,
`t = 1, 2, 3`.  The cube classes mod 7 are `{1,6}`, `{2,5}`, `{3,4}`.  For a
subgroup `H` it counts the irreducible `chi` with `<Ind_H^G 1, chi> != 0`, i.e.
with `H`-fixed vectors.  This is the rank of the class-function convolution
matrix modulo `2^61 - 1` and modulo `10^9 + 7`; both agree in every row.  It also
prints `sum chi(1)^2` over the missing `chi`.  `SL_3(F_7)` has `K = 64`
irreducibles.

| subgroup | irreducibles with fixed vectors | `sum chi(1)^2` over missing |
|---|---|---|
| `Omega^(1)` (order 168) | 58 | `43362 = 4*96^2 + 2*57^2` |
| `Omega^(2)` | 58 | `43362` |
| `Omega^(3)` | 58 | `43362` |
| block `SL_2` (order 336) | 40 | `1548288` |
| block and `Omega^(1)` | 60 | `36864 = 4*96^2` |
| block and `Omega^(1)`, `Omega^(2)`, `Omega^(3)` | **64** | **`0`** |

The `57`s are odd degenerate principal series.  They are non-cuspidal, so they
have block fixed vectors (Theorem E.1).  The four `96`s missing from the block
and `Omega^(1)` reproduce the earlier census.  Adding the other two cube classes
catches every irreducible, as Theorem E predicts.

**Scope.**

- *Prime levels only.*  Mixed levels escape every witness here
  (`sl3z-has-no-invariant-vector-witnesses` uses tensor products at two primes).
  Prime-power levels already escape both the block and the principal `SL_2` at
  `Z/9`.
- *What survives at prime levels.*  The surviving candidates lie on a set of
  primes of density `1/[Q(zeta_3, 2^(1/3), ..., M^(1/3)) : Q] -> 0`.  Their
  principal fixed vectors migrate to witnesses `H_m` with `m` at least the least
  non-cube mod `p_i`, which tends to infinity.  Corollary F constrains such a
  sequence but does not refute one: the witness element changes with `i`.
