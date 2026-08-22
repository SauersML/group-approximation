# Finite-support central corners collapse to finite-normal twisted sectors

Let `q=q*=q^2` lie in the center of the algebraic group algebra
`C[Gamma]`.  This note proves that `q` is already supported on a finite
normal subgroup and records the resulting Clifford decomposition.

## 1. The support generates a finitely generated normal FC-group

Write `S=supp(q)`.  Centrality says that `S` is invariant under conjugation
by `Gamma`.  Since `S` is finite, every element of `S` has a finite
`Gamma`-conjugacy class.  Hence

```text
H=<S>
```

is a finitely generated normal FC-subgroup of `Gamma`: it is normal because
`S` is conjugation invariant, and each of its finitely many generators has
finite conjugacy class.  Here we use that the FC-center is a subgroup: the
conjugacy class of a product (or inverse) is contained in the product (or
inverse) of the corresponding finite conjugacy classes.

For a finitely generated FC-group `H`, its torsion radical `K` is finite and
characteristic, and

```text
H/K ~= Z^r.                                            (1)
```

Indeed the center has finite index in `H`, so Schur's theorem makes the
commutator subgroup `H'` finite.  The image of every torsion element in the
finitely generated abelian group `H_ab` lies in its finite torsion subgroup,
and each fibre over that subgroup has at most `|H'|` elements.  Hence the
torsion set `K` is finite.  In an FC-group it is a characteristic subgroup;
it contains `H'`, and the quotient is finitely generated, abelian and
torsion-free, proving (1).  Since `H` is normal in `Gamma` and `K` is
characteristic in `H`, `K` is finite normal in `Gamma`.

## 2. Central idempotents have no nonzero Laurent degree

We prove that every central idempotent of `C[H]` belongs to `C[K]`.
Decompose the finite-dimensional semisimple algebra `C[K]` into its
irreducible blocks.  Conjugation by `H` permutes these blocks.  Fix one
orbit `O`, choose `rho in O`, and let `H_rho` be the inertia subgroup.
The standard full-corner/Morita reduction gives

```text
e_O C[H] e_O ~= M_|O|( z_rho C[H_rho] z_rho ).        (2)
```

Because `rho` is invariant under `H_rho`, the homogeneous fibres over
`H_rho/K` are rank-one bimodules over `M_d(C)`.  Schur's lemma therefore
gives

```text
z_rho C[H_rho] z_rho
 ~= M_d(C) tensor C_omega[H_rho/K].                    (3)
```

Here `H_rho/K` is a finite-index subgroup of `H/K`, hence a free abelian
lattice `A`.  Let

```text
b(x,y)=omega(x,y) omega(y,x)^(-1),
R={x in A : b(x,y)=1 for every y in A}.
```

Coefficient comparison against every twisted monomial shows that a central
element is supported exactly on `R`; hence
`Z(C_omega[A])=C_(omega|R)[R]`.  On `R` the cocycle is symmetric.  A
symmetric scalar cocycle on a free abelian group is a coboundary, so this
center is an ordinary Laurent group algebra after rescaling its monomial
basis.  It is an integral domain and its only idempotents are `0` and `1`.
(The FC hypothesis also makes the commutation bicharacter finite-valued,
but that stronger fact is not needed for this idempotent argument.)

Thus a central idempotent on the orbit block (2) is either zero or the
whole orbit identity `e_O`.  Applying this to every orbit shows

```text
q=sum_(selected O) e_O in C[K].                        (4)
```

This also covers `r=0`; then `H=K` is finite from the outset.

## 3. Decomposition in the ambient group

Now let `Gamma` act on `Irr(K)`.  Equation (4), together with centrality in
`C[Gamma]`, says that the selected set of irreducibles is a union of
`Gamma`-orbits.  For one orbit `O`, choose `rho in O` and write
`Gamma_rho` for its inertia subgroup.  The same matrix-corner reduction as
in (2) gives

```text
e_O C*(Gamma) e_O
 ~= M_|O|( z_rho C*(Gamma_rho) z_rho ).                (5)
```

The same invariant-type Clifford calculation, now applied to
`K normal Gamma_rho`, identifies the latter corner as

```text
M_d(C) tensor C*_(omega_rho)(Gamma_rho/K),             (6)
```

where `omega_rho` can be chosen finite-valued.  Distinct cosets and
distinct finite-group matrix coefficients are orthogonal for the canonical
group trace, so (5)--(6) also identify the normalized corner trace with
the normalized matrix trace tensor the twisted regular trace.

For completeness, finite phase follows directly from the intertwiner
factor set.  If `T_xT_y=alpha(x,y)rho(k(x,y))T_(xy)`, determinants show that
`alpha(x,y)^d` differs from a scalar coboundary by the finite-valued term
`det rho(k(x,y))^(-1)`.  Thus the cohomology class of `alpha` is torsion and
has a root-of-unity-valued representative.  The passage to full universal
completions loses no representations: a representation of a central
algebraic corner extends to the ambient algebra by `a |-> pi(e_O a)` (and
similarly for `z_rho`).

Summing over the selected orbits proves the announced finite direct-sum
decomposition.

## 4. Consequence for the common-corner programme

This removes a possible loophole in the finite-normal Clifford fence.
Starting from an arbitrary finite Fourier polynomial, rather than naming a
finite subgroup beforehand, does not create an infinite central selector.
If the polynomial is a central projection, its support manufactures a
finite normal subgroup automatically.  Each selected sector is then only a
matrix amplification of a finite-phase twisted group algebra.

Thus a successful algebraic central-corner trace promotion must already
solve the twisted-group-factor problem on one summand.  To escape that gate,
a common-corner compiler must use a noncentral compression, an analytically
defined spectral projection not lying in `C[Gamma]`, or a genuinely mixed
holonomy mechanism.
