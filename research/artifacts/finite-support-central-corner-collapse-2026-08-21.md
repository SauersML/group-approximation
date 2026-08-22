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
finite conjugacy class.

For a finitely generated FC-group `H`, its torsion radical `K` is finite and
characteristic, and

```text
H/K ~= Z^r.                                            (1)
```

Indeed the center has finite index in `H`; the commutator subgroup is
finite, the torsion subgroup is finite, and the torsion-free quotient is
finitely generated abelian.  Since `H` is normal in `Gamma` and `K` is
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
lattice.  Since `H` is FC, all commutators lie in the finite group `K`; the
commutation bicharacter of `omega` consequently has finite image.  The
center of the twisted Laurent algebra in (3) is the Laurent group algebra
of the radical sublattice of that bicharacter.  It is an integral domain,
so its only idempotents are `0` and `1`.

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
