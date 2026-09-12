# Projective Lie-group truncations cannot evade the Kazhdan compression gap

Date: 2026-09-08.

The perturbative criterion in `deligne-sep8-first-order-tensor-threshold`
asks for matrix tuples at nonzero `t_n->0` whose projective operator
defects are `o(|t_n|)`. This note audits a natural possible source: compress
exact infinite-dimensional projective representations, allowing both the
parameter and the ambient representation to vary. That construction faces
a fixed positive unitarity gap before its relation defects are considered.

## The exact finite-dimensional parameters are only zero and one-half

Use the actual integral cocycle `b` of

```text
1 -> Z<z> -> E_infinity -> Sp_4(Z) -> 1.
```

An exact finite-dimensional `c_t=exp(2 pi i t b)` projective
representation lifts to a representation `rho` of `E_infinity` with
`rho(z)=exp(2 pi i t)I`. If `2t!=0`, its element `rho(z^2)` is nontrivial.
The group `E_infinity` is finitely generated: take lifts of finitely many
generators of the base and add `z`. Its linear image is residually finite
by Malcev, so a finite quotient detects `rho(z^2)`.

Let `M` be the order of the image of `z` in that quotient. Since its
square survives, `M>=3`; the quotient factors through `E_M`. It detects
`z_M^2`, contradicting the fact that Deligne's finite residual in `E_M`
is `2K_M`, where `K_M=<z_M>` is the cyclic covering kernel. Thus
`t in {0,1/2}` is necessary. This argument works equally for rational
and irrational parameters and does not require identifying the covering
cocycle with a primitive cohomology generator.

The trivial representation realizes zero. The residually finite
metaplectic cover supplies an exact nonzero negative central summand and
therefore realizes one-half, as established in
`deligne-sep7-norm-parameter-closed-subgroup`. Hence the exact scalar
parameter set is precisely `{0,1/2}`.

The finite-cover residual and Malcev inputs are recorded in
[Stover, *Residual finiteness and discrete subgroups of Lie groups*,
Theorems 1.2 and 1.5 and the paragraph following 1.5](https://arxiv.org/html/2407.07680v2).
The source calls the cyclic subgroup the center; here it is consistently
called the covering kernel because lifts of the base center also occur.

## One spectral gap works for every forbidden parameter

Fix a Kazhdan pair `(S,kappa)` for `Gamma=Sp_4(Z)`, reducing `kappa`
to at most one if necessary. For each `t notin {0,1/2}`, let `pi_t` be
any exact `c_t`-projective unitary representation on `H_t`.

The conjugation action on the Hilbert space of Hilbert-Schmidt operators,

```text
rho_t(g)T=pi_t(g)T pi_t(g)^*,
```

is an exact ordinary representation of the base. Its multiplier cancels
between the two factors. If `T!=0` were invariant, `T^*T` would be a
nonzero positive compact operator commuting with all `pi_t(g)`. A
positive nonzero eigenvalue has a nonzero finite-dimensional eigenspace,
which would be invariant under `pi_t`. That gives the forbidden exact
finite-dimensional projective representation at parameter `t`.

There are consequently no invariant vectors. For any nonzero finite-rank
projection `P` on `H_t`, property (T) gives

```text
max_(s in S) ||pi_t(s)P pi_t(s)^*-P||_HS
    >=kappa sqrt(rank P).
```

Right multiplication by `pi_t(s)` identifies the left side with the
commutator expression. The same fixed `kappa` applies for every choice
of `t`, `H_t`, `pi_t`, and `P`. This is the feature absent from a
fixed-representation compactness argument.

## Compression pays a fixed unitarity error

For `U=pi_t(s)`, decompose relative to `P H_t` and its orthogonal
complement. With `A=PUP`, the two off-diagonal blocks have equal squared
Hilbert-Schmidt norms: each is `rank P-||A||_HS^2`. Therefore

```text
||[P,U]||_HS^2=2 Tr(I_(P H_t)-A^*A).
```

Choose the generator supplied by the preceding Kazhdan inequality. Its
compression satisfies

```text
tr_(P H_t)(I-A^*A)>=kappa^2/2,
||I-A^*A||_op>=kappa^2/2.
```

For any unitary `V` on the compressed space, the contraction bound
`||A||<=1` yields

```text
||I-A^*A||=||V^*V-A^*A||<=2||V-A||.
```

Thus `||V-A||>=kappa^2/4`. This applies even to the best possible
unitary replacement of the compression; choosing a polar factor cannot
make the change small.

For moving parameters `t_n->0`, with each `t_n` nonzero and eventually
different from one-half, this gives the same fixed lower bound at every
stage. Hence exact Lie-group projective representations, including any
discrete-series realizations one chooses, cannot be compressed to nearly
unitary matrices by an operator-norm perturbation tending to zero.

The conclusion is about closeness to compressed exact operators. It
does not assert that a radically changed tuple has large projective
relation defects. Symbol corrections in Toeplitz quantization can change
the compression by a fixed amount and require a separate analysis of
their scalar multiplier; this theorem does not silently include them.

## What the inspected quantization and stability sources supply

[Manoliu, *Quantization of symplectic tori in a real polarization*,
arXiv:dg-ga/9609012](https://arxiv.org/abs/dg-ga/9609012)
identifies the Maslov projective factor and constructs unitary
representations of the integer metaplectic group. These exact finite
models lie in the metaplectic subgroup above. Their increasing quantum
level does not by itself supply a sequence of nonzero Deligne parameters
approaching zero.

[Zelditch, *Index and dynamics of quantized contact transformations*,
Annales de l'Institut Fourier 47 (1997)](https://www.numdam.org/item/AIF_1997__47_1_305_0/)
constructs unitary Toeplitz operators by adding a symbol to compressed
contact transformations. For torus automorphisms the construction
recovers the theta transformation laws. The inspected statements give
no `o(|t_n|)` Deligne scalar-projective defect estimate at moving
nonzero parameters. General unitarization alone does not provide that
estimate or identify its multiplier.

[Bader--Lubotzky--Sauer--Weinberger, *Stability and instability of lattices
in semisimple groups*, Theorem 1.1(O)](https://arxiv.org/html/2303.08943v2)
deduces operator instability of a linear group from nonzero real
cohomology in a positive even degree. The theorem does not prescribe
the scalar direction or little-o parameter rate of its almost
representations, so it does not establish the perturbative input here.

No second-order matrix construction was obtained. The headline exact
triple-cover radical problem remains open. The proved advance is that
even varying-parameter exact-representation compressions cannot furnish
such a construction through a small polar or unitary correction.

The verification was symbolic. No executable code, build, or local test
was run for this argument.
