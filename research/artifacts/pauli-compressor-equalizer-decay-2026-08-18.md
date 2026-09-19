# 2026-08-18 — Compressor equalizer sectors exist, but their regular mass decays as `8^{-m}`

**Status:** exact finite-packet calculation.  This is a no-go for a tempting
finite-multiplicity shortcut; it does not prove nonhyperlinearity.

The one-cut atlas route asks for a finite-multiplicity coefficient corner in
which the comb compressor becomes a genuine finite unitary carrying a
one-sided Leavitt index.  A natural idea is to force the source scalar Pauli
packet to agree with its compressed Pauli packet on a positive-density Fourier
sector, then use Schur's lemma.  One such sector does exist.  The obstruction
is that compressor invariance pushes the equality condition down the whole
binary `0`-ray, and every extra level costs a factor `1/8` of regular trace.

## 1. The binary fringe decomposition

Put

```text
alpha(a)=s_0 a t_0,
q_m=alpha^m(1)=s_0^m t_0^m,
f_j=alpha^j(p_1)=s_0^j s_1 t_1 t_0^j.
```

Here `q_m` is the cylinder projection `0^m` and `f_j` is the cylinder
projection `0^j1`.  The Cuntz--Leavitt relations give, for every `m>=1`,

```text
1 = f_0+f_1+...+f_(m-1)+q_m,                         (E1)
f_j f_k=0  (j!=k),                                  (E2)
f_j q_m=0  (j<m).                                   (E3)
```

Work in three adjacent elementary roots and set

```text
X_j=x_12(f_j),
Y_j=x_23(f_j),
Z_j=x_13(f_j).
```

For each `j`, Steinberg multiplication gives

```text
[X_j,Y_j]=Z_j,
```

and the characteristic-two root groups make `X_j,Y_j,Z_j` involutions.  Thus

```text
H_j=<X_j,Y_j> ~= D_8.                                (E4)
```

Orthogonality `(E2)` makes distinct cells commute: all mixed commutators
between `H_j` and `H_k`, `j!=k`, are trivial.  Their coefficient supports are
disjoint, so the product is direct:

```text
H_[0,m) := <H_0,...,H_(m-1)> ~= D_8^m.              (E5)
```

## 2. Exact equalizer and its trace

Let `e_m` be the fixed-space/Fourier projection for the trivial character of
`H_[0,m)`.  In any representation on which the finite subgroup is exact,
`e_m` is the average of its `8^m` group elements.  On `e_m`, every fringe
root generator acts trivially.

Because one additive root is a homomorphism from `(R,+)`, `(E1)` gives

```text
x_12(1)=x_12(f_0)...x_12(f_(m-1)) x_12(q_m),
x_23(1)=x_23(f_0)...x_23(f_(m-1)) x_23(q_m),
x_13(1)=x_13(f_0)...x_13(f_(m-1)) x_13(q_m).
```

Therefore on `e_m` the scalar and depth-`m` compressed Pauli triples coincide:

```text
e_m x_rs(1)=e_m x_rs(q_m)          for rs=12,23,13. (E6)
```

Under the canonical regular character, the restriction to every finite
subgroup is its regular character.  Hence

```text
tau(e_m)=1/|H_[0,m)| = 8^(-m).                       (E7)
```

The long-root sign `x_13(q_m)` commutes with every `H_j`, `j<m`, and is not in
`H_[0,m)`.  Thus the negative Pauli equalizer

```text
E_m=e_m (1-x_13(q_m))/2                              (E8)
```

has exact regular trace

```text
tau(E_m)=1/(2*8^m).                                  (E9)
```

For `m=1` this is the tempting trace-`1/16` corner: the scalar Pauli packet and
the `p_0=s_0t_0` packet agree there.

## 3. Why compressor invariance destroys the density

The comb covariance shifts the fringe:

```text
alpha(f_j)=f_(j+1),
alpha(q_m)=q_(m+1).                                  (E10)
```

Consequently a compressor carries the depth-`m` equality conditions to the
next block of `m` fringe cells.  Requiring one sector to satisfy both the
original and once-transported equality conditions forces triviality of

```text
H_0,H_1,...,H_m,
```

and the corresponding negative central condition has trace at most

```text
1/(2*8^(m+1)).                                      (E11)
```

After `r` iterates the bound is `1/(2*8^(m+r))`.  Any sector invariant under
all compressor iterates therefore has regular trace zero.

This is the finite Fourier shadow of the extension-fiber/rectangular escape
already seen in the growing-root decoder: every compression step creates one
fresh independent Pauli fringe cell.  A fixed-depth equalizer is useful as a
local coordinate chart, but it cannot be the positive-density invariant
coefficient corner required by the one-cut contradiction.

## 4. Research consequence

The calculation rules out the following shortcut:

> choose a positive-density character sector on which source and compressed
> Pauli packets coincide, then treat the compressor as an endomorphism of that
> one finite multiplicity space by Schur's lemma.

One-step equality has positive mass, but a compressor-stable equality sector
has zero regular mass.  A successful one-cut extraction must therefore
**transport coefficient data across changing equalizer sectors** or use a
relative/gauge index; it cannot obtain a positive-density fixed fiber merely
by imposing finitely many source=compressed Pauli character equations at all
scales.

This no-go is compatible with `TRUE_NEGATIVE_CHARACTER_SECTOR_AGGREGATION.md`:
aggregation keeps total negative long-root mass fixed by allowing all extension
fibers, whereas the equalizer attempt kills the newly created fringe fiber at
every depth and pays the factor `1/8` each time.
