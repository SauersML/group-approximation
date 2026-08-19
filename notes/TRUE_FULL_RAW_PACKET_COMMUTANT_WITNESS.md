# One full-packet commutant unitary witnesses the comb gap

Date: 2026-08-14

## 1. Outcome

The exact subgroup-intersection certificate already proves a stronger
statement than the binary-algebra gap in
`TRUE_PAULI_CARRIER_BINARY_ALGEBRA_GAP.md`.

Let

```text
K  = <raw,z_11,z_001>,
K' = U* K U,
A  = C[K],
F  = U* Q U in C[K'].
```

The archived exact calculation gives

```text
|K|=16,                 K intersect K'={1},
F=F*=F^2,               tau(F)=1/4.                 (FCW1)
```

Then the trace-preserving conditional expectation onto the entire raw
finite-packet algebra satisfies

```text
E_A(F)=(1/4)1,
dist_2(F,A)^2=3/16.                                  (FCW2)
```

Consequently, in every sufficiently accurate trace-preserving finite matrix
coordinate, there is a unitary `V` commuting with the full exactified copy of
`K` such that

```text
||[V,F]||_2^2 >= 3/8-o(1).                          (FCW3)
```

After a two-by-two dilation, `V` may be taken to be a self-adjoint
involution without changing the commutator energy.  Thus the terminal
multiplicity obstruction is witnessed by one symmetry in the **full raw
packet commutant**, not merely by a symmetry commuting with the single
binary cut `E`.

## 2. The full-algebra expectation

For a finite subgroup `K` of a discrete group, the canonical conditional
expectation from the group von Neumann algebra onto `L(K)` deletes every
Fourier coefficient outside `K`:

```text
E_(L(K))(sum_g a_g lambda_g)=sum_(g in K) a_g lambda_g. (FCW4)
```

The projection `F` belongs to `C[K']`.  By `(FCW1)`, its only group term
which can also belong to `K` is the identity.  The identity coefficient is
its canonical trace, namely `1/4`.  This proves the first identity in
`(FCW2)`.  Since conditional expectation is the Hilbert--Schmidt orthogonal
projection and `F` is a projection,

```text
dist_2(F,A)^2
 =||F-(1/4)1||_2^2
 =tau(F)-tau(F)^2
 =1/4-1/16
 =3/16.                                             (FCW5)
```

This uses the full sixteen-element packet algebra.  In particular, adding
all raw Pauli off-diagonal matrix units does not reduce the `3/16` gap.

## 3. Finite-coordinate persistence

Let `rho_n` be trace-preserving matrix microstates on a finite set containing
`K`, `K'`, and the group-algebra polynomial defining `F`.  Exactify the
restriction to the fixed finite group `K`, and write

```text
A_n=Alg(rho_n(K)) subset M_(d_n)(C).                 (FCW6)
```

The normalized character of `rho_n|K` converges to the regular character.
Equivalently, the finite Gram matrix

```text
(tr_(d_n)(rho_n(k)^*rho_n(l)))_(k,l in K)            (FCW7)
```

converges to the identity matrix.  The mixed coefficients converge to the
canonical group traces

```text
tr_(d_n)(rho_n(k)^* F_n) -> tau(k^(-1)F)
                           = (1/4) if k=1, else 0.   (FCW8)
```

Because `K` is fixed, inversion of the Gram matrix has no growing-dimension
loss.  Orthogonal projection onto `A_n` therefore gives

```text
||E_(A_n)(F_n)-(1/4)1||_2 -> 0,
dist_2(F_n,A_n)^2 -> 3/16.                          (FCW9)
```

No coordinate choice or minimal-projection matching occurs here.

## 4. Exact commutant-energy identity

For any unital finite-dimensional star-subalgebra `A subset M_d(C)`, let
`E_A` be its trace-preserving conditional expectation.  Haar averaging over
the unitary group of the commutant gives

```text
E_A(X)=integral_(V in U(A')) V X V* dV.             (FCW10)
```

For self-adjoint `X`, expansion of the squared commutator and `(FCW10)` give

```text
integral_(V in U(A')) ||[V,X]||_2^2 dV
  =2||X-E_A(X)||_2^2.                               (FCW11)
```

Hence at least one `V in U(A')` has squared commutator energy at least the
right-hand side.  Applying this to `(FCW9)` proves `(FCW3)`.

If a symmetry is preferable, pass to the doubled coordinate and put

```text
V_tilde = [[0,V],[V*,0]],       X_tilde=diag(X,X).   (FCW12)
```

Then `V_tilde=V_tilde*=V_tilde^(-1)`, it commutes with the doubled copy of
`A`, and

```text
||[V_tilde,X_tilde]||_2^2=||[V,X]||_2^2.            (FCW13)
```

Doubling is an allowed amplification of a hyperlinear microstate and does
not change normalized traces, defects, or word separation.

## 5. What this closes

`TRUE_PAULI_MULTIPLICITY_HAS_ONE_SYMMETRY_WITNESS.md` produced a symmetry in
the commutant of one projection `E`.  That commutant is too large to interact
directly with finite-packet recovery.  Equations `(FCW2)--(FCW3)` place the
witness in the commutant of every raw packet element simultaneously.

The remaining theorem can therefore be stated sharply:

> **Full-packet bicommutant gate.**  Show that the cross-root multiplication
> and compressor synchronization relations force the transported carrier
> lift `F_n` to asymptotically commute with every unitary in
> `Alg(rho_n(K))'`.

That assertion contradicts `(FCW3)` with a fixed `3/8` energy floor.  It is
strictly more structured than asking for scalarization against the binary
commutant, because the forbidden witness now respects the whole exactified
raw Pauli packet.

## 6. Exact limitation

This is not yet a nonhyperlinear group.  The unitaries `V_n` are selected
from coordinate commutants and are not fixed group words.  The regular
representation realizes `(FCW2)` exactly, so no abstract group relation can
force `F` into `L(K)` or make it commute with `L(K)'` in every finite von
Neumann algebra.

The missing input must distinguish finite matrix coordinates and synchronize
their multiplicity spaces across the raw and comb charts.  Separate
finite-group exactification recovers `A_n` and `A_n'`, but it does not make
the comb carrier lie in `A_n=A_n''`.  The gain is that a successful
synchronization theorem now needs to control only one full-commutant
symmetry, with the quantitative contradiction already fixed at `3/8`.

## 7. Existing certificate

No new computation is needed.  The group facts in `(FCW1)` are already
recorded in
`experiments/atlas-pauli-transported-carrier.json` and explained in
`TRUE_PAULI_CARRIER_BINARY_ALGEBRA_GAP.md`.  Equations `(FCW2)--(FCW13)` are
finite Fourier and Hilbert--Schmidt identities.
