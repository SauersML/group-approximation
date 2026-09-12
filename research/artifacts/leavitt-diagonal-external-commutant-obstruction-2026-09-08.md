# Diagonal embeddings give an embeddability-preserving commutant obstruction

2026-09-08. Exact group, Fourier, and conditional-expectation arguments.
No computation or build is used. Hyperlinearity remains undecided.

The distinction is between a commutant computed in the group's own
von Neumann algebra and a commutant in a larger tracial algebra.
Here the latter contains an extra unitary at distance exactly one
from the native right algebra together with the ambient commutant
of the whole group. The separation persists in every further finite
tracial extension. Unlike a construction requiring a new amalgamated
group to be embeddable, tensor-square microstates supply this example
whenever the original group is hyperlinear.

## 1. Native subgroups and their centralizers

Let `R=L_(F_2)(1,2)` and use the four-leaf identification

```text
H=R^x ~= GL_4(R)=EL_4(R).
```

Set

```text
L={diag(g,1):g in EL_3(R)},
K={diag(I_3,k):k in R^x}.
```

The established prefix identifications, GL/EL equality, and simplicity
make both `L,K` copies of the countably infinite simple group `H`.
The algebraic inputs are
[GL/EL and prefix identification](../leavitt-gl-equals-el-and-perfect-unit-group.md),
[simplicity](../binary-leavitt-elementary-group-is-simple.md), and
[the center calculation `Z(R)=F_2`](../leavitt-center-is-coefficient-field.md).
Infinitude also follows from the unbounded finite matrix subgroups
in the degree-zero coefficient ring.

We use the two exact group centralizers

```text
C_H(L)=K,       C_H(K)=L.                            (1)
```

For the first, write an element commuting with `L` in `3+1` block
form. Commuting with every constant elementary matrix in the upper
block kills both off-diagonal blocks and makes the upper block
`a I_3`. Commuting with `x_ij(r)` for every `r in R` forces `a`
to be central. The full block diagonal matrix is invertible, so
`a` is a unit; `Z(R)=F_2` makes `a=1`. The remaining lower block
is an arbitrary unit, as required.

For the second, choose a unit `q in R` for which `q-1` is invertible.
For example, under `R ~= M_2(R)` take the constant matrix
`[[0,1],[1,1]]`; it satisfies `q^2+q+1=0`, and in characteristic
two `q-1=q^2` is a unit. Commuting a block matrix `[[g,b],[c,d]]`
with `diag(I_3,q)` gives `b(q-1)=0` and `(q-1)c=0`, so its
off-diagonal blocks vanish. Its lower unit then centralizes `R^x`.
The center of an infinite simple group is trivial, so `d=1`.
Its upper block lies in `GL_3(R)=EL_3(R)`, proving (1).

## 2. Fourier invariants for the diagonal embedding

Put

```text
N=L(H),       A=L(L),       B=L(K),
M=N tensor N=L(H times H).
```

All traces are the canonical normalized traces. The diagonal subgroup
of `H times H` gives the normal trace-preserving embedding

```text
Delta:N -> M,       Delta(lambda_g)=lambda_g tensor lambda_g.
```

An infinite simple group has no nontrivial action on a finite set:
the kernel would be either the whole group or trivial, and the latter
would embed an infinite group into a finite symmetric group. Thus
every finite `L`-conjugacy orbit in `H times H` is a singleton.
By (1), its singleton pairs are precisely `K times K`.

Identify `L^2(M)` with `l^2(H times H)`. A vector fixed by conjugation
by `Delta(L)` has Fourier coefficients constant on its conjugacy
orbits. Square summability kills all infinite orbits. Consequently

```text
L^2(M)^(Ad Delta(L))=l^2(K times K),
Delta(A)' intersect M=B tensor B.                    (2)
```

The same argument for `H`, whose center is trivial, gives

```text
Delta(N)' intersect M=C I.                          (3)
```

For comparison, the one-coordinate Fourier calculation gives the
internal identity `A' intersect N=B`; the calculation for `K`
also gives `B' intersect N=A`. These identities do not transport
to arbitrary external ambient algebras as identities with the
embedded native algebras.

Choose `k in K\{1}` and let

```text
x=lambda_k tensor I.
```

It is a unitary in the commutant (2). The subgroup defining
`Delta(B)` consists of pairs `(h,h)` with `h in K`. The Fourier
basis vector `(k,1)` lies outside that subgroup, so

```text
E_(Delta(B))(x)=0,       ||x||_2=||x||_op=1.          (4)
```

Thus already inside `M`, adjoining the whole-group commutant (3)
does not recover this extra operator.

## 3. Exact separation survives every finite tracial extension

Let `M subset Q` be any unital trace-preserving inclusion of finite
tracial von Neumann algebras. Write

```text
C_Q=Delta(N)' intersect Q,
D_Q=Delta(B) join C_Q.
```

The trace-preserving conditional expectation `E_M:Q -> M` is
`M`-bimodular. For `z in C_Q` and every `y in Delta(N)`, this gives

```text
y E_M(z)=E_M(yz)=E_M(zy)=E_M(z)y.
```

Therefore (3) implies `E_M(C_Q) subset C I`. Moreover `C_Q`
commutes with `Delta(B)`. The algebraic span of products `b z`,
with `b in Delta(B)` and `z in C_Q`, is dense in `L^2(D_Q)`.
On each such product,

```text
E_M(b z)=b E_M(z) in Delta(B).
```

Continuity in `L^2` consequently proves

```text
E_M(D_Q) subset Delta(B).                           (5)
```

For `y in D_Q`, equations (4)--(5) imply

```text
<x,y>_2=<x,E_M(y)>_2=0.
```

Hence the exact conclusion in every such extension is

```text
x in Delta(A)' intersect Q,
E_(D_Q)(x)=0,       dist_2(x,D_Q)=1.                 (6)
```

In particular, even a proposed inequality
`dist_2(x,D_Q)<=F(max_s ||[Delta(lambda_s),x]||_2)`
with `F(0)=0` fails on this unitary, for any chosen generators
`s` of `L`. Their commutators are all exactly zero.

## 4. Tensor-square microstates and the frozen factors

Suppose `H` is hyperlinear, equivalently that its canonical trace
admits matrix microstates. If `U_g^(n)` are such microstates, then

```text
(g,h) -> U_g^(n) tensor U_h^(n)
```

are microstates of `H times H`. The two tensor factors commute
exactly; each fixed multiplicative error is bounded by the sum
of the two original errors, and normalized traces multiply.
Their tracial ultraproduct therefore contains a trace-preserving
copy of `M=L(H times H)`. Its diagonal copy of `H` is represented
by `U_g^(n) tensor U_g^(n)`.

The conclusion (6) applies to this matrix tracial ultraproduct.
It applies as well after embedding those matrix algebras into the
hyperfinite finite factor and passing to its tracial ultrapower.
There is no assumption that an unrelated amalgamated free product
is embeddable.

For completeness, tensor squaring also preserves the exact frozen
source profiles whenever the original source tuple has them. If its
dimension is `n=24k`, then in dimension `n^2`:

* Each eigenvalue of `C tensor C` has multiplicity
  `3(n/3)^2=n^2/3`.
* For the simultaneously commuting involutions, each character of
  `C_2^3` in the tensor-square representation has multiplicity
  `8(n/8)^2=n^2/8`.
* `n^2=24*(24k^2)`, so this is again an admissible frozen dimension.

The profiles are understood up to the usual unitary identification
with the prescribed frozen matrices. For any source word `w`, its
tensor-square evaluation is exactly `W tensor W`, where `W` is
the original evaluation. Since `W` is unitary,

```text
W tensor W-I=(W-I) tensor W+I tensor (W-I),
||W tensor W-I||_2 <= 2||W-I||_2.                    (7)
```

Thus this construction is compatible both with full group microstates
and with the current finite packet and factor-profile constraints.
It does not assert that a vanishing sequence for that one finite
packet is already a full microstate sequence for `H`.

The distance-one conclusion concerns the von Neumann algebras generated
by the limiting represented groups. It does not identify these with
ultraproducts of the full finite-stage generated algebras: finite-stage
elements may require word lengths growing with the stage, and replacing
one algebra by the other would need a separate proof.

## 5. What the obstruction preserves and what it leaves open

The diagonal embedding preserves every native group-word identity.
In particular any chosen native compressor and its subgroup relations
are retained. The copies of `H,L,K` have the same abstract group
properties as before. The restricted character of `H` remains its
canonical character, since

```text
tau_M(Delta(lambda_g))=delta_(g,1).
```

All root fixed-projection trace identities therefore remain valid.
Those are fixed projections for left multiplication by root groups;
they do not identify the invariant space for the conjugation action
on `L^2(Q)`. A Kazhdan estimate for that conjugation action projects
onto the actual external commutant, which contains the unitary in (6).

Conditional on hyperlinearity, this supplies a bad embedding into a
matrix tracial ultraproduct, and into the hyperfinite ultrapower,
even after including the ambient whole-group commutant in the proposed
target algebra. Hence the universal external-commutant identification
cannot be inferred from just the exact native identities, character
information, and abstract property (T).

The construction does not say that every embedding has this excess.
It does not exclude selecting a special embedding or proving a
different controlled replacement. Nor does the conditional statement
decide whether any embedding exists: nonhyperlinearity is not proved.
