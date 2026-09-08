# Exactifying the Jacobson tail braid and locating its required carrier

2026-09-08. This is a finite-dimensional reduction of the two-braid
problem. It does not establish a non-MF existence theorem.

Use the packet notation

```text
F=GL_3(F_2)_Q x GL_3(F_2)_P,
B=pi(w_23,w_23),          D=pi(1,w_13),
X=pi(w_23,1),            e=(I-X)/2.
```

The packet representation `pi` is exact. The operator `H` is a
self-adjoint unitary commuting with the head overlap `K~=S_3`.
The operators `D` and `X` commute, and the two tail swaps have product of
order three. Consequently

```text
(DB)^3=X.                                                (1)
```

The involution `X` is conjugate in the head group to the marked
transvection, so `e` has precisely the marked negative rank.

## Relative rounding that fixes the entire packet

Put `U=HD`. Then `U` is unitary and

```text
DUD=U^*.                                                (2)
```

Suppose `epsilon=||U^3-I||<2`. Every spectral value of `U` has a unique
nearest cube root of unity: write it as `z=zeta exp(i theta)` with
`zeta^3=1` and `|theta|<pi/3`. Ambiguity would require `z^3=-1`, which
the strict bound excludes. The nearest-root function `f` is continuous
on the spectrum and obeys `f(conjugate(z))=conjugate(f(z))`. Set

```text
U'=f(U),                    H'=U'D.                     (3)
```

Functional calculus and (2) give `DU'D=(U')^*`. Therefore `H'` is a
self-adjoint unitary, and `(H'D)^3=(U')^3=I`. Both `U` and `D` commute
with `pi(K)`, so `H'` does too. Neither `D` nor any other packet matrix
has been changed.

For `x=|theta|/2<pi/6`,

```text
|z-zeta|=2 sin(x),       |z^3-1|=2 sin(3x),
sin(3x)=sin(x)(3-4 sin(x)^2) >= 2 sin(x).
```

Hence `|z-zeta|<=|z^3-1|/2`, and spectral calculus proves

```text
||H'-H||=||U'-U||<=epsilon/2.                            (4)
```

The telescoping identity for cubes of two contractions gives
`||A^3-C^3||<=3||A-C||`. Apply it to `A=H'B`, `C=HB` to obtain

```text
||(H'B)^3-I|| <= ||(HB)^3-I||+3epsilon/2.                (5)
```

Let `gamma_tail` be the infimum of the first defect with the tail braid
exact, and let `gamma` be the two-defect infimum. The admissible set for
`gamma_tail` is nonempty: take a faithful packet and `H=D`.
Both infima lie in `[0,2]`. Inclusion of admissible sets gives
`gamma<=gamma_tail`. If `gamma<2`, apply (3)--(5) to packets whose
maximum defects tend to `gamma`; the tail defect is eventually less than
two and the resulting first defects are at most `5/2` times that maximum.
Thus `gamma_tail<=5gamma/2`. If `gamma=2`, this inequality follows
already from `gamma_tail<=2`. This proves

```text
(2/5)gamma_tail <= gamma <= gamma_tail.                  (6)
```

## Complete normal form for the exact tail braid

Now suppose `(HD)^3=I` exactly. Under the overlap decompose the space as

```text
directSum_kappa V_kappa tensor M_kappa,
```

where `V_kappa` are the three irreducible complex representations of
`K`. Schur's lemma writes both `H` and `D` as the identity on each
`V_kappa` tensor an operator on `M_kappa`. The two multiplicity operators
are involutions whose product has cube one. They therefore give a unitary
representation of the finite group

```text
<s,t | s^2=t^2=(st)^3=1> ~= S_3.                        (7)
```

For completeness, its three irreducibles are the trivial and sign
representations and the two-dimensional standard representation: these
can be constructed from the permutation action on three points, and their
squared dimensions sum to `1+1+4=6`, exhausting the group order. On each
one-dimensional component the two involutions agree. On a standard
component choose the `D` eigenbasis, with its positive line first. The
matrices are

```text
D=[1,0;0,-1],
H=[-1/2,sqrt(3)/2;sqrt(3)/2,1/2].                        (8)
```

Arbitrary multiplicities and changes of orthonormal bases give the
following full parameterization. Split `M_kappa=M_kappa^+ directSum
M_kappa^-` by the signs of the fixed operator `D`. Choose subspaces
`A_kappa^+<=M_kappa^+`, `A_kappa^-<=M_kappa^-` of a common dimension,
and a unitary map `T_kappa:A_kappa^- -> A_kappa^+`. On their sum,

```text
H=[ -(1/2)I         (sqrt(3)/2)T_kappa ]
  [ (sqrt(3)/2)T_kappa^*         (1/2)I ],                (9)
```

and on the orthogonal complement `H=D`. Conversely every such choice
gives the exact relations (7), as direct multiplication verifies.

Let `P_std` denote the projection onto the paired subspaces, including
their `K` factors. Equations (8)--(9) give

```text
P_std=(2I-HD-DH)/3,
(H-D)^2=3P_std,
rank(P_std)=2 sum_kappa dim(V_kappa) dim(A_kappa^+).      (10)
```

In particular `H-D` has range exactly `P_std` and vanishes on its
orthogonal complement. These formulas do not assert that `P_std`
commutes with the full head packet.

## The first braid must use that standard carrier

Write `V=HB`, `A=DB`, and `delta=||V^3-I||`. By (1), `A^3=X`.
The noncommutative telescoping identity gives

```text
V^3-A^3
 = V^2(H-D)B + V(H-D)BA + (H-D)BA^2.                   (11)
```

Let `J_std` project onto the sum of the ranges of

```text
P_std,        V P_std V^*,        V^2 P_std (V^*)^2.
```

Every summand on the right of (11) has range inside this sum. Because
`V^3-X=(V^3-I)+2e`, multiplication by `I-J_std` gives

```text
2(I-J_std)e=-(I-J_std)(V^3-I),
||(I-J_std)e||<=delta/2.                                (12)
```

If `delta<2`, restriction of `J_std` to `Ran(e)` is injective: a unit
vector of that range killed by `J_std` would make the left side of the
second inequality at least one. Therefore

```text
rank(e)<=rank(J_std)<=3 rank(P_std).                     (13)
```

Combining (10) and (13) gives

```text
sum_kappa dim(V_kappa) dim(A_kappa^+) >= rank(e)/6.       (14)
```

Thus the tail braid may be imposed exactly at a universal cost. The
remaining variable is a family of paired subspaces of known `D` sign
spaces and their unitary identifications. A small first defect requires
their three displayed translates to cover the marked negative space with
the explicit leakage bound (12). The result does not force the marked
rank to vanish and does not settle the two-braid infimum.
