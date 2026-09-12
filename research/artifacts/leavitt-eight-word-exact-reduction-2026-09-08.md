# An exact eight-row reduction of the Leavitt unitary certificate

2026-09-08. Handwritten group-word identities, independently checked by
three agents. No code, build, or numerical experiment is used for this
reduction. The comparison holds on every unitary tuple with `C^3=I`.

## 1. The complete retained packet

Work in `P=C_3*C_2^3`, with marked generators `c,b_1,b_2,b_3`.
Use `[x,y]=xyx^(-1)y^(-1)` and `gamma(x)=cxc^(-1)`. The shared
words of the current shorter compiler are

```text
d=[b_2,gamma(b_1)],       h=gamma^2(d),
a=[d,h],                 e=gamma(d),
j=a e a^(-1),            r_*=j c j c,

u=[b_2,gamma(b_3)],       w=[gamma^2(b_1),a],
p_0=gamma(b_2),          q_0=w,
p_1=[e,u],               q_1=[gamma^2(b_3),b_1],
X_0=p_0 q_0 p_0,         X_1=p_1 q_1 p_1,

A=j,                    B=X_0 X_1,       D=gamma^2(j). (1)
```

For conjugating exponents use `X^Y=Y^(-1)XY`, which differs from
`gamma(X)`. The eight rows are

```text
r_* = j c j c,

sigma = d^2,

rho_2 = B^3,

rho_3 = (A B)^4,

rho_5 = D^(-1)
        A^(B D A D A A^(B A))
        A^(B^(-1) D A D A A^(B^(-1) A)),

rho_6 = [ A^(B^(-1) D A D),
          A^(B^(-1) D A D A^B A^(B^(-1) A)) ],

rho_7 = [ A^(B D A D),
          A^(B^(-1) D A D A^B A^(B^(-1) A)) ],

rho_8 = [ A^(B D A^(B D A)),
          A^(B D A D A^B A^(B^(-1) A)) ].             (2)
```

Write `T_8` for (2). The original `T_9` used the same compiler and
six retained Thompson rows, together with

```text
r_*,       rho_1=j^2,       rho_4=(JD)^(-1)D(JD)J^(-1),
where J=j.                                                (3)
```

Native kernel authentication and the Thompson presentation are recorded
in `leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md`.
This reduction keeps `j,r_*` and every retained row exactly unchanged.

## 2. Replace the square row by an exact conjugate

The compiler definition gives the identity in `P`

```text
j^2=(a c)d^2(a c)^(-1).                                (4)
```

Thus every unitary evaluation and every unitarily invariant norm satisfy

```text
||rho_1-I||=||d^2-I||.                                 (5)
```

No small-defect assumption is used. These two square relators also have
the same normal closure individually in `P`.

## 3. The overlap row is a commutator with r_*

Let `J,C` be arbitrary unitaries with `C^3=I`, and put

```text
K=JC,       R=K^2,       D=C^(-1)JC.
```

For the compiler, `D=gamma^2(J)` has this form because the `C_3`
relation holds exactly. The substitutions are

```text
J=K C^(-1),       J^(-1)=C K^(-1),
D=C^(-1)K,        JD=K C^(-2)K=K C K.                 (6)
```

Expand the overlap word using (6), without assuming `J^2=I`:

```text
rho_4=(JD)^(-1)D(JD)J^(-1)
     =K^(-1) C^(-1) K^(-1) C^(-1) K^2 C K C K^(-1).
```

Set

```text
L=K^(-1) C^(-1) K^(-1) C^(-1),
M=C K C K^(-1).
```

Cancellation gives

```text
LM=K^(-1) C^(-1) K^(-1) C^(-1) C K C K^(-1)
  =K^(-2)=R^(-1).
```

Hence `M=L^(-1)R^(-1)`, and

```text
rho_4=L R L^(-1)R^(-1)=[L,R].                         (7)
```

In `P` this reads
`rho_4=[(jc)^(-1)c^(-1)(jc)^(-1)c^(-1),r_*]`.
In particular `r_*=1` alone implies `rho_4=1`.

For any unitarily invariant norm satisfying the triangle inequality,

```text
||rho_4-I||
 =||L R L^(-1)-R||
 <=||L(R-I)L^(-1)||+||R-I||
 =2||r_*-I||.                                          (8)
```

This applies to normalized Schatten norms for every `1<=p<=infinity`,
including normalized HS and operator norm. It compares the evaluated
words on arbitrary unitaries with `C^3=I`, not just their native images.

## 4. Same quotient and quantitative gap question

Let `N_i` be the normal closure of `T_i` in `P`. Equation (4) permits
replacing `rho_1` by `d^2`, and (7) puts the omitted `rho_4` in the
normal closure of the retained `r_*`. Therefore

```text
N_8=N_9.                                               (9)
```

The established nine-word theorem consequently authenticates `T_8`
as a native kernel packet and shows that its exact finite-dimensional
unitary models kill `c`.

Define `delta_i=max_(r in T_i)||r-I||`. The unchanged rows together
with (5) and (8) give

```text
delta_8 <= delta_9 <= 2delta_8.                         (10)
```

Thus the zero sets agree in every dimension, as do vanishing sequences
when dimension varies. Taking infima over any fixed admissible space
preserves the comparison. This includes each frozen `24k` space and
their union: a positive uniform gap for either packet is equivalent to
one for the other, with the displayed constants.

For normalized-HS squared-sum energies
`E_i=sum_(r in T_i)||r-I||_2^2`, the square-row equality gives

```text
E_9=E_8+||rho_4-I||_2^2,
E_8 <= E_9 <= E_8+4||r_*-I||_2^2 <= 5E_8.             (11)
```

This does not assert that the objective functions or their critical
points are identical.

## 5. Conservative length bounds

Count letters in `c,c^(-1),b_1,b_2,b_3`, using
`gamma^2(x)=c^(-1)xc` inside `P`. The shorter compiler gives

```text
|d|<=8,       |a|<=36,       |j|<=82,
|u|<=8,       |w|<=78,       |B|<=164,       |D|<=84.
```

The retained row bounds are

| Row | Length bound |
|---|---:|
| `r_*` | 166 |
| `d^2` | 16 |
| `rho_2` | 492 |
| `rho_3` | 984 |
| `rho_5` | 4528 |
| `rho_6` | 7576 |
| `rho_7` | 7576 |
| `rho_8` | 9880 |

The two conjugating exponents in `rho_5` have length at most `1070`,
giving `84+2(82+2*1070)=4528`. The commutator inputs in `rho_6,rho_7`
have bounds `910,2878`, and those in `rho_8` have bounds `2062,2878`.
Doubling the sum of each pair gives the displayed bounds. No cancellation
is needed. The reduction removes the overlap row of length at most `498`
and replaces the square row of length at most `164` by one of length
at most `16`. Shared evaluation can use the already constructed `d`.

## Scope

The proof uses only `C^3=I`, the shared word definitions, and unitary
invariance of the norm. It establishes a quantitative reduction on the
entire frozen-factor search space without assigning Leavitt coefficients
to arbitrary word values.

The exact finite-dimensional obstruction survives with eight rows. The
positive dimension-uniform normalized-HS lower bound remains unproved.
No nonhyperlinear group follows from this simplification alone.
