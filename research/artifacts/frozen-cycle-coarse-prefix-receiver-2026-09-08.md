# A fixed coordinate cycle supplies the coarse prefix receiver

2026-09-08. Direct finite-dimensional Hilbert-space and representation
calculations. No computation or enumeration is used.

The actual Leavitt packet contains `J=j`, `r_*=(JC)^2`, and `rho_1=J^2`.
This note extracts an auxiliary exact `S_3` anchor and its three-cell
projection system from those two errors, while keeping `C` and the
dimension fixed. It then isolates an incompatible pair of child
transports for the actual compiled `B` occurrence. Deriving those
transports from the remaining packet is not proved.

All Schatten norms below use the normalized trace `tr=Tr/n`.

## 1. Quantitative rounding with the cycle fixed

Suppose `C,J` are unitary, `C^3=I`, and the eigenspaces of `C` for
`1,omega,omega^2` all have dimension `m`; thus `n=3m`. Set

```text
r=||(JC)^2-I||_2,       s=||J^2-I||_2.
```

Round each eigenvalue of `J` to the nearer of `1,-1`, choosing either
at a tie, and call the resulting self-adjoint unitary `H`. The scalar
inequality

```text
min(|z-1|,|z+1|) <= |z^2-1|/sqrt(2),       |z|=1,
```

gives

```text
||H-J||_2=||H-J^(-1)||_2 <= s/sqrt(2).               (1)
```

The map `mathcal T(X)=C X C` is a unitary operator of order three
on the Hilbert space of matrices with normalized HS inner product.
Consequently

```text
T=(H+C H C+C^2 H C^2)/3                              (2)
```

is the orthogonal projection of `H` onto its fixed space
`M={X:C X C=X}`. The matrix `T` is self-adjoint: taking adjoints
interchanges the last two summands. On each nonfixed eigenspace of
`mathcal T`, the modulus of its eigenvalue minus one is `sqrt(3)`.
It follows that

```text
||H-T||_2 = ||C H C-H||_2/sqrt(3)
          <= (r+sqrt(2)s)/sqrt(3).                   (3)
```

For the inequality, use
`||C J C-J^(-1)||_2=r` and the two terms in (1).

There is a self-adjoint unitary polar completion `J_0` of `T` which
still belongs to `M`. To see the only possible dimension issue,
decompose by the three eigenspaces of `C`. A self-adjoint element
of `M` has the block form

```text
T = [ T_0   0    0  ],
    [  0    0    X  ]
    [  0   X^*   0  ]
```

where `T_0` is self-adjoint and `X` is square. Round `T_0` to its
sign, choosing signs on its kernel. Complete the polar partial
isometry of `X` to a unitary `V`; its two kernel dimensions agree
because `X` is square. Replace the lower block by
`[[0,V],[V^*,0]]`. This constructs `J_0` and proves

```text
J_0^2=I,       C J_0 C=J_0,       (J_0 C)^2=I.        (4)
```

A unitary polar completion minimizes HS distance from `T` among
all unitaries, so `||J_0-T||_2 <= ||H-T||_2`. Both `J_0,T` belong
to `M`, and `H-T` is orthogonal to `M`. Pythagoras and (3) therefore
give

```text
||J_0-H||_2 <= sqrt(2)||H-T||_2,

||J_0-J||_2
 <= sqrt(2/3) r +(1/sqrt(2)+2/sqrt(3)) s
 <= 2(r+s).                                         (5)
```

This requires no smallness assumption. The bound is useful when the
two displayed defects are small.

## 2. The exact S3 anchor supplies three equal cells

The pair `J_0,C` represents the group

```text
S_3=<J_0,C | J_0^2=C^3=(J_0 C)^2=1>.
```

Write its multiplicities of the trivial, sign and two-dimensional
standard representations as `a,b,t`. On a three-cycle, the first
two representations have eigenvalue one, and the standard has
eigenvalues `omega,omega^2`. Hence the frozen cycle profile implies

```text
t=m,       a+b=m.                                   (6)
```

Equivalently, `Tr(C)=a+b-t=0` together with the prescribed nonreal
eigenspace dimensions gives (6).

Let the subgroup `C_2=<J_0>` stabilize the label `1` in the three-letter
action on `00,01,1`. Its trivial induced representation is the
three-point permutation representation, namely `1+standard`. Its
sign induced representation is `sign+standard`: it is the sign twist
of that permutation representation. Thus (6) says that our exact
representation is unitarily equivalent to

```text
Ind_(C_2)^(S_3) (a copies of trivial + b copies of sign). (7)
```

The three coset fibers in (7) yield a PVM `Q_00,Q_01,Q_1`, each of
rank `m`, with

```text
C:   Q_00 -> Q_01 -> Q_1 -> Q_00,
J_0: Q_00 <-> Q_01,       Q_1 -> Q_1.                (8)
```

The arrows mean conjugation of projections. On the fixed cell, `J_0`
may act by either fiber sign. In particular (8) does not assert that
`J_0` is the identity on `Q_1 H`.

This is a coarse receiver extracted from the frozen cycle and the
two actual auxiliary word defects. It need not be a reducing support
of those defects, and no uniqueness of the PVM is asserted.

## 3. The missing occurrence is the compiled B child transport

In the native prefix action, the code is `(00,01,1)` and the compiled
word is `B=X_0 X_1`, with `X_0=swap(01,10)` and
`X_1=swap(01,11)`. On columns it maps

```text
01 -> 11 -> 10 -> 01.
```

Therefore the two required child transports for an orthogonal
refinement `Q_1=Q_10+Q_11` have the precise orientation

```text
B Q_01 B^* approximately Q_11,
B^* Q_01 B approximately Q_10.                     (9)
```

For any projections `P,Q`,

```text
||P-Q||_2^2=tr(P)+tr(Q)-2tr(PQ)
           >= |tr(P)-tr(Q)|.                        (10)
```

Both conjugates on the left of (9) have rank `m`. Each target child
has rank at most `m`, and their ranks sum to `m`. Adding (10) for
the two comparisons gives the dimension-free bound

```text
||B Q_01 B^*-Q_11||_2^2
 + ||B^* Q_01 B-Q_10||_2^2 >= m/n=1/3.              (11)
```

Thus at least one child error is at least `1/sqrt(6)`, for every
choice of the coarse PVM from Section 2 and every refinement.
The statement allows any unitary `B`; adding its order-three
relation cannot invalidate the bound.

This pinpoints what a receiver extraction would need to prove. The
coarse `C,J_0` covariance is available. A derivation of both comparisons
(9), with errors tending to zero as the actual packet defect tends
to zero, would contradict (11). This note does not supply that
derivation. In particular, replacing prescribed conjugator words by
independently chosen transports would not establish it.

## 4. The receiver bound is sharp even with the finite S4 anchor

Here is an auxiliary six-point sharpness example, with ordinary
permutations acting on columns:

```text
C   =(1 3 5)(2 4 6),
J_0 =(1 3)(2 4),
B   =(3 6 1)(4 2 5).

Q_00={1,2},       Q_01={3,4},
Q_10={5},         Q_11={6},       Q_1={5,6}.
```

The displayed subsets name coordinate projections. Direct evaluation
gives

```text
J_0 C=(3 5)(4 6),       J_0 B=(2 5)(3 6).
```

Consequently `J_0^2=(J_0 C)^2=B^3=(J_0 B)^4=I`, and `C` has
two copies of the regular `C_3` representation. The images in (9) are

```text
B{3,4}={2,6},       B^(-1){3,4}={1,5}.
```

Each differs from its target by one extra coordinate, so both squared
normalized HS errors are exactly `1/6`. Thus the constant in (11)
cannot improve using only these finite anchors.

These are auxiliary matrices. No native `B_1,B_2,B_3` realizing their
prescribed compiled `J_0,B` words is claimed, and the other packet
relators are not asserted. Amplification preserves this exact
sharpness calculation but adds no such authentication.

## 5. A source-authenticated model isolates two remaining rows

The six-point example above did not authenticate the compiled source
words. The following model does. Use the actual shorter compiler and
the retained packet

```text
T_8={r_*,d^2,rho_2,rho_3,rho_5,rho_6,rho_7,rho_8}
```

specified in [the exact eight-row reduction](leavitt-eight-word-exact-reduction-2026-09-08.md).
Let `z,w` be the two independent central involutions in

```text
G=GL_3(F_2) times <z,w>,
```

and define the marked source tuple by

```text
c=((123),1),
b_1=(x_12(1),1),
b_2=(x_12(1),z),
b_3=(x_12(1),w).                                    (12)
```

The notation `(123)` is the coordinate permutation on columns. The
three `b_i` are commuting involutions. Their product with exponent
vector `(e_1,e_2,e_3)` is

```text
(x_12(1)^(e_1+e_2+e_3), z^e_2 w^e_3).
```

If this is identity, its central coordinates force `e_2=e_3=0`,
and then its first coordinate forces `e_1=0`. Thus the marked
`C_2^3` factor embeds, as does the order-three factor generated by `c`.

There are `7` choices for the first nonzero column of an invertible
three-by-three matrix over `F_2`, then `6` outside its span, then
`4` outside the plane spanned by the first two. Consequently

```text
|GL_3(F_2)|=7*6*4=168,
|G|=672=24*28.                                      (13)
```

Use the regular representation of `G`. Its restriction to either
embedded finite factor is a sum of regular representations, by coset
decomposition. Therefore it has the exact frozen `C_3` and `C_2^3`
profiles: the three cycle eigenvalues each have multiplicity `224`,
and the eight joint sign characters each have multiplicity `84`.
Equivalently, the regular representation of this direct product is
the tensor product of its two regular representations. No explicit
672-by-672 matrix computation is required.

Here are the compiler values. Entries without displayed central tags
have trivial central coordinate. To avoid confusing the central
generator `w` with a compiler word, denote the latter by `w_word`.
Three-distinct-index elementary commutators give

```text
d=x_13(1),       h=x_32(1),       a=x_12(1),
e=x_21(1),       u=d,             w_word=x_32(1),
j=A=(12),       D=(13),

p_0=(x_23(1),z),        q_0=x_32(1),
p_1=x_23(1),            q_1=x_32(1).
```

The tags cancel in all commutators. In `p_0 q_0 p_0` the two
copies of `z` cancel as well. The usual characteristic-two swap
identity now gives

```text
X_0=X_1=(23),       B=X_0 X_1=I.                    (14)
```

Evaluate the eight retained rows at these exact shared values:

```text
r_*=d^2=rho_2=rho_3=rho_6=rho_7=I,
rho_5=D,
rho_8=[A,D]=c.                                      (15)
```

For a direct check of the longer rows, put `E=DAD=(23)`. When `B=I`,
both exponents in `rho_5` reduce to `E`, and `A^E=D`; thus the
two identical involutions cancel, leaving `D^(-1)=D`. Both inputs
of `rho_6,rho_7` are likewise `D`. In `rho_8`, the first exponent
is `D A^(DA)=D^2=I`, because `A^(DA)=D`. Its second exponent is
`E`, so its inputs are `A,D`. Finally `AD=c^(-1)` and
`[A,D]=(AD)^2=c`. This uses the prescribed conjugation convention
`X^Y=Y^(-1)XY` throughout.

A nonidentity element has trace zero in the regular representation.
Both `D` and `c` are nonidentity, so their normalized HS defects in
(15) are exactly `sqrt(2)`.

For this tuple the anchor is already exact: `J_0=J=A` is allowed.
In every coarse PVM of Section 2 and every orthogonal refinement,
`Q_01` is orthogonal to both children. Since `B=I`, their errors
satisfy the stronger exact identity

```text
||B Q_01 B^*-Q_11||_2^2 + ||B^* Q_01 B-Q_10||_2^2
 =2tr(Q_01)+tr(Q_10)+tr(Q_11)=1.                    (16)
```

Thus the actual source and its compiled words can satisfy all six
other retained rows, including `rho_6,rho_7`, while the fine receiver
fails by a fixed amount. This is a countermodel to extracting the
receiver from those six rows alone. It does not satisfy the full
packet, and it makes no assertion about omitting only one of
`rho_5,rho_8`.

## 6. Quantitative and logical boundary

Apply Sections 1--2 with the actual word `J=j(B_1,B_2,B_3,C)` of the
packet. The result is a nearby auxiliary `J_0`. It is not a change
to the original three finite-factor generators that makes their
compiled word equal to `J_0`.

If one evaluates a fixed auxiliary word after replacing `J` by
`J_0` and `D=C^(-1)JC` by `D_0=C^(-1)J_0 C`, telescoping costs
at most the number of changed occurrences times (5). This permits
fixed-word comparisons; it supplies no constant independent of
arbitrarily growing word length or refinement depth.

Literal finite prefix models cannot satisfy (9) with vanishing error
while retaining the extracted coarse covariance. Arbitrary approximate
models of the nine-word presentation have not been shown to carry
those fine prefix projections. The missing fine receiver remains a
mathematical obligation, and no uniform HS gap or nonhyperlinearity
claim is made here.
