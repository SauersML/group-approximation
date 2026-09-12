# All four Leavitt packet words have an exact 24-point model

2026-09-08. An explicit permutation construction, proved by hand.
It satisfies all four words of the current Leavitt packet in the
frozen `24k` format, already at `k=1`. Its generated finite group
is `S_3 x C_2^2`. Thus these four words have zero minimum in both
normalized-HS and operator norm. The full relation exhaustion is
not satisfied. One missing native relation is the involution law
`d^2=1` for the derived constant root, which fails in this model.
No unrestricted gap conclusion is asserted for the packet enlarged by
that relation; Section 5 records a necessary exact-model condition.

## 1. Frozen factors and the relative permutation

Use the orthonormal basis indexed by

```text
Omega=(Z/3) x F_2^3,
C|a,x>=|a+1,x>,
D_i|a,x>=|a,x+e_i>,             i=1,2,3.
```

Here `C` is eight copies of the regular representation of `C_3`,
and the `D_i` jointly give three copies of the regular representation
of `C_2^3`. These are exactly the frozen factors for `k=1`.
Write `epsilon(x)=(-1)^(x_1+x_2+x_3)`, and define

```text
U|a,x>=|epsilon(x)a,x>.                              (1)
```

The sign acts on `a` modulo three. This permutation satisfies
`U=U^*=U^(-1)`. Conjugating the second frozen factor gives

```text
B_i=U D_i U^*,
B_i|a,x>=|-a,x+e_i>.                                (2)
```

Indeed `epsilon(x+e_i)=-epsilon(x)`, so the two sign multipliers
in `U D_i U` have product minus one. Thus all the `B_i` are
commuting involutions. Their joint action is faithful: a product
with nonzero exponent vector translates the `x` coordinate by
that nonzero vector.

For an explicit permutation list, encode

```text
x=x_1+2x_2+4x_3 in {0,...,7},
index(a,x)=8a+x in {0,...,23}.
```

The odd-parity values of `x` are `1,2,4,7`. Formula (1) fixes
all even-parity coordinates and every coordinate with `a=0`.
It exchanges `a=1` and `a=2` on those four odd-parity fibers.
Therefore, in zero-based indices,

```text
U=(9 17)(10 18)(12 20)(15 23),                       (3)
```

with the other sixteen indices fixed. Formula (3) is a complete
exact certificate for the relative unitary.

## 2. One commutator calculation evaluates the entire packet

Use `gamma(X)=C X C^(-1)` and the commutator convention
`[X,Y]=XYX^(-1)Y^(-1)`. From (2),

```text
gamma(B_j)(a,x)=(-a+2,x+e_j),
B_i gamma(B_j)(a,x)=(a+1,x+e_i+e_j).
```

Both `B_i` and `gamma(B_j)` are involutions. The square of
their product translates `a` by two and fixes `x`, so

```text
[B_i,gamma(B_j)]=C^2           for every i,j.         (4)
```

Retain exactly the native straight-line definitions from
`leavitt-24k-kernel-packet-excludes-scalar-field-models`:

```text
d=[B_2,gamma(B_1)],        h=gamma^2(d),
a_word=[d,h],             e=gamma(d),
j=a_word e a_word^(-1),
u=[B_2,gamma(B_3)],        w=[gamma^2(B_1),a_word].
```

We write `a_word` to distinguish this word from the coordinate `a`.
Equation (4) implies

```text
d=h=e=j=u=C^2,            a_word=w=I.                 (5)
```

It also makes both `[B_1,gamma(B_2)]` and
`[B_3,gamma(B_1)]` equal to `C^2`. Consequently the four
packet words evaluate exactly as follows:

```text
r_*=j C j C=(C^2 C)^2=I,
R_v=[B_3,gamma(B_3)]d^(-1)=C^2(C^2)^(-1)=I,
R_0=[u,w]=[C^2,I]=I,
R_sum=[[B_1,gamma(B_2)],h]
      [[B_3,gamma(B_1)],gamma^2(u)] a_word^(-1)
     =[C^2,C^2][C^2,C^2]I=I.                        (6)
```

No coefficient-matrix representation, rounding, optimization, or
numerical tolerance enters this calculation.

## 3. The finite group and its regular action

Every `B_i` inverts `C`:

```text
B_i C B_i=C^(-1).
```

Hence the generated group has normal forms
`C^a B_1^(x_1) B_2^(x_2) B_3^(x_3)` and at most 24 elements.
Each normal form sends `(0,0)` to `(a,x)`, so these 24 forms
are distinct and the action on `Omega` is regular. The group is

```text
G=C_3 semidirect C_2^3 ~= S_3 x C_2^2.               (7)
```

More explicitly, `<C,B_3>` is `S_3`, while the two independent
central involutions `B_1 B_3` and `B_2 B_3` generate the direct
`C_2^2` factor. Thus an equivalent abstract description is

```text
G=S_3 x <x,y>,
c=((123),1),
b_1=((12),x), b_2=((12),y), b_3=((12),1).
```

Both marked finite factors embed, so their restrictions really are
the required regular multiples. In the explicit basis this was already
guaranteed by `C` and the common conjugation of the `D_i`.

For every `k>=1`, use `U_k=U tensor I_k`. Equations (2)--(6)
then hold in the prescribed basis of dimension `24k`. Therefore

```text
min_(V in U(24k)) max_(r in {r_*,R_v,R_0,R_sum})
                    ||pi_(k,V)(r)-I|| = 0           (8)
```

for every `k`, in either normalized-HS or operator norm. In
particular this packet cannot witness a positive uniform gap.

## 4. The precise missing root relation

In the actual Leavitt elementary group, `d=x_13(ts)=x_13(1)`.
Every characteristic-two elementary root is an involution, so

```text
R_d=d^2
```

is another true word in the marked kernel. It has a length-at-most-16
expression in `c,c^(-1),b_1,b_2`: the commutator `d` has length
at most eight. This relation was absent from the four-word packet.

In the present model, (5) instead gives

```text
pi(R_d)=(C^2)^2=C != I.                              (9)
```

Since `C` is regular on its order-three orbits, its normalized
trace is zero. Accordingly, at every amplification,

```text
||pi(R_d)-I||_2=sqrt(2),
||pi(R_d)-I||_op=sqrt(3).                            (10)
```

The failure is explicit: the packet's derived constant root has
order three instead of two, and its commutator with the cyclic
conjugate degenerates to the identity. Thus the construction lies
outside the literal characteristic-two coefficient realization
excluded by the rank-gap theorem. There is no conflict between
that restricted rank theorem and (8).

Adding `R_d` excludes this model and its amplifications. This
calculation does not decide whether the enlarged packet has other
finite models or a positive normalized-HS or operator-norm gap.
It also does not give a model of the whole Leavitt relation
exhaustion: the true relation `R_d` already fails. Hyperlinearity
and nonhyperlinearity of the full unit group remain unresolved
by this construction.

## 5. An exact restriction after the missing involution law is added

Consider any exact group model of the packet together with `d^2=1`,
retaining the nonidentity marked element `c` of order three. Put

```text
p=b_3 gamma(b_3)=b_3 c b_3 c^(-1)=[b_3,c].
```

Since `b_3` and `gamma(b_3)` are involutions, the relation `R_v=1`
gives

```text
d=[b_3,gamma(b_3)]=p^2.
```

The extra relation `d^2=1` therefore gives `p^4=1`. Also `d`
cannot be the identity: otherwise its words `h,e,a_word,j` are
all identity, and `r_*=1` becomes `c^2=1`, contradicting the
nontrivial order-three mark. Thus `p^2!=1`, and

```text
p has order exactly four and belongs to [G,G].       (11)
```

This excludes every ambient group `S_n x A` with `n<=5` and
`A` abelian. Its commutator subgroup lies in `A_n x {1}`, and
`A_n` has no element of order four for `n<=5`: such a permutation
would need a four-cycle, which is odd, with too few remaining
points for a disjoint transposition to change its parity.
Consequently adding central abelian factors cannot repair a
degree-at-most-five symmetric-group attempt at the strengthened
packet. Degree six is the first possible symmetric degree under
this test, since `(1234)(56)` has order four in `A_6`.

This is only a necessary condition for an exact model. It supplies
no model in degree six, no exclusion of larger finite groups, and
no approximate or normalized-HS gap for the strengthened packet.
