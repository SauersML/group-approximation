# An explicit nine-word finite c-killing certificate in the Leavitt generators

2026-09-08. Handwritten root calculations and a finite presentation import.
No code, build, group enumeration, or numerical search is used. All word
definitions below are finite straight-line substitutions in four fixed
generators, rather than new abstract generators or existential lifts.

The result improves the existing nonconstructive finite-quotient witness
by identifying every word and excluding all exact finite-dimensional
unitary models retaining the marked coordinate cycle. The quantitative
normalized-HS problem remains open.

## 1. Explicit words in the marked free product

Let `R=L_(F_2)(1,2)`, with `t_i s_j=delta_ij` and
`s_0t_0+s_1t_1=1`. Put

```text
s=s_0,       t=t_0,       v=s_0t_1+s_1t_0.
```

Thus `ts=1`, `vs=s_1`, and `tv=t_1`. Write `x_ij(r)=I+rE_ij` and
let the marked map `q:P=C_3*C_2^3 -> EL_3(R)` send

```text
c -> (123),       b_1 -> x_12(s),
b_2 -> x_12(t),   b_3 -> x_12(v).
```

Use `[X,Y]=XYX^(-1)Y^(-1)` and `gamma(X)=c X c^(-1)`. Inside `P`,
define the existing shared words

```text
d=[b_2,gamma(b_1)],       h=gamma^2(d),
a=[d,h],                 e=gamma(d),
j=a e a^(-1),            r_*=j c j c.                 (1)
```

The new compiler is

```text
p_0=gamma(b_2),
q_0=gamma(j b_1 j^(-1)),

p_1=[j b_2 j^(-1), gamma^2(j b_3 j^(-1))],
q_1=[gamma^2(b_3), b_1],

X_0=p_0 q_0 p_0,        X_1=p_1 q_1 p_1,

A=j,                   B=X_0 X_1,       D=gamma^2(j). (2)
```

Here `q_0,q_1` name words and are unrelated to the marked homomorphism
`q`. Also `a` in (1) and `A` in (2) are different words. We use `D` for
the third Thompson generator to keep it distinct from the marked cycle
`c`. The order `B=X_0 X_1` is essential for the source convention.

For conjugations in the relator list below, use the different, explicitly
specified notation

```text
X^Y=Y^(-1) X Y.                                       (3)
```

Thus `gamma(X)` is not `X^c`. Integer powers, inverses, concatenation,
commutators, (1)--(3), and the finite list in Section 3 specify ordinary
finite words without any remaining choices.

## 2. Authenticate the compiler in the native Leavitt group

For pairwise distinct indices, direct matrix multiplication gives

```text
[x_ij(r),x_jk(z)]=x_ik(rz).
```

Conjugation by `c` cycles the roots as

```text
12 -> 23 -> 31 -> 12,
13 -> 21 -> 32 -> 13.
```

Consequently the native images of (1) are

```text
q(d)=x_13(ts)=x_13(1),    q(h)=x_32(1),
q(a)=x_12(1),            q(e)=x_21(1),
q(j)=x_12(1)x_21(1)x_12(1)=(12).                     (4)
```

The use of the third factor `x_12(1)` here is justified by characteristic
two, where each transvection is its own inverse. Hence `q(r_*)=1`.
Conjugation by this literal coordinate swap now authenticates (2):

```text
q(p_0)=x_23(t),                    q(q_0)=x_32(s),

q(p_1)=[x_21(t),x_13(v)]=x_23(tv)=x_23(t_1),
q(q_1)=[x_31(v),x_12(s)]=x_32(vs)=x_32(s_1).         (5)
```

These are three-distinct-index commutators. No opposite-root commutator
has been interpreted as multiplication of coefficients.

To read the prefix action, use the complete code `C=(00,01,1)`. The
relations for a complete code give the ring isomorphism

```text
Phi:M_3(R) -> R,
Phi((r_ij))=sum_(i,j) s_(C_i) r_ij t_(C_j).            (6)
```

Its inverse has entries `t_(C_i) r s_(C_j)`: both compositions are the
identity because `t_(C_i)s_(C_j)=delta_ij` and
`sum_i s_(C_i)t_(C_i)=1`.

For incomparable binary words `alpha,beta`, let

```text
P=s_alpha t_beta,    Q=s_beta t_alpha,
e_alpha=s_alpha t_alpha,    e_beta=s_beta t_beta.
```

Then `P^2=Q^2=0`, `PQ=e_alpha`, `QP=e_beta`, and `PQP=P`.
Expansion in characteristic two proves

```text
(1+P)(1+Q)(1+P)=1+e_alpha+e_beta+P+Q.                 (7)
```

The right side swaps the two prefix cylinders and fixes their complement.
For `epsilon=0,1`, (5)--(6) send `p_epsilon` to
`1+s_01 t_(1epsilon)` and `q_epsilon` to
`1+s_(1epsilon)t_01`. Formula (7) therefore gives

```text
Phi(q(X_0))=swap(01,10),
Phi(q(X_1))=swap(01,11),
Phi(q(A))=swap(00,01),
Phi(q(D))=swap(1,00).                                (8)
```

The last equality uses `gamma^2((12))=(31)` on the three code leaves.

The source writes prefix maps on the right. Its second generator is the
written product `swap(01,10) swap(01,11)`, sending `01 -> 10 -> 11 -> 01`
as a right action. To realize a right-acting map `g` by ordinary matrices
acting on columns, assign the left operator

```text
U_g e_x=e_(x g^(-1)).                                 (9)
```

Indeed `U_g U_h e_x=e_(x h^(-1)g^(-1))=U_(gh)e_x`, so this is a
homomorphism. Each swap is an involution and is unchanged by (9). Thus
the source's product is represented by the same written matrix product
`q(X_0)q(X_1)`, which acts on the left by the inverse three-cycle.
This proves that (2) uses the correct order; reversing `X_0,X_1` would
require changing the presentation substitution as well.

The prefix substitutions used here are identities of Leavitt units:
common refinements of their finite prefix tables give their products via
`t_i s_j=delta_ij` and `s_0t_0+s_1t_1=1`. No finite-dimensional
representation of the coefficient algebra is being assumed.

## 3. The full finite relator list

Bleak and Quick prove that Thompson's group `V` is presented by generators
`A,B,D` and the following eight relators. This is their Theorem 2.1,
equation (2.3), with the generator names changed. The source's definitions
immediately preceding that theorem specify exactly the right-action
generators authenticated above. We use their conjugation convention (3).
[Primary source: Bleak--Quick, arXiv:1511.02123, Section 2](https://arxiv.org/html/1511.02123#S2).

```text
rho_1 = A^2,

rho_2 = B^3,

rho_3 = (A B)^4,

rho_4 = D^(A D) A^(-1),

rho_5 = D^(-1)
        A^(B D A D A A^(B A))
        A^(B^(-1) D A D A A^(B^(-1) A)),

rho_6 = [ A^(B^(-1) D A D),
          A^(B^(-1) D A D A^B A^(B^(-1) A)) ],

rho_7 = [ A^(B D A D),
          A^(B^(-1) D A D A^B A^(B^(-1) A)) ],

rho_8 = [ A^(B D A^(B D A)),
          A^(B D A D A^B A^(B^(-1) A)) ].             (10)
```

Each expression `A^(...)` uses the complete parenthesized word as its
conjugating exponent. A commutator set equal to one has the same meaning
under either common commutator convention; (10) uses the convention in
Section 1. The displayed list is the theoretically proved presentation
(2.3), rather than the subsequently shortened presentation obtained using
Knuth--Bendix calculations.

Substitute the finite words (1)--(2) into (10), and set

```text
T_V={r_*,rho_1,rho_2,rho_3,rho_4,rho_5,rho_6,rho_7,rho_8}. (11)
```

Equations (4)--(9) and the presentation prove `T_V` is contained in
`ker q`. The added relations are native root-word identities compiled
through prefix permutations. Their sufficiency does not assert that
arbitrary models already possess a common additive coefficient receiver.

## 4. Exact finite-dimensional c-killing

Let `pi:P -> U(n)` kill (11). Since it kills (10), the finite presentation
supplies a homomorphism

```text
V -> U(n),     (A,B,D) -> (pi(A),pi(B),pi(D)).          (12)
```

The established claim
`thompson-v-has-no-nontrivial-fd-unitary-representation` makes (12)
trivial. For completeness, its mechanism is that `V` is infinite,
finitely generated and simple; a nontrivial finite-dimensional complex
representation would embed it into a finitely generated linear group.
Malcev residual finiteness then contradicts infinite simplicity.

In particular `pi(A)=pi(j)=I`. The remaining word `r_*=jcjc` gives
`pi(c)^2=I`. Since `c^3=1` already holds in `P`, this forces

```text
pi(c)=I.                                             (13)
```

For a finite target group, compose with its faithful unitary regular
representation and apply (13). No assumption of a literal coefficient
ring, elementary matrix realization, monomial model, or normalizer model
was made about `pi`.

## 5. Conservative explicit word bounds

Count letters in `c,c^(-1),b_1,b_2,b_3`. Because `c^3=1` in `P`, use
`gamma^2(W)=c^(-1)Wc`; thus either nontrivial cyclic conjugation adds
two letters. Inversion preserves length, a commutator adds at most
twice the sum of its input lengths, and `|X^Y| <= |X|+2|Y|`.
No cancellation is needed for the bounds below.

| Word | Length bound |
|---|---:|
| `d` | 8 |
| `h,e` | 10 |
| `a` | 36 |
| `j=A` | 82 |
| `D` | 84 |
| `p_0` | 3 |
| `q_0` | 167 |
| `p_1` | 664 |
| `q_1` | 8 |
| `X_0` | 173 |
| `X_1` | 1336 |
| `B` | 1509 |

For example, the two inputs defining `p_1` have length at most `165`
and `167`, giving `2(165+167)=664`. Applying the same rules to (10)
gives:

| Relator | Length bound |
|---|---:|
| `r_*` | 166 |
| `rho_1` | 164 |
| `rho_2` | 4527 |
| `rho_3` | 6364 |
| `rho_4` | 498 |
| `rho_5` | 20668 |
| `rho_6,rho_7` | 39856 |
| `rho_8` | 52920 |

To make the largest entries directly checkable, the two exponents in
`rho_5` have length at most `5105`, so its bound is
`84+2(82+2*5105)=20668`. The two commutator inputs of `rho_6` and
`rho_7` have bounds `3600` and `16328`. Those of `rho_8` have bounds
`10132` and `16328`; hence `2(10132+16328)=52920`.

This bounds literal expanded words without printing tens of thousands
of redundant letters. It does not give a degree bound for the separate
coefficient-ideal certificates used to define an exhaustion stage `T_m`.
Exhaustivity puts this finite set in some stage, or it can be adjoined
explicitly to every stage.

## 6. What this resolves and what remains

The existing theorem `mf-obstruction-gives-a-finite-c-killing-relation-set`
obtains an unnamed finite set by compactness and concerns finite targets.
Here (11) is a specified witness and excludes every exact
finite-dimensional unitary target retaining the coordinate cycle. The
proof imports the published presentation and the established exact
representation theorem for `V`; it is not a new proof of either input.

Adjoining (11) to the earlier coefficient packet excludes its exact
finite countermodels. In each fixed `24k` frozen regular-factor dimension,
the maximum relator defect for (11) has positive minimum: it is a
continuous function of the relative unitary on a compact space, and a
zero would contradict (13) because the prescribed `C_3` factor is
nontrivial.

The minima can still tend to zero as `k` grows. Exact finite-dimensional
invisibility does not by itself rule out normalized-HS approximate
representations in unbounded dimension. No uniform HS gap, stability
estimate for the Thompson presentation, or nonhyperlinearity conclusion
is established. In particular the common additive-receiver propagation
problem has been bypassed for exact finite models, not solved as a
quantitative extraction problem for arbitrary approximate models.
