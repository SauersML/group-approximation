# Two exact short-packet countermodels in frozen dimension 48

2026-09-08. This is a hand calculation with seven-point permutations
and finite-dimensional representations. No script or search is used.
The stronger example disproves the implication even after adjoining
`B^3` and `(AB)^4` to the two small anchors. Neither example decides
derivability from the full eight-word Thompson packet.

## 1. The marked assignment and the shared words

Products act on the left, with the rightmost factor acting first,
and `[X,Y]=XYX^(-1)Y^(-1)`. On the seven letters `a,b,c,d,e,f,g`,
put

```text
C=(a b c)(d f e),
B_1=B_2=Y=(b d)(f g),
B_3=Z=(a c).                                       (1)
```

The marked involutions commute, and `C` has order three. Thus
(1) defines a homomorphism `P=C_3*C_2^3 -> S_7`; injectivity on
the second factor is not needed at this stage. It will be restored,
with its regular profile, in Section 3.

For clarity use hats on the lower-case compiler words, which otherwise
collide with the seven letter labels. The
[native compiler](leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md)
is

```text
gamma(W)=C W C^(-1),
dhat=[B_2,gamma(B_1)],        hhat=gamma^2(dhat),
ahat=[dhat,hhat],            ehat=gamma(dhat),
A=ahat ehat ahat^(-1),       D=gamma^2(A),
uhat=[B_2,gamma(B_3)],       what=[gamma^2(B_1),ahat],
p_0=gamma(B_2),             q_0=what,
p_1=[ehat,uhat],            q_1=[gamma^2(B_3),B_1],
X_0=p_0 q_0 p_0,            X_1=p_1 q_1 p_1,
B=X_0 X_1.                                         (2)
```

The final occurrence of `p_1` in `X_1` is not its inverse.
Since `C^3=1`, `gamma^2(W)=C^(-1)WC`.

## 2. Exact cycle replay

The constant part is the
[seven-point core](leavitt-seven-cell-centralizer-completion-2026-09-08.md).
All required values can also be checked directly from (1):

```text
gamma(Y)=(c f)(e g),       gamma^2(Y)=(a e)(d g),
dhat=(c e)(f g),           hhat=(b f)(d g),
ahat=Y,                   ehat=(a d)(e g),
A=(a b)(e f),             AC=(b c)(d e),
q_0=(b f)(d g),           X_0=(b c)(d e).            (3)
```

In particular `dhat^2=(AC)^2=1`. The only new marked assignment
in (1) gives

```text
gamma(Z)=(a b),           gamma^2(Z)=(b c),
uhat=[Y,(a b)]=(a d)(a b)=(a b d).                  (4)
```

Conjugation by `ehat=(a d)(e g)` reverses this three-cycle.
Consequently

```text
p_1=[ehat,uhat]=uhat^(-2)=uhat=(a b d),
q_1=[(b c),Y]=(c d)(b d)=(b c d),
X_1=p_1 q_1 p_1=(a c)(b d),
B=X_0 X_1=(a b e d c).                             (5)
```

Thus the two small anchor relators vanish, but `p_1^2` does not.
It follows already from this finite homomorphism that

```text
p_1^2 is not in <<d^2,(Ac)^2>> inside P.             (6)
```

This uses the same occurrences of all the `B_i` throughout (2).
In particular it respects the exact centralization consequences
of `d^2=1`; those consequences cannot force `p_1^2=1`.

## 3. Exact regular profiles in dimension 48

Let `pi` be the permutation representation of `S_7` on the
six-dimensional subspace

```text
W={ (z_a,...,z_g) in C^7 : sum_x z_x=0 }.
```

This is a unitary representation for the inherited inner product,
and its trace is `tr(pi(sigma))=number_of_fixed_letters(sigma)-1`.
Let `E=C_2^3`, let `e_1,e_2,e_3` be its standard generators,
and let `lambda_E` be its eight-dimensional left regular representation.
Define on `W tensor l^2(E)`

```text
mathcal C=pi(C) tensor I_8,
mathcal B_i=pi(B_i) tensor lambda_E(e_i).            (7)
```

These are exact commuting marked involutions together with an exact
marked cycle of order three. The dimension is `6*8=48=24*2`.

The two three-cycles and one fixed letter in `C` give eigenvalue
multiplicities `(3,2,2)` on `C^7`, for eigenvalues `(1,omega,omega^2)`.
Removing the constant vectors leaves `(2,2,2)` on `W`. Thus
`mathcal C` has multiplicities `(16,16,16)`, exactly sixteen copies
of the regular representation of `C_3`.

For every nonzero `x in E`, its image under (7) has the form

```text
pi(B_1^(x_1) B_2^(x_2) B_3^(x_3)) tensor lambda_E(x).
```

Its trace is zero because `lambda_E(x)` has trace zero. The identity
has trace 48. Equivalently, every character of the marked `E` occurs
with multiplicity six: its character projection has trace `48/8=6`.
This is six copies of the regular representation of `E`, and in
particular the marked second factor is faithful.

These are precisely the two profiles in the frozen `24k` problem
at `k=2`. Conjugating (7) to put `mathcal C` in the prescribed
first-factor basis, the marked `mathcal B_i` are simultaneously
unitarily conjugate to the prescribed second-factor generators.
Hence (7) supplies a relative-unitary model of that actual finite
target; it does not require the profiles to be relaxed.

## 4. Anchor and nonanchor defects

The extra `E` labels in (7) are central, so every commutator in
(2) has trivial label. The same holds for `A` and `X_1`; in `X_0`
the two occurrences of `p_0` cancel its label. Therefore the
compiled words `d,A,p_1,B` evaluate to their `pi` images tensored
with `I_8`, and the anchor defects remain exactly zero.

For normalized trace `tau` and normalized Hilbert--Schmidt norm,
every unitary `T` satisfies

```text
||T-I||_2^2=2-2 Re tau(T).
```

The three-cycle `p_1^2` fixes four letters, so

```text
tau(p_1^2)=(4-1)/6=1/2,
||p_1^2-I||_2=1.                                   (8)
```

The nontrivial power `B^3` of the five-cycle in (5) fixes two
letters, giving

```text
tau(B^3)=(2-1)/6=1/6,
||B^3-I||_2=sqrt(5/3).                             (9)
```

Taking any positive number `r` of direct sums preserves all these
normalized defects and yields the regular profiles at `k=2r`.
Thus no implication or estimate forcing the `p_1^2` defect to zero
can use only the two small anchor defects and the exact marked
factor profiles, even along unbounded frozen dimensions.

## 5. A second choice also satisfies the next two short rows

Keep `C,B_1,B_2` fixed and replace only the last marked generator by

```text
Z_+=(c e)(b d)=Y dhat.                             (10)
```

It is again an involution commuting with `Y`. It is the member
`v=(c e), z=(b d)` of the finite centralizer family with `v`
acting on the fixed letters `{a,c,e}` and `z` on `{b,d,f,g}`.
No enumeration of that family is needed to verify this member.
The constant words (3) are unchanged. Direct substitution in (2)
gives

```text
gamma(Z_+)=(a d)(c f),    gamma^2(Z_+)=(a e)(b f),
uhat=(a d b)(c f g),      p_1=(a d b)(c g e),
q_1=(b f)(d g),          X_1=(a e g c b d f),
B=(a d f)(b e g),        AB=(a d e g)(b f).         (11)
```

For example, conjugating the two three-cycles of `uhat` by
`ehat=(a d)(e g)` gives `(a b d)(c f e)`. Multiplication by
`uhat^(-1)=(a b d)(c g f)` gives the stated `p_1`.
Thus `p_1` still has order three, but now

```text
dhat^2=(AC)^2=B^3=(AB)^4=1.
```

An explicit remaining failure is the native certificate's row

```text
rho_5=D^(-1) A^K A^L,
K=B D A D A A^(B A),
L=B^(-1) D A D A A^(B^(-1) A),
where T^W=W^(-1) T W.                              (12)
```

Here `D=(a c)(d f)` and `D A D A=C^(-1)`. Put
`E_0=(a d)(e g)` and `T_0=(d f)(b g)`. The relevant conjugations
are

```text
A^(B A)=E_0,              A^(B^(-1) A)=T_0,
K=B C^(-1) E_0,           L=B^(-1) C^(-1) T_0,
A^K=(c f)(e g),           A^L=(d f)(b g),
rho_5=(a c d)(b e g).                              (13)
```

For instance `K^(-1)=E_0 C B^(-1)` sends the pairs `(a,b)`
and `(e,f)` of `A` to `(g,e)` and `(c,f)`, respectively.
Likewise `L^(-1)=T_0 C B` sends them to `(d,f)` and `(b,g)`.
This checks the conjugation orientation in (13) directly.

Apply the same construction (7), now with `B_3=Z_+`. Its proof
of both exact regular profiles is unchanged. Both `p_1^2` and
`rho_5` are products of two disjoint three-cycles, so each fixes
one of the seven letters. Their normalized trace on `W` is
`(1-1)/6=0`. Hence this dimension-48 model satisfies

```text
||d^2-I||_2=||(AC)^2-I||_2=||B^3-I||_2=||(AB)^4-I||_2=0,
||p_1^2-I||_2=||rho_5-I||_2=sqrt(2).                (14)
```

Direct sums retain (14) at every `k=2r`. In particular the finite
model proves the stronger nonmembership

```text
p_1^2 is not in <<d^2,(Ac)^2,B^3,(AB)^4>> inside P. (15)
```

The first example distinguishes the two-anchor condition from this
four-row condition: its failed `B^3` row is now repaired, while the
compiled square remains nontrivial and `rho_5` explicitly fails.

## 6. Boundary of the counterexamples

The native certificate identifies `p_1` with `x_23(t_1)` in
characteristic two. Its square is a true native kernel word, with
unreduced length at most 72. Statements (6) and (15) determine that this
word requires more than the indicated short rows as abstract relations.

The first example fails `rho_2=B^3` by (9); the stronger example
fails `rho_5` by (14). Thus neither is a model of `T_8`, establishes
independence from `T_8`, or contradicts the exact finite-dimensional
`c`-killing theorem for that larger packet. Neither constructs
a Thompson completion or disproves a uniform gap for `T_8`.
