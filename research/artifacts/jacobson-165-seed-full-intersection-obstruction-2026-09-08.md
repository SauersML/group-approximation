# A 165-dimensional seed passes the smaller overlap and fails the full one

2026-09-08. A natural representation profile with a 147-dimensional
rank-one root carrier passes the trace conditions and the complete
`L'=P_Q x K_P` overlap. It nevertheless fails on the larger
intersection `I=P intersect J`. One character of one stabilizer
already detects the failure. This excludes the specified seed; it
does not exclude all profiles of dimension 165 or all higher
dimensions.

All groups, root embeddings, and finite-character data are those of
[the coherent correction proof](jacobson-first-root-packet-coherent-rounding-2026-09-08.md)
and [the doubled-orbit obstruction](jacobson-double-rank-one-orbit-obstruction-2026-09-08.md).
No numerical search or project execution is used here.

## 1. A parity constraint from the full head parabolic

Let `S,S'` be the standard three-dimensional representation of
`P_Q~=S_4` and its sign twist. Let `T` be its two-dimensional
representation factoring through `P_Q/A_Q~=S_3`.

For a representation of the boundary packet `J`, split a rank-one
`E`-character fiber under its source `C_2` stabilizer into positive
and negative dimensions `m_+,m_-`. The target factor commutes
with this source `C_2`, so the dimensions are constant across
the target orbit. Over a fixed nonzero `A_Q` character, there
are exactly four rank-one `E` characters. They contribute
`4m_+` copies of `S` and `4m_-` copies of `S'`.

For the rank-two orbit, there are twelve characters over each
fixed nonzero `A_Q` character. Its source stabilizing involution
acts freely on these twelve characters: if it fixed a rank-two
map `lambda:F_2^3->F_2^2`, then its action on the image of
that surjective map would be trivial. Hence its positive and
negative dimensions are both `6m_2`, regardless of the action
inside the rank-two fiber of dimension `m_2`. Therefore every
representation of `J` has head multiplicities

```text
mult_S =4m_+ +6m_2,
mult_S'=4m_- +6m_2.                                 (1)
```

In particular both are even. This already rejects the tentative
156-dimensional profile

```text
(rho_0)_Q tensor Ind_(S_4)^G(S)_P
  direct-sum sigma_3,Q tensor sigma_3,P:
```

its `S,S'` multiplicities are 21 and 3. Here `rho_0` is
the seven-point representation and `sigma_3` is either
three-dimensional irreducible of `G`.

## 2. The next profile and the two different P fibers

Write `s` for the sign character of a target `S_4`, and
`t_2` for its two-dimensional irreducible. Set

```text
V=Ind_(S_4)^G(S),
V=chi_6 + chi_7 + chi_8,
dim(V)=21,
V|K=4*1+3*sgn+7*tau.
```

Consider the `F` representation

```text
F_seed=(rho_0)_Q tensor V_P
         direct-sum chi_6,Q tensor sigma_3,P.        (2)
```

Its dimension is `147+18=165`. The first summand is the
nontrivial part of a rank-one `N` orbit with fiber dimension
three. The second is `N`-trivial. The head negative rank is
`42+6=48`, matching the root negative rank `16*3=48`.
The trace difference of the braid involutions is zero: the first
summand contributes `4*1=4` to `trace(c)-trace(b)` and the
second contributes `4*(-1)=-4`.

There are two distinct target `S_4` fiber representations
giving the same carrier in (2):

```text
psi=S,
psi=t_2+s.                                         (3)
```

Both induce to `V`, since `Ind(t_2)=chi_6+chi_8` and
`Ind(s)=chi_7`. These are the only three-dimensional target
fibers inducing to `V`: enumerate sums of linear characters,
`t_2` plus a linear character, and the two three-dimensional
irreducibles. Their induced irreducible decompositions distinguish
all remaining choices. The head fiber must be trivial: for a
rank-one fiber of total dimension three its minimum head negative
rank is 42, while any nontrivial head stabilizer constituent raises
that rank by at least 14, to at least 56. For a single head sign
or two-dimensional constituent the increase is 14; a
three-dimensional head constituent raises it by at least 28.
These bounds follow from the induced involution traces in the
preceding finite-character calculations. They exceed the total
head negative rank 48 in (2). Thus (3) exhausts the `P` fibers
for this rank-one carrier. In particular one must not infer a
unique `P` extension from its restriction to `F`.

Let `R=sigma_3|K=sgn+tau`, and let `v=V|K`. Using
`rho_0|P_Q=2*1+T+S` and `chi_6|P_Q=1+T+S`, the full
restriction of (2) to the smaller overlap is

```text
F_seed|L'=1 tensor (2v+R)
            + T tensor (v+R)
            + S tensor (v+R).                      (4)
```

Its `S,S'` multiplicities are 24 and zero. Equation (1) thus
forces `m_2=0`, `m_-=0`, `m_+=6` in any matching `J`
representation. The boundary rank-one fiber is a six-dimensional
target `S_4` representation `chi`, with trivial source action.

## 3. The smaller overlap is genuinely feasible

For a target `S_4` representation `chi`, its rank-one boundary
module restricts to `L'` as

```text
(1+T) tensor A(chi) + S tensor B(chi).                (5)
```

The first term comes from the three target covectors satisfying
`f(e_2)=0`; their stabilizing involution belongs to the normal
four-group of `S_4`. Thus `A(chi)` is induction of that
involution restriction from `C_2` to `K~=S_3`. The remaining
four covectors consist of one fixed covector and an orbit of
three; in the latter orbit the stabilizing involution is a
transposition of `S_4`. This gives

```text
target irrep       A(chi)                  B(chi)
1                  1+tau                  2*1+tau
s                  1+tau                  2*sgn+tau
t_2                2*1+2*tau              1+sgn+3*tau
S                  1+2*sgn+3*tau          3*1+sgn+4*tau
S'                 1+2*sgn+3*tau          1+3*sgn+4*tau.
```

Equation (4) requires

```text
B(chi)=v+R=4*1+4*sgn+8*tau.                          (6)
```

Solving the three coefficient equations in this table, with
`dim(chi)=6`, gives precisely four possibilities:

```text
chi_0=1+s+2*t_2,
chi_1=s+t_2+S,
chi_2=1+t_2+S',
chi_3=S+S'.                                         (7)
```

For an explicit enumeration, put `p=mult_S+mult_S'`.
The standard coefficient and dimension equations give
`mult_(t_2)=2-p` and `mult_1+mult_s=2-p`, so
`p=0,1,2`; the difference of the trivial and sign coefficients
then gives exactly (7).

The first choice has `A(chi_0)=6*1+6*tau`, leaving the
impossible negative trivial multiplicity in
`v+R-A(chi_0)=-2*1+4*sgn+2*tau`. The other three choices
really do extend across the whole smaller overlap. For `chi_1`
or `chi_2`, put `Y=2*sigma_3`; for `chi_3`, put `Y=chi_6`.
Then

```text
Y|K=v+R-A(chi),
dim(Y)=6.
```

Take the `J` rank-one orbit with the indicated fiber `chi`
and add the `E`-trivial representation

```text
1_Q tensor V_*  direct-sum (1_Q+tau_Q) tensor Y_*.   (8)
```

Its dimension is `21+3*6=39`, while the rank-one orbit has
dimension 126. Equations (5), (6), and (8) reproduce all three
head types in (4). Thus this is an exact character match on
`L'`, not merely equality of two traces or one fixed-space rank.

## 4. A nonzero N_0 fiber distinguishes the full intersection

Now use

```text
I=N_0 semidirect L',
N_0=Mat_({1,3} x {1,3})(F_2)_add.
```

Choose the rank-one `N_0` character with head plane vector
`e_1` and tail plane covector `e_1^*`. Its stabilizer contains

```text
z=x_31,P.
```

An isomorphism of the two representations on `I` would give
the same trace of `z` on this character's spectral subspace.
That subspace has dimension twelve on both sides, but the traces
are different.

On the `P` side, this character has four rank-one lifts,

```text
head vector:    e_1+b e_2,
tail covector:  e_1^*+a e_2^*,       a,b in F_2.
```

Each has the three-dimensional fiber `psi` from (3). The
tail involution `z` fixes all four characters. For `a=0`,
it belongs to the normal four-group of the covector stabilizer
`S_4`. For `a=1`, it belongs to that stabilizer but lies
outside its normal four-group, so it is a transposition there.
For example, a normal-four-group transvection in a covector
stabilizer has that covector as its defining linear functional;
`z` has functional `e_1^*`, not `e_1^*+e_2^*`.
The character-space trace on the `P` side is therefore

```text
2*(psi(double transposition)+psi(transposition))
 =0       if psi=S,
 =4       if psi=t_2+s.                              (9)
```

On the `J` side there are two lifts, the shifted target
covectors `e_1^*` and `e_1^*+e_2^*`, each with its
six-dimensional fiber `chi`. The same class distinction for
`z` applies. The corresponding trace is

```text
chi(double transposition)+chi(transposition)
 =6       for chi_0,
 =2       for chi_1 or chi_2,
 =-2      for chi_3.                                (10)
```

Neither value in (9) occurs in (10). This contradicts the
necessary character equality on the stabilizer. The `N`-trivial
18-dimensional summand in (2), and all `E`-trivial summands in
(8), contribute nothing to this nonzero `N_0` spectral subspace.

## 5. Scope of the exclusion

The seed (2) therefore cannot extend to coherently glued exact
`P,J`, for either of its target fibers (3), despite the exact
smaller-overlap matches in Section 3. Arbitrary additional
head-trivial, `N`-trivial spectators do not repair the obstruction:
they change neither the nontrivial head types fixing (6) nor the
nonzero `N_0` character-space traces (9)--(10).

This calculation does not check or solve the mixed braid and TS
relations. It excludes this proposed finite-packet seed before
those questions arise. Other rank-one fiber-three profiles, other
root orbits, and a uniform non-MF obstruction remain unresolved.
