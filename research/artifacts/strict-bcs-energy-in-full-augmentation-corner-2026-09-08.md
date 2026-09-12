# A strict BCS energy bound suffices in the full augmentation corner

2026-09-08. The finite-subgroup corner endgame can consume one strict
energy inequality in the maximal group C-star algebra. It does not
require the displayed elements to satisfy every BCS relation exactly.
This gives another sufficient construction target; it neither constructs
that target nor proves that it is easier to construct. Like the exact
corner target, it already excludes hyperlinear hosts.

Fix the finite BCS `B` and its positive unitary matrix energy gap
`beta_rob` from `non-ce-bcs-has-robust-approximate-energy-gap`.
Every context has a fixed order. All commutators in the energy below
are additive matrix commutators.

## 1. A quantitative contraction version of the existing gap

For self-adjoint contractions `A_x` in a unital star algebra with
unit `e`, use the following finite relation list:

```text
r_x(A)=A_x^2-e,
r_(x,y)(A)=A_x A_y-A_y A_x,
f_(c,a)(A)=product_(x in U_c, fixed order)
                    (e+(-1)^(a_x) A_x)/2.
```

The commutator list includes the pairs from every context; the last
list includes its forbidden assignments. Put

```text
E_B(A)=sum_(all listed r) r(A)^*r(A),
C_B=2+32 M+sum_(forbidden (c,a)) |U_c|^2,
beta=beta_rob/C_B>0,                                  (1)
```

where `M` is the number of commutator terms, including any repetitions
across contexts. Then every finite-dimensional self-adjoint contraction
tuple satisfies

```text
tr_d(E_B(A))>=beta.                                   (2)
```

Here is a direct reduction to the existing unitary gap. Let
`S=sum_x ||A_x^2-I||_2^2`, and spectrally round each `A_x` to
the self-adjoint unitary `U_x=sign(A_x)`, choosing sign `+1` at
zero. The scalar inequality

```text
(1-|t|)^2 <= (1-t^2)^2          for -1<=t<=1
```

gives `||U_x-A_x||_2<=sqrt(S)` for each variable. Consequently
the additive commutator changes by at most `4sqrt(S)` in normalized
HS norm. Its squared norm after rounding is at most twice its old
squared norm plus `32S`.

An ordered forbidden product of length `l` changes by at most
`l sqrt(S)/2`: telescope its contractive factors. Its squared norm
after rounding is at most twice its old squared norm plus `l^2 S/2`.
The new involution defects are zero. On unitaries the additive and
multiplicative commutator defects have equal HS norms. Summing these
estimates gives

```text
E_rob(U)<=C_B tr_d(E_B(A)).                            (3)
```

The lower bound `E_rob(U)>=beta_rob` proves (2).

Inequality (2) also holds in every tracial matrix ultraproduct for
self-adjoint contractions. Such elements have self-adjoint contraction
lifts; bounded polynomial traces pass to their ultralimit. Thus (2)
holds for every Connes-embeddable tracial state on a unital C-star
algebra containing the tuple.

## 2. The strict-energy endgame

Let `G` be countable, let `K<=G` be finite and nontrivial, and put

```text
q=1-e_K,               e_K=|K|^-1 sum_(k in K) k.
```

Suppose self-adjoint contractions `a_x` in
`q C*_max(G) q`, with its unit `q`, obey

```text
E_B(a)<=c q              for some 0<=c<beta.           (4)
```

Then every homomorphism from `G` to a norm matrix corona kills `K`.
Indeed, extend any such homomorphism to a unital star homomorphism
from `C*_max(G)`. If the image `p` of `q` is nonzero, the corner
`pQp` has a unital map to a tracial matrix ultraproduct, by
`matrix-corona-projection-ideal-and-corner-calculus` and intrinsic
corner-rank normalization. Applying that trace to the images of `a_x`
gives both (2) and an upper bound `c`, contradicting (4).

Therefore the image of `q` is zero. The identities `k e_K=e_K`
then imply that every `k in K` maps to the identity. This is the
authentication argument of
`nonhyperlinear-finite-augmentation-corner-kills-mf`; it requires
neither normality of `K` nor centrality of `q`. In particular (4)
would prove that `G` is non-MF.

No compression of the whole group representation is made. Only
the displayed elements of the corner are mapped to a corner, so
there is no requirement that its projection commute with arbitrary
group generators.

## 3. A finite group-ring certificate is sufficient

One may seek all `a_x` in the finite-support corner `q C[G] q`.
For example, if `g_x` are involutions, the elements
`a_x=q g_x q` are automatically self-adjoint contractions.
The exact identity

```text
q-a_x^2=((1-q)g_x q)^*((1-q)g_x q)
```

certifies their contraction bound without assuming `[g_x,q]=0`.

More generally, finite group-ring identities of the form

```text
a_x=a_x^*,                   a_x=q a_x q,
q-a_x^2=sum_j y_(x,j)^* y_(x,j),
c q-E_B(a)=sum_j z_j^* z_j                             (5)
```

are sufficient, where all `y_(x,j),z_j` have finite support and
right support `q`. Positivity of squares in every C-star
representation makes (5) imply the hypotheses of Section 2.
Thus (5), together with a certified `c<beta`, is a finite
algebraic certificate target. No claim that every positive maximal
norm inequality admits the displayed sum-of-squares form is used.

## 4. Exact full C-star maps give finite-support strict inequalities

Suppose there is a unital star homomorphism

```text
Phi:A(B)->q C*_max(G) q.                              (6)
```

Its generator images are self-adjoint unitaries in the corner.
Approximate each in maximal norm by an element of `q C[G] q`,
take its self-adjoint part, and divide by `1+epsilon` when its
distance from the target is at most `epsilon`. This gives
finite-support self-adjoint contractions converging to those images
in maximal norm. Every relation polynomial in Section 1 vanishes
at the images of (6), so the energies of the approximating tuples
tend to zero in maximal norm. Positivity then gives (4), with any
fixed `c` strictly between zero and `beta`, once the approximation
is sufficiently close.

This does not promote a star homomorphism into a quotient of the full
group C-star algebra to (6). The images in (6) must lie inside the
actual corner retained by the group representation.

A single positive bound `c<beta` also does not itself construct
an exact map (6): its relation errors need not tend to zero.
Even a sequence with energy tending to zero in a fixed corner
directly produces a map only into that corner's norm ultrapower,
not necessarily into the corner. No equivalence between (4), (6),
and an exact algebraic group-ring map is asserted here.

## 5. This still excludes every hyperlinear host

The canonical group trace satisfies
`tau_G(q)=1-1/|K|>0`. If `G` were hyperlinear, the normalized
canonical trace on `qL(G)q` would be Connes embeddable. Restricting
it along `q C*_max(G) q -> qL(G)q` would give a CE trace on the
displayed tuple and hence the lower bound (2). This contradicts
(4). Therefore the strict-energy condition also implies that `G`
is nonhyperlinear.

This is the same host obstruction as for the exact algebraic corner
map. Allowing a strict energy inequality does not establish a route
inside known hyperlinear groups, does not evade the canonical trace,
and does not supply a new group. It changes the form of the missing
finite certificate while retaining that substantial construction
requirement. No property `(T)` or uniform invariant-vector estimate
for an infinite subgroup appears in the argument.
