# Strict Iwahori instability inside a single multiplicity stratum

Date: 2026-09-08.

The new assertion is local and strict: even inside one modular
generator-multiplicity stratum, a dimension-uniform Hilbert--Schmidt
neighborhood of compatible points admits no strict repair modulus.
The construction has an explicit flexible repair using at most twelve
additional dimensions. It is not a counterexample to the generalized
Iwahori question.

## 1. Conventions and the one analytic input

Put `Gamma=SL_2(Z[1/2])`. Fix the images of the two modular generating
pairs `(s_i,b_i)`, `i=1,2`, as a finite generating set `S` of `Gamma`.
Their central-positive representations satisfy `s_i^2=b_i^3=1`.
The finite Iwahori edge generators are fixed words in these pairs.
Write `||.||_F` for unnormalized Frobenius norm and `||.||_(2,N)`
for that norm divided by `sqrt(N)`.

Property `(T;FD)` supplies `kappa>0` such that, in every finite-dimensional
unitary representation without invariant vectors,

```text
max_(g in S) ||alpha(g)v-v|| >= kappa ||v||.             (ST1)
```

For a general representation, apply this inequality to the orthogonal
complement of its invariant vectors. In particular, any nonzero vector
with smaller relative displacement forces a nonzero invariant vector.
The set `S` can be used by expressing a fixed Kazhdan set as bounded
words in `S` and decreasing `kappa` by their maximum length.

This is the established `(T;FD)` input in
`sl2-s-arithmetic-pair-is-codense-kazhdan`, specialized to `p=2`.
The finite-dimensional gap and its local-intertwiner use are also
recorded in [Dogon--Vigdorovich, Sections 3--4](https://arxiv.org/html/2506.20843v2).
We use this gap only between honest finite-dimensional representations.
No gap for the approximate input pair is asserted.

## 2. Irreducibles with nearly uniform torsion spectra

For a prime `p>3`, let `rho_p` be the augmentation complement of the
permutation representation of `PSL_2(F_p)` on `P^1(F_p)`, pulled back
to `Gamma`. Its dimension is `p`.

The action is two-transitive: it is transitive, and the stabilizer of
infinity contains every translation of the affine line. Thus there are
exactly two orbits on ordered pairs. The permutation commutant has
dimension two, and the invariant constants have multiplicity one.
Complete reducibility then makes their complement irreducible.

Every nonidentity projective transformation has at most two fixed
points. Therefore

```text
Tr(rho_p(g)) = #Fix_(P^1(F_p))(g)-1 in {-1,0,1}         (ST2)
```

whenever `g` has nonidentity reduction. Both modular involutions and
both modular order-three generators, and their nonidentity powers,
have this property for `p>3`. Conjugating the second modular embedding
by its invertible rational diagonal matrix does not change their orders
modulo these primes.

If `U=rho_p(g)` and `g` has order `m=2` or `3` in the projective quotient,
Fourier inversion on the cyclic group gives its eigenvalue multiplicities:

```text
a_j = (p + sum_(l=1)^(m-1) zeta^(-jl) Tr(U^l))/m,
|a_j-p/m| <= (m-1)/m < 1.                              (ST3)
```

No Weil character estimate is needed.

## 3. Delete a bounded dimension and balance each torsion generator

Set

```text
r=12 floor((p-1)/12),   k=p-r,   1<=k<=12.
```

Choose any rank-`k` orthogonal projection `Q` in the space of `rho_p`,
put `P=1-Q`, and let `J:P C^p <- C^p` be the orthogonal coisometry.
We construct an exact order-`m` unitary `U_hat` on `P C^p` whose every
root multiplicity is `r/m` and for which

```text
||U_hat J-JU||_F <= 16.                               (ST4)
```

Start with the cyclic hull

```text
W = span {U^j Q C^p : 0<=j<m}.
```

It reduces `U`, contains `Q C^p`, and has dimension at most `mk`.
Its orthogonal complement lies in `P C^p`. For each root `zeta^j`,
let `c_j` be its multiplicity on `W^perp`. If `c_j>r/m`, add exactly
`c_j-r/m` vectors from that eigenspace to `W`. Since `c_j<=a_j`,
the number of added vectors is at most

```text
sum_j max(a_j-r/m,0) <= k+m.
```

Call the enlarged reducing space `W'`. It has dimension at most
`mk+k+m<=51`. On `(W')^perp` retain `U`. On `P C^p intersect W'`
choose root eigenvalues with multiplicities

```text
r/m - multiplicity_(zeta^j)(U|_(W')^perp).
```

These numbers are nonnegative and sum to `dim(W')-k`, exactly the
dimension to be filled. This defines `U_hat` and its required uniform
multiplicities. Both terms in `U_hat J-JU` agree on `(W')^perp`.
Their difference has operator norm at most two, and domain support
of dimension at most 51. Thus its Frobenius norm is at most
`2 sqrt(51)<16`, proving `(ST4)`.

Perform this construction separately for the four modular torsion
generators, using the same `P`. Each pair now satisfies `s_i^2=b_i^3=1`
exactly and hence defines a representation of `PSL_2(Z)=C_2*C_3`,
or a central-positive representation of `SL_2(Z)`.
Denote the resulting exact vertex pair on `C^r` by `psi_p`.

The separate cyclic hulls need not agree or reduce the other generator.
That causes no problem: the only within-vertex relations here are the
order-two and order-three relations. Iwahori compatibility is still
approximate and is estimated next.

For every word `w` of length `ell` in the four generators and inverses,
telescoping the rectangular intertwining relations gives

```text
||psi_p(w)J-Jrho_p(w)||_F <= 16 ell.                   (ST5)
```

The same bound holds for an inverse generator by multiplication with
the two unitary inverses. On an Iwahori relation the two corresponding
`rho_p` words agree. Subtract `(ST5)` for those words and use `JJ*=I_r`:
`||AJ||_F=||A||_F` for every operator `A` on `C^r`. Thus every edge
mismatch of `psi_p` has Frobenius norm bounded by an absolute constant
`C_edge`, depending only on the chosen fixed edge words.

## 4. Add a larger irreducible and count required dimensions

Let `q>p` be prime and let `sigma_q=rho_q` be the distinct irreducible
of dimension `q`. On `N=r+q` dimensions put

```text
phi_(p,q) = psi_p direct-sum sigma_q|_(the two vertices).
```

The second block is compatible, so

```text
def(phi_(p,q)) <= C_edge/sqrt(N).                      (ST6)
```

Let `tau:Gamma->U(N)` be any exact compatible candidate, with arbitrary
basis, and set

```text
t = max_(g in S) ||tau(g)-phi_(p,q)(g)||_(2,N).
```

Include `J` into the first block of `C^N` and call the resulting
map `J_p:C^p->C^N`. Then `||J_p||_F=sqrt(r)` and `||J_p||_op=1`.
For every generator, `(ST4)` gives

```text
||tau(g)J_p-J_p rho_p(g)||_F <= sqrt(N)t+16.           (ST7)
```

Let `I_q:C^q->C^N` include the second block. It satisfies

```text
||I_q||_F=sqrt(q),
||tau(g)I_q-I_q sigma_q(g)||_F <= sqrt(N)t.            (ST8)
```

Take `c=kappa/4` and `p` sufficiently large that `16<=kappa sqrt(r)/4`.
If `t<c sqrt(r/N)`, `(ST7)` has relative displacement less than
`kappa` in the genuine unitary representation
`Hom(C^p,C^N)` given by `X |-> tau(g)Xrho_p(g)*`.
Property `(T;FD)` forces a nonzero intertwiner. Since `rho_p` is
irreducible, it embeds into `tau`.

Likewise `(ST8)` has relative displacement less than `kappa`, because
`q>r`, and `sigma_q` embeds into `tau`. The two irreducibles have
different dimensions and are inequivalent; their invariant images in a
unitary representation are orthogonal. Hence

```text
N >= p+q > r+q=N,
```

a contradiction. We have proved

```text
D_N(phi_(p,q)) >= c sqrt(r/N).                        (ST9)
```

The argument compares rectangular exact-representation modules; it does
not assume that `tau` respects the original two-block decomposition.

## 5. An explicit compatible point in the same stratum

Let `lambda_3` be the twelve-dimensional regular representation of
`PSL_2(F_3)=A_4`, pulled back to `Gamma`. Each modular involution acts
as six disjoint two-cycles in the regular permutation basis; each
order-three generator acts as four disjoint three-cycles. The same
holds for the second modular vertex. Thus all order-two multiplicities
are six and all order-three multiplicities are four.

The compatible pair

```text
eta_(p,q) = lambda_3^(direct-sum r/12) direct-sum sigma_q
```

has exactly the same four generator multiplicity lists as `phi_(p,q)`.
Its generators differ from those of `phi_(p,q)` only on the first
`r` dimensions, with operator norm at most two. Consequently

```text
D_N(phi_(p,q)) <= D_str(phi_(p,q))
               <= d_2(phi_(p,q),eta_(p,q)) <= 2 sqrt(r/N).       (ST10)
```

In each fixed dimension the same-stratum compatible set is compact
and nonempty, so its distance is attained. The issue is not an absent
compatible stratum or a failure to supply a comparison point.

The same construction also gives an intrinsic stratum path of length
at most `2pi sqrt(r/N)`: conjugate each torsion generator on the first
`r`-block to its matched `eta` generator, using a skew-Hermitian logarithm
of operator norm at most `pi`, and perform the four conjugations
simultaneously. Each generator speed is at most `2pi sqrt(r/N)` in
normalized HS norm. The central-positive vertex relations remain exact.
Thus replacing the chord tube by its usual product-flag path metric
does not restore a uniform strict neighborhood.

We do not assert that a globally closest compatible point attaining
`D_N` has the same multiplicities. The supplied comparison and the
minimizer defining `D_str` do. Any claim that additionally requires
the unrestricted minimizer to stay in that stratum has that extra
hypothesis and is not literally refuted here without checking it.

## 6. No strict local modulus and no strict Holder germ

Fix `epsilon>0`. Choose a fixed `L>1` with `2/sqrt(1+L)<epsilon`.
For each sufficiently large prime `p`, Bertrand's postulate supplies
a prime `q` with `Lp<q<2Lp` (round the lower endpoint if necessary).
Then `(ST10)` places the pair within `epsilon` of a compatible point
in its own stratum, while `(ST9)` stays bounded below by a positive
constant depending on `L`, and `(ST6)` tends to zero. Therefore no
dimension-uniform strict modulus tending to zero can hold throughout
that neighborhood.

Alternatively choose `p log p<q<2p log p`. Then

```text
D_str(phi_(p,q)) -> 0,
D_N(phi_(p,q)) >= c'/sqrt(log p),
def(phi_(p,q)) <= C'/sqrt(p log p).
```

For every `alpha>0`,

```text
D_N(phi_(p,q))/def(phi_(p,q))^alpha
 >= c_alpha p^(alpha/2) (log p)^((alpha-1)/2) -> infinity.       (ST11)
```

The defect is nonzero because `(ST9)` excludes compatibility.
These are strict distances. In particular `(ST11)` is not a lower
bound on the generalized flexible distance.

## 7. The bounded flexible repair and the exact scope

The full exact representation `rho_p direct-sum sigma_q` has dimension
`N+k`, with `1<=k<=12`. Identify its space with the retained `r`-space,
the `q`-space, and the deleted `k`-space. For each generator, the top
rows of its difference from zero-padded `phi_(p,q)` are bounded by
`(ST4)`; the deleted rows have Frobenius norm `sqrt(k)`. Thus

```text
d_2^gen(phi_(p,q),rho_p direct-sum sigma_q)
 <= sqrt(16^2+12)/sqrt(N+k).                          (ST12)
```

This explicitly repairs the sequence with bounded additional dimension.
We claim an upper padding and distance bound, not an energy-paid converse
or a lower bound on the raw Iwahori defect.

The example explains what the modular chart theorem does and does not
provide. The pair and `eta_(p,q)` have the same multiplicities and small
HS distance, so controlled coordinates exist. Their operator sizes need
not be small, and a strict endpoint cannot absorb the missing dimensions
without a macroscopic change on the smaller irreducible block. Neither
uniform infinitesimal rigidity nor exact coordinate coverage supplies a
dimension-uniform strict HS tube theorem. An operator-small hypothesis or
a flexible dimension mechanism is additional mathematical content.

This refines the repository's earlier global strict/flexible separation;
the new ingredients are the irreducible dimension competition and an
explicit compatible comparison in the same torsion stratum. No claim of
literature novelty or a new non-hyperlinear group is made.
