# A relative-commutant wall forces flexible HS-instability

Date: 2026-08-12

## 1. Outcome

Let `Gamma<G` be a property-`(T)` compressor pair.  Thus there are

```text
t in G,       t Gamma t^(-1)<=Gamma,
gamma in Gamma,       h=t^(-1) gamma t.                (WFI1)
```

The one-map endpoint in `FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md` asks for
normalized-Hilbert--Schmidt asymptotic homomorphisms

```text
pi_n:G->U(d_n)                                         (WFI2)
```

and walls `v_n in U(d_n)` such that

```text
||[v_n,pi_n(s)]||_2 -> 0       for every s in Gamma,   (WFI3)
liminf_n ||[v_n,pi_n(h)]||_2 > 0.                      (WFI4)
```

Here `[x,y]=xy-yx`; replacing it by the group commutator changes none of the
conclusions.

The main result of this note is:

**Theorem 1.**  If `(WFI2)--(WFI4)` hold, then `G` is not flexibly
Hilbert--Schmidt stable.

This is stronger than the observation that the particular maps `pi_n` cannot
be corrected in their original dimensions.  Even correction by genuine
representations after adding `o(d_n)` dimensions is impossible.

For the fully framed Kun--Thom pair, a wall satisfying `(WFI2)--(WFI4)` would
therefore do two things simultaneously:

1. give a hyperlinear nonsofic image of the radical double; and
2. exhibit an explicit residually finite Kazhdan group which is not flexibly
   HS-stable.

The theorem puts the FALSE endpoint directly on the stability boundary
studied by Dogon, *Flexible Hilbert--Schmidt stability versus hyperlinearity
for property (T) groups*, Math. Z. 305 (2023), Article 58, and by
Dogon--Vigdorovich, [arXiv:2506.20843](https://arxiv.org/abs/2506.20843).
Their implications start from flexible stability; Theorem 1 says that the
relative wall necessarily lives on the opposite side of that dichotomy.

## 2. Flexible correction and leakage from the old corner

Assume for contradiction that `G` is flexibly HS-stable.  Applied to
`(WFI2)`, flexible stability gives dimensions `D_n>=d_n`, projections `p_n`
onto the first `d_n` coordinates, and exact representations

```text
rho_n:G->U(D_n),       D_n/d_n->1,                     (WFI5)
```

such that, for every fixed `g in G`,

```text
||p_n rho_n(g) p_n-pi_n(g)||_(2,d_n)->0.               (WFI6)
```

Put `q_n=1-p_n`.  The off-diagonal corners of `rho_n(g)` have vanishing
normalized HS norm.  Indeed, with `A_n=p_n rho_n(g)p_n`, unitarity gives

```text
||q_n rho_n(g)p_n||_F^2=d_n-||A_n||_F^2.               (WFI7)
```

Since `(WFI6)` says that `A_n` is `o(sqrt(d_n))` away in Frobenius norm from
the unitary `pi_n(g)`, the right side of `(WFI7)` is `o(d_n)`.  As
`D_n/d_n->1`,

```text
||q_n rho_n(g)p_n||_(2,D_n)->0,
||p_n rho_n(g)q_n||_(2,D_n)->0.                        (WFI8)
```

The second assertion follows either by the same calculation or by applying
the first one to `g^(-1)`.

Extend the wall by the identity on the added coordinates:

```text
V_n=v_n directSum 1_(q_n) in U(D_n).                   (WFI9)
```

Writing `rho_n(g)` in `p_n directSum q_n` blocks, equations
`(WFI3)`, `(WFI6)`, and `(WFI8)` imply

```text
max_(s in S) ||[V_n,rho_n(s)]||_(2,D_n)->0             (WFI10)
```

for every fixed finite `S subset Gamma`.  On the old-old block this is just
`[v_n,A_n]`, which is close to `[v_n,pi_n(s)]`; the other two nonzero blocks
are bounded by the leakages in `(WFI8)`.

## 3. Property `(T)` propagates agreement through the compressor

Fix a finite Kazhdan set `S subset Gamma` and constant `kappa>0` in the
spectral-gap form used by `FINITE_REPRESENTATION_MATCHING_BARRIER.md`.  Apply
that note's finite-representation matching theorem with

```text
pi=sigma=rho_n,       U=V_n.                           (WFI11)
```

It gives

```text
||rho_n(h)-V_n rho_n(h)V_n^*||_(2,D_n)
 <= (2/kappa) max_(s in S)
       ||rho_n(s)-V_n rho_n(s)V_n^*||_(2,D_n).         (WFI12)
```

By `(WFI10)`, the right side tends to zero.

Compress `(WFI12)` by `p_n`.  Its old-old block is

```text
A_(h,n)-v_n A_(h,n)v_n^*,
A_(h,n)=p_n rho_n(h)p_n.                               (WFI13)
```

Equation `(WFI6)` and unitary invariance show that `(WFI13)` is
`o(1)`-close in normalized `d_n`-HS norm to

```text
pi_n(h)-v_n pi_n(h)v_n^*.                              (WFI14)
```

Moreover `d_n/D_n->1`, so convergence of the full `D_n`-normalized norm in
`(WFI12)` forces the `d_n`-normalized norm of `(WFI13)` to converge to zero.
Consequently `(WFI14)` converges to zero, contradicting `(WFI4)`.  This proves
Theorem 1.

## 4. Exact scope

The argument uses all three hypotheses below:

* `Gamma` has property `(T)`, to convert almost agreement on a fixed Kazhdan
  set into agreement at the predecessor `h`;
* `h=t^(-1) gamma t` comes from a genuine compressor relation;
* the correction is by **finite-dimensional** representations with only
  `o(d_n)` padding.

It does not show that arbitrary failure of flexible HS-stability creates a
relative wall, and it does not rule out weak ucp corrections into genuinely
infinite-dimensional representations.  The finite-dimension equality behind
the compressor matching theorem is exactly what makes `(WFI12)` work.

The infinite-dimensional escape is explicit.  Let `lambda_(G/Gamma)` be the
quasi-regular representation on `ell^2(G/Gamma)`, let `p_Gamma` be the
rank-one projection onto the basis vector `delta_Gamma`, and put

```text
V=1-2p_Gamma.                                           (WFI15)
```

Every element of `Gamma` fixes `delta_Gamma`; since the orthogonal complement
of a fixed vector is invariant as well, `p_Gamma` and `V` commute with
`lambda_(G/Gamma)(Gamma)`.  In the strict pair used here one chooses
`h notin Gamma` (and any wall satisfying `(WFI3)--(WFI4)` forces this), so

```text
lambda_(G/Gamma)(h)delta_Gamma=delta_(h Gamma)
                         perpendicular delta_Gamma.
```

Consequently

```text
[V,lambda_(G/Gamma)(h)]!=0.                            (WFI16)
```

Thus even a finite-rank operator in the relative commutant of an
infinite-dimensional representation can detect the inverse predecessor.
There is no compact-operator analogue of the finite-dimensional bicommutant
collapse.  A weak ucp dilation may place precisely this shift sector outside
the finite compression, so Theorem 1 cannot be promoted from flexible
HS-stability to weak ucp-stability by the leakage argument alone.

Thus the implication is one-way but sharp for the present endpoint:

```text
relative wall  =>  flexible HS-instability of G.       (WFI17)
```

The new stability papers do not construct the wall.  They identify its
necessary nature: it must be a nonliftable, nonamenable, multi-directional
matrix sector.  Dogon--Vidick removes the one-axis lamplighter sector, while
Burton--Chaudkhari--Juschenko--Muliarchyk additionally permutationizes every
trace-separated amenable sector.
