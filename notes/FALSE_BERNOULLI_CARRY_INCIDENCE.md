# Sparse Bernoulli carry codes give a finite FALSE certificate

Date: 2026-08-11

## 1. Purpose

Uniform averaging over a nonzero deck-invariant discriminant subgroup has
linear carry energy; see `FALSE_REGULAR_COVER_MEAN_ENERGY_NO_GO.md`.  In the
two-torsion sector there is a precise nonuniform replacement.

Choose binary generators of the discriminant code.  If every ambient
relator coordinate depends on at most `a_n` generators, while a positive
fraction of the marked radical-word coordinates depend on at least `b_n`
generators, then

`a_n/b_n->0`                                          `(BCI1)`

is enough to prove FALSE.  Sample the generators independently with a
vanishing Bernoulli density.  Relator parity is then rare, but the much
denser word parity remains asymptotically unbiased.

This is an exact finite binary-incidence criterion.  It replaces the
impossible uniform subgroup mean by a low-energy probability distribution.

## 2. Binary carry and word matrices

Retain the phase-relator setup of
`FALSE_DISCRIMINANT_PHASE_INSTABILITY.md`.  At stage `n`, let

`D_(K,n)=K_n^#/K_n`                                   `(BCI2)`

be the cycle discriminant group, with exact carry map

`theta_n=iota_n compose gamma_n:`
` D_(K,n)->(R/Z)^(m_n)`,                              `(BCI3)`

and marked radical-word map

`chi_(w,n):D_(K,n)->(R/Z)^(N_n)`.                    `(BCI4)`

Let

`T_n:F_2^(d_n)->D_(K,n)`                              `(BCI5)`

be any homomorphism.  Since the source has exponent two, both composites
`theta_n T_n` and `chi_(w,n)T_n` take values in `{0,1/2}` coordinatewise.
There are therefore binary matrices

`A_n in F_2^(m_n times d_n)`,
`B_n in F_2^(N_n times d_n)`                          `(BCI6)`

such that

`theta_n(T_n v)=A_n v/2 mod Z^(m_n)`,
`chi_(w,n)(T_n v)=B_n v/2 mod Z^(N_n)`.              `(BCI7)`

Write `wt(row)` for binary Hamming weight and define

`a_n=max_(1<=j<=m_n)wt((A_n)_(j,*))`.                `(BCI8)`

Assume that for some fixed `alpha>0`, at least `alpha N_n` rows of `B_n`
have weight at least `b_n`.

For `c=T_nv`, the exact carry energy `(PCE4)` and marked chordal energy
`(DPI24c)` become

`delta_n(c)^2=(1/4)wt(A_n v)`,
`mu_(w,n)(c)^2=(4/N_n)wt(B_n v)`.                    `(BCI9)`

The first identity is the coordinate torus formula `(CMS9)` specialized to
order two; the second follows because an odd word parity has phase `-1`.

## 3. Bernoulli incidence theorem

**Theorem 1 (sparse-carry/dense-word incidence criterion).**  Suppose the
binary data `(BCI5)--(BCI8)` satisfy

`a_n/b_n->0`.                                         `(BCI10)`

Then there are `v_n in F_2^(d_n)` such that

`delta_n(T_n v_n)^2/m_n->0`                          `(BCI11)`

and

`liminf_n mu_(w,n)(T_n v_n)^2>=alpha`.               `(BCI12)`

Consequently a hyperlinear nonsofic group exists.

**Proof.**  The word-row hypothesis implies `b_n>0`.  If `a_n=0`, then
`theta_n T_n=0`; injectivity of `theta_n` gives `T_n=0`, contradicting the
existence of a positive-weight word row.  Thus eventually `a_n,b_n>=1`.

Set

`p_n=1/sqrt(a_n b_n)`.                                `(BCI13)`

After discarding finitely many stages, `0<p_n<=1/2`, and

`p_n a_n=sqrt(a_n/b_n)->0`,
`p_n b_n=sqrt(b_n/a_n)->infinity`.                    `(BCI14)`

Choose the coordinates of `v in F_2^(d_n)` independently, with
`P[v_i=1]=p_n`.

For a binary row of weight `k`, the probability of odd parity is

`q_p(k)=(1-(1-2p)^k)/2`.                              `(BCI15)`

For a carry row, `q_(p_n)(k)<=p_n k<=p_n a_n`.  Therefore `(BCI9)` gives

`E[delta_n(T_n v)^2/m_n]`
` <=(1/4)p_n a_n->0`.                                 `(BCI16)`

For each of the `alpha N_n` dense word rows,

`q_(p_n)(k)>= (1-exp(-2p_n b_n))/2->1/2`.            `(BCI17)`

Hence

`E[mu_(w,n)(T_n v)^2]>=2alpha-o(1)`.                 `(BCI18)`

Put `epsilon_n=E[delta_n(T_n v)^2/m_n]`.  Markov's inequality shows that
the event

`delta_n(T_n v)^2/m_n>sqrt(epsilon_n)`                `(BCI19)`

has probability at most `sqrt(epsilon_n)`.  Marked energy is bounded by
four, so deleting this event lowers `(BCI18)` by at most
`4sqrt(epsilon_n)`.  For all large `n`, some remaining `v_n` has marked
energy at least `alpha` and carry energy at most `sqrt(epsilon_n)m_n`.
This proves `(BCI11)--(BCI12)`.

The exact carry energy is the normalized relator defect of the canonical
phase table.  Thus `(BCI11)` gives an asymptotic unitary representation,
while `(BCI12)` retains the fixed word `w in Rad_sof(H)`.  The marked
discriminant criterion `(DPI24)--(DPI26)` produces a hyperlinear image which
cannot be sofic.  End proof.

The theorem does not require `T_n` to be injective.  Redundant binary
generators merely define a different Bernoulli distribution on its image.

## 4. Deck-equivariant interpretation

For a regular cover, take the columns of `T_n` to be selected deck
translates of two-torsion filling classes.  Then:

1. `a_n` is the largest number of selected filling generators whose
   range-gluing images touch one relator coordinate;
2. `b_n` is a lower bound on the number of selected generators detected by
   a typical marked radical-word coordinate.

The load-bearing target is therefore the incidence separation

`local carry degree / marked word degree ->0`.         `(BCI20)`

This is compatible with deck symmetry.  Uniform averaging failed because
it activated every binary generator with density `1/2`; Theorem 1 uses the
intermediate density `(BCI13)`, which tends to zero slowly enough that a
dense word row still sees many active generators.

The criterion is also robust under bounded carry overlap.  If `a_n=O(1)`,
it is enough that the marked row degree `b_n->infinity`.  Conversely, a
bounded marked degree cannot work through this Bernoulli mechanism: any
density making carry parity rare also makes those word parities rare.

## 5. Next finite calculation

For the radical filling code, form a binary generator matrix for a
two-torsion subcode and compute two incidence profiles:

`row weights of A_n`  versus  `row weights of B_n`.    `(BCI21)`

No discriminant enumeration, lattice CVP, or uniform character average is
needed.  A certified gap `(BCI10)` proves FALSE.  If deck symmetry forces
the two row degrees to remain comparable, then this entire sparse-Bernoulli
route is closed and the next search must use higher-order phases or a
non-product distribution.
