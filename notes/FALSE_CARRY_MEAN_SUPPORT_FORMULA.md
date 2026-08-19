# Mean carry energy is exactly coordinate support

Date: 2026-08-11

## 1. Purpose

`FALSE_PAIRED_CARRY_ENERGY.md` reduces the metric hypothesis in the radical
phase construction to the mean ambient carry energy

`(1/|C|)sum_(c in C)delta(c)^2`.                      `(CMS1)`

This note evaluates `(CMS1)` exactly.  No closest-vector problem and no
enumeration of the discriminant subgroup is required.  Each ambient carry
coordinate is a finite character of `C`; its contribution depends only on
the order of that character.  In particular, mean carry energy `o(m)` is
equivalent to sublinear support among the `m` ambient relator coordinates.

## 2. The range discriminant inside the ambient torus

Let

`Lambda=Z^m subset R^m`,
`L=Lambda intersect W`, `K=Lambda intersect W^perp`,  `(CMS2)`

and let

`gamma:D_K=K^#/K -> D_L=L^#/L`                      `(CMS3)`

be the canonical discriminant gluing isomorphism.  There is a canonical
injective homomorphism

`iota:D_L->R^m/Lambda`, `a+L |-> a+Lambda`.          `(CMS4)`

Indeed it is well defined because `L subset Lambda`, and its kernel is

`L^# intersect Lambda=Lambda intersect W=L`.         `(CMS5)`

Fix a subgroup `C<=D_K` and put

`theta=iota compose gamma|_C:C->R^m/Lambda`.         `(CMS6)`

For `j=1,...,m`, let

`theta_j:C->R/Z`                                     `(CMS7)`

be the `j`-th coordinate character, and let

`n_j=|theta_j(C)|`.                                  `(CMS8)`

Thus `n_j=1` precisely when the `j`-th ambient carry coordinate vanishes on
the whole subgroup.

For `c in C`, choose `a_c in L^#` representing `gamma(c)`.  The exact carry
energy of `(PCE4)--(PCE5)` is

`delta(c)^2=dist(a_c,Lambda)^2`
`            =sum_(j=1)^m dist(theta_j(c),Z)^2`.      `(CMS9)`

The first equality is independent of the chosen representative, and the
second uses the product Euclidean metric of `Z^m`.

## 3. Exact mean formula

Define

`nu(1)=0`,                                            `(CMS10)`

and, for `n>=2`,

`nu(n)=(n^2-1)/(12n^2)` if `n` is odd,
`nu(n)=(n^2+2)/(12n^2)` if `n` is even.              `(CMS11)`

**Theorem 1 (coordinate-order formula).**  For every finite subgroup
`C<=D_K`,

`(1/|C|)sum_(c in C)delta(c)^2`
` =sum_(j=1)^m nu(n_j).`                              `(CMS12)`

**Proof.**  A homomorphism from the uniform finite group `C` pushes uniform
measure to uniform measure on its image.  The image of `theta_j` is the
unique cyclic subgroup of `R/Z` of order `n_j`.  Hence the `j`-th average in
`(CMS9)` is

`(1/n_j)sum_(k=0)^(n_j-1)dist(k/n_j,Z)^2`.            `(CMS13)`

For `n=2h+1`, pairing `k` with `n-k` gives

`(2/n^3)sum_(k=1)^h k^2=(n^2-1)/(12n^2).`            `(CMS14)`

For `n=2h`, the unpaired midpoint contributes `1/4`, and

`(1/n)(2sum_(k=1)^(h-1)(k/n)^2+1/4)`
` =(n^2+2)/(12n^2).`                                 `(CMS15)`

Sum over the coordinates in `(CMS9)`.  End proof.

The formula has uniform sharp bounds.  For every `n>=2`,

`2/27<=nu(n)<=1/8`.                                  `(CMS16)`

The lower endpoint occurs at `n=3`; the upper endpoint occurs at `n=2`.
Indeed the odd formula increases from `2/27` to `1/12`, while the even
formula decreases from `1/8` to `1/12`.

Define the ambient character support

`supp_L(C)=|{j:theta_j|_C is nontrivial}|`.           `(CMS17)`

**Corollary 2 (mean energy equals support up to universal constants).**

`(2/27)supp_L(C)`
` <=(1/|C|)sum_(c in C)delta(c)^2`
` <=(1/8)supp_L(C).`                                 `(CMS18)`

Consequently, for a sequence with ambient dimensions `m_n`,

`(1/|C_n|)sum_(c in C_n)delta_n(c)^2=o(m_n)`
` iff supp_(L,n)(C_n)=o(m_n).`                       `(CMS19)`

Thus the exact mean-carry hypothesis is combinatorial support sparsity, not
a metric covering-radius estimate.

## 4. Finite computation

Suppose `c_1,...,c_t` generate `C`, and choose rational range representatives

`a_i in L^#`, `a_i+L=gamma(c_i)`.                    `(CMS20)`

For each coordinate `j`, the image order `n_j` is the least positive integer
which kills all entries

`a_(1j),...,a_(tj) in Q/Z`;                          `(CMS21)`

equivalently it is the least common multiple of their reduced denominators.
Therefore `(CMS12)` is obtained by one rational/Smith pass through the
generator matrix `(a_(ij))`.  It does not require:

1. enumerating `C`;
2. finding shortest representatives in `K^#` or `L^#`;
3. solving any closest-vector problem.

The actual values of the orders refine the support count through `(CMS11)`,
but `(CMS18)` shows that their sizes are irrelevant to the asymptotic
`o(m)` question.

## 5. Consequence for the FALSE certificate

Combine Corollary 2 with Theorem 2 of
`FALSE_PAIRED_CARRY_ENERGY.md`.

**Corollary 3 (sparse-carry/dense-word certificate).**  Let `C_n<=D_(K,n)`
be discriminant subgroups in finite presentation charts with `m_n` relator
coordinates and `N_n` marked-word coordinates.  A hyperlinear nonsofic group
exists if:

1. the marked-word character is nontrivial on at least `alpha N_n`
   coordinates for one fixed `alpha>0`; and
2. the ambient range embedding of `C_n` is nontrivial on only `o(m_n)`
   relator coordinates.

For regular radical filling codes, deck transitivity and the nonisotropy
criterion of `FALSE_RADICAL_FILLING_DISCRIMINANT.md` supply item 1 from one
nonzero discriminant pairing.  The formerly metric item 2 is now the exact
support calculation `(CMS17)`.

In regular covers of one fixed presentation, deck symmetry actually
prevents item 2 for every nonzero invariant code: its support contains a
whole deck orbit, a fixed positive fraction of all relator coordinates.
See `FALSE_REGULAR_COVER_MEAN_ENERGY_NO_GO.md`.  Thus Corollary 3 is useful
only with a non-invariant/nonuniform choice, a growing number of coordinate
orbits, or a different chart architecture.

This exposes the finite structure a FALSE construction must seek: not a
uniform deck-invariant subgroup, but a low-carry subset or distribution whose
range-gluing coordinates are sparse and whose marked radical-word evaluation
is dense.  The joint support/energy profile, rather than the orders of the
discriminant classes, is the decisive data.
