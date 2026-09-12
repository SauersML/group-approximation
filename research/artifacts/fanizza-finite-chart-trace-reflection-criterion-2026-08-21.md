# Fixed characteristic-zero charts reflect only an irreducible dimension vector

## The multiplicity-simplex formula

Let

```text
A = direct_sum_(j=1)^s M_(d_j)(C)                       (FTR1)
```

be a finite-dimensional C-star algebra, and let `e in A` be a projection.
Write `r_j=rank(e_j)` in the `j`th simple summand.  Every finite-dimensional
unital representation of `A` has the form

```text
pi_m = direct_sum_j (id_(M_(d_j)) tensor I_(m_j))       (FTR2)
```

for nonnegative integer multiplicities `m_j`, not all zero.  Therefore its
normalized matrix trace is

```text
tr(pi_m(e)) = (sum_j m_j r_j)/(sum_j m_j d_j).          (FTR3)
```

It follows immediately that `tr(pi_m(e))` is one constant `c` for every
finite-dimensional representation if and only if

```text
r_j/d_j = c                                             (FTR4)
```

for every simple sector.  A fixed finite chart can thus authenticate a
relative rank only when that rank is already constant in its irreducible
dimension vector.  A simple `M_k(C)` chart is the smallest positive example:
a rank-`a` projection always has normalized trace `a/k` in every
amplification.

This criterion includes any fixed two-idempotent overlap table, four-root
square, or shared-selector extension whose generated characteristic-zero
C-star algebra is finite dimensional.  Enlarging the table merely replaces
`A` by another finite direct sum and changes the finite list in `(FTR4)`.

There is a useful positive form.  Suppose the packet forces one faithful
multiplicity profile `m_j=L a_j`, where every `a_j>=1` and only the common
amplification `L` varies.  Put

```text
gamma_A=min_j a_j/(sum_i a_i d_i)>0.                    (FTR5)
```

Every nonzero projection in the represented algebra `pi_m(A)` then has
normalized trace at least `gamma_A`.  Hence, if a decoded Gram deficiency
`q=e-g` is authenticated as a projection in `pi_m(A)`,

```text
tr(q)<gamma_A  implies  q=0 and g=e.                    (FTR6)
```

The smallest nontrivial example is one simple `M_2(C)` packet, for which
`gamma_A=1/2`.  Its load-bearing hypothesis is that `q` lies in the algebra
coordinate `M_2 tensor 1`, not in the uncontrolled multiplicity coordinate
`1 tensor M_L`.

## Fullness is different from a nontrivial rational rank

Now let `g<=e` be projections in `A`.  In the notation above put
`q=e-g`.  If

```text
tr(pi(g)) = tr(pi(e))                                   (FTR7)
```

for every finite-dimensional representation `pi`, then apply `(FTR7)` to
each irreducible representation separately.  It gives `rank(q_j)=0` in
every summand, hence

```text
g=e in A.                                               (FTR8)
```

The same conclusion already follows from one faithful tracial state on
`A`, since faithfulness and `q>=0` turn `tau(q)=0` into `q=0`.

Consequently a fixed semisimple packet can lock a proper rational rank such
as `1/2`, and `(FTR6)` decodes fullness once the Gram deficiency is in the
algebra coordinate.  What its internal trace profile cannot do is
authenticate that coordinate localization.  If its fixed relations instead
make the Gram projection full in every sector, fullness is an algebraic
equality in the chart and is inherited by every representation.

## Application to the Fanizza compression

For the Fanizza target put

```text
X=(E-H)UE,              g=X^*X.                         (FTR9)
```

A fixed finite C-star chart containing exact projections `g<=E` can force
the trace equality needed for `g=E` only in the two ways described above:

1. it fixes a sector dimension vector with `rank(g_j)=rank(E_j)` in every
   active sector, in which case `g=E` already inside the chart; or
2. it leaves more than one sector ratio, in which case changing
   multiplicities changes the reflected rank and gives an exact escape.

The first option is useful only after the Gram has been localized in the
chart algebra; the finite trace table itself does not prove that
localization.  If equality is instead promoted to a universal group-algebra
identity, the canonical regular tracial firewall from
`fanizza-compressed-unitary-has-guarded-rank-floor` applies.  The second
option is multiplicity blindness.

Thus neither a two-projection Grassmannian table nor a fixed four-root
Steinberg square with one shared finite selector can be the missing decoder
merely by being a finite-dimensional characteristic-zero chart.  A fixed
chart can contribute the gap `gamma_A`, but one must still force the
deficiency into its algebra factor rather than its multiplicity commutant.
Otherwise the surviving mechanism must use data growing with the ambient
matrix coordinate, or an infinite/non-semisimple chart with a genuinely
finite-only multiplicity law.  This does not rule out an external
equivalence or endomorphism coupling; that separate route lies beyond this
finite-chart calculation.
