# Audit: fixed-replication infinite-dimensional selection barrier

## Verdict

The corrected weighted obstruction is green.  The initially tempting
fixed-c projection sequence is invalid under half slack and is explicitly
excluded from the proof.

For every fixed m>=1, the half-slack family contains the fibres

    M_(2m),       p rank one,       a_lambda=lambda p.

Their topology is V_m(C^(2m)), their first nonzero homotopy group is

    pi_(2m+1)=Z,

and an explicit generator has Hilbert-sum radius at most

    2sqrt(lambda)/sqrt(2m).

As lambda tends to zero, essential spheres shrink in one fixed degree.
Therefore this fixed-m family is not equi-LC^(2m+1), under either the
degreewise or a stronger uniform-in-degree convention, and its nonzero
values are not globally C-infinity.

## Tuple and topology check

For x in the unit sphere of

    span{e_1,e_(m+1),...,e_(2m)},

the tuple

    sqrt(lambda) x e_1^*,
    sqrt(lambda) e_2 e_1^*, ...,
    sqrt(lambda) e_m e_1^*

has common weighted initial square lambda p and orthogonal ranges.  Its
polar frame is (x,e_2,...,e_m).  The forget-first-vector fibration has
this S^(2m+1) as fibre and V_(m-1)(C^(2m)) as base.  The base is
(2m+2)-connected, so the sphere is a generator, not merely a candidate.

Only the first tuple coordinate moves.  Normalized trace therefore gives

    d_2=sqrt(lambda/(2m))||x-e_1||,

which proves the stated radius.  The repository's weighted-copy
hypotheses impose no norm-one condition or uniform spectral lower bound,
so every a_lambda with lambda>0 is allowed.

A norm-one robustness check is also available.  In M_(4m), use a
rank-two support with weight p_1+lambda p_2.  Half slack is equality.
Vary one low-eigenvalue column and fix the other 2m-1 columns.  This gives
the generator in degree 4m+1 with radius at most
2sqrt(lambda)/sqrt(4m).  Thus the phenomenon is not created solely by
allowing the norm of the whole weight to vanish.

Strict half slack is covered by the rank-one construction in M_(2m+1).
The first obstruction is then in degree 2m+3 and has radius at most
2sqrt(lambda/(2m+1)).

## Quantifier firewall

If rank(p)=d, total source rank is md.  With n=md+c, half slack says
md<=c.  Thus fixed m,c cannot coexist with d,n tending to infinity.
The invalid fixed-c projection argument must not be used.

The valid projection sequence n=2md has c=md and shrinking normalized
spheres, but their degree 2md+1 grows.  It only excludes a modulus common
to all degrees.  It does not contradict the positive theorem, whose
modulus may depend on each fixed degree.

## Scope

The result blocks the straightforward continuation which fixes a finite
replication number and applies a Michael-type selection theorem requiring
C-infinity/equi-LC-infinity values over an arbitrary-dimensional base.
It does not disprove STW Problem XXII, produce a bundle without a
selection, or rule out a telescope, an increasing-replication
skeletonwise construction, or another trace argument.

The finite-dimensional theorem is untouched.  For each fixed D it chooses
m>=ceil((D-1)/2) and invokes only sphere degree D-1, within the sharp
matrix range.

An independent hostile audit found the fixed-c projection proposal red,
checked the corrected tuple, fibration, normalized metric, half-slack and
strict-half-slack variants, and returned green only with the scope above.
