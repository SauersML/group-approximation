# A realizable cancellation rectangle requiring eighth-root phases

Handwritten exact example, 2026-09-07. This separates two cancellation
tests; it is not a counterexample to direct finiteness.

Let G=C4=<u | u^4=1>. Over F2 put

    B=[u^2]+[u^3]+[1],       A=[1]+[u]+[u^2].

Index the rows of B by i=0,1,2 in the displayed order and the columns
of A by j=0,1,2. Their multiplication rectangle is

|       | 1 | u | u^2 |
| ----- | - | - | --- |
| u^2   | u^2 | u^3 | 1 |
| u^3   | u^3 | 1 | u |
| 1     | 1 | u | u^2 |

Keep (2,0) as the pivot. Pair the other cells as

    e1: (0,0) -- (2,2),
    e2: (0,1) -- (1,0),
    e3: (0,2) -- (1,1),
    e4: (1,2) -- (2,1).

Each pair has equal group labels. All row labels are distinct, as are
all column labels. Thus BA=1. Since G is abelian, AB=1 as well.

## Real signs cannot cancel this pairing

Write a proposed row sign as (-1)^r_i and a proposed column sign as
(-1)^c_j, with r_i,c_j in F2. Each paired cell must have the opposite
sign to its partner. The equations for e1,e2,e4 are respectively

    r0+c0+r2+c2 = 1,
    r0+c1+r1+c0 = 1,
    r1+c2+r2+c1 = 1.

Their sum is 0=1. Hence no assignment of real signs can cancel all
four pairs, whether or not the pivot is normalized.

## The integer pairing vectors have no dependency

Orient the pairs from the first displayed cell to the second and put

    v_e = row_i + col_j - row_k - col_l.

Every such vector has total row coordinate zero and total column
coordinate zero. Removing coordinates row_0 and col_0 identifies
this rank-four lattice with Z^4. In coordinates
(row_1,row_2,col_1,col_2), the four vectors form the rows of

    M = [  0 -1  0 -1 ]
        [ -1  0  1  0 ]
        [ -1  0 -1  1 ]
        [  1 -1 -1  1 ].

The determinant is 4. For an explicit manual check, perform, in order,
R4 <- R4-R1, R3 <- R3-R2, and R4 <- R4+R2. The result is

        [  0 -1  0 -1 ]
        [ -1  0  1  0 ]
        [  0  0 -2  1 ]
        [  0  0  0  2 ],

whose diagonal block determinants are -1 and -4. Consequently every
integer relation sum_e n_e v_e=0 is trivial. In particular, there is
no odd-sum integer relation, despite the odd binary dependency above.

## Eighth roots give exact cancellation and are necessary

Let zeta be a primitive eighth root of unity. Give the rows phases

    (1,zeta,zeta^2)

and the columns phases

    (1,zeta^5,zeta^2).

The exponent rectangle, modulo 8, is

    [ 0 5 2 ]
    [ 1 6 3 ]
    [ 2 7 4 ].

The paired exponents differ by 4, so every pair cancels over
Z[zeta]. The surviving pivot has phase zeta^2. Multiplying every row
phase by zeta^(-2) normalizes that pivot and gives

    B_tilde = zeta^(-2)[u^2]+zeta^(-1)[u^3]+[1],
    A_tilde = [1]+zeta^5[u]+zeta^2[u^2],
    B_tilde A_tilde = A_tilde B_tilde = 1.

The homomorphism Z[zeta] -> F2 given by zeta -> 1 reduces these
elements to B and A.

Fourth roots cannot work for this fixed pairing. Indeed set the row
and column phases at indices 0 to 1, using the two independent scalar
normalizations, and write the remaining phase exponents additively as
x=row_1, y=row_2, p=col_1, q=col_2 in R/Z. The four cancellation
equations read

    -y-q=1/2,   -x+p=1/2,
    -x-p+q=1/2,  x-y-p+q=1/2.

The middle two give p=x+1/2 and q=2x. The first gives y=-2x-1/2.
Substitution into the last gives 4x=1/2 modulo 1. Hence x has order
8, which is impossible if all phases are fourth roots. The displayed
eighth roots attain the minimum possible phase order.

## The matching presentation itself is exactly C4

This is also an example at the level of a universal normalized
matching presentation, with no hidden extra relations. Normalize the
pivot by making its row and column labels both 1. Call the remaining
rows x,y and the remaining columns u,v. The four paired products
impose

    x=v,   xu=y,   xv=yu,   yv=u.

The first three equations give v=x, y=xu, and x=u^2. The fourth then
gives u^5=u, or u^4=1. Conversely x=u^2, y=u^3, v=u^2 satisfy all
four matching equations whenever u^4=1. Thus the normalized universal
group is C4, and its specified support labels remain distinct.

The example shows that testing only real-sign assignments discards
an exact characteristic-zero cancellation lift already on a valid
3-by-3 inverse rectangle. Allowing higher 2-power roots is a strictly
stronger filter; it still does not prove that every possible matching
admits such phases.

## A different pivot in the same inverse rectangle forbids every phase lift

Keep exactly the same support sets, now ordered as rows (1,u^2,u^3)
and columns (1,u^2,u). The product table, checked using u^4=1, is

|       | 1 | u^2 | u |
| ----- | - | --- | - |
| 1     | 1 | u^2 | u |
| u^2   | u^2 | 1 | u^3 |
| u^3   | u^3 | u | 1 |

Choose (2,2) as the pivot and pair the remaining cells as

    f1: (0,0) -- (1,1),
    f2: (1,2) -- (2,0),
    f3: (2,1) -- (0,2),
    f4: (0,1) -- (1,0).

All four pairs again have equal group labels. The pivot has label 1,
so this is another exact cancellation certificate for the same
identity BA=AB=1 over F2. Relative to the first construction, the
surviving identity term has changed from the product 1 times 1 to the
product u^3 times u.

With the displayed orientations, the first three integer pairing
vectors satisfy

    w1 = row_0+col_0-row_1-col_1,
    w2 = row_1+col_2-row_2-col_0,
    w3 = row_2+col_1-row_0-col_2,
    w1+w2+w3 = 0.

This is an integer dependency with odd coefficient sum 3. If nonzero
row scalars a_i and column scalars b_j cancelled each of those three
pairs over a field of characteristic different from 2, then

    (a0*b0)/(a1*b1) = -1,
    (a1*b2)/(a2*b0) = -1,
    (a2*b1)/(a0*b2) = -1.

Multiplying gives 1=-1. Hence this matching admits no such phase
assignment, even with arbitrary nonzero complex scalars. Normalizing
the pivot cannot change the displayed zero relation or remove the
contradiction.

Thus an odd integer dependency obstructs the prescribed cancellation
lift, but does not establish a direct-finiteness defect. The very same
inverse supports admit both the successful eighth-root matching and
this obstructed matching. A search using the filter must distinguish
failure for a selected matching from failure for every matching and
every choice of the surviving identity cell.

## A noncommuting central-sign lift succeeds on the obstructed matching

The same obstructed matching does admit a lift once its row and
column coefficients are allowed to be group elements with a central
sign. Normalize at its chosen pivot (2,2). For original row labels
a_i and column labels b_j with a_2 b_2=1, the replacement

    a_i -> a_i a_2^(-1),     b_j -> a_2 b_j

preserves every product and makes row_2=col_2=1. Write the normalized
rows as (x,y,1) and columns as (p,q,1). Introduce a central element J
with J^2=1, and require paired products to differ by J. The four
equations are exactly

    f1: xp = J yq,
    f2: y  = J p,
    f3: q  = J x,
    f4: xq = J yp.

The surviving pivot product is 1. Eliminating p=Jy and q=Jx gives

    H = <x,y,J | J^2=1, J central, yx=Jxy, y^2=Jx^2>.

This presentation does not collapse J to 1. Indeed let

    D8 = <r,s | r^4=1, s^2=1, srs=r^(-1)>

be the dihedral group of order eight. Assign

    J=r^2,   x=s,   y=r,   p=r^3,   q=r^2 s.

The four signed equations can be checked directly:

    xp = s r^3 = r s = r^2 r (r^2 s) = J yq,
    y  = r = r^2 r^3 = J p,
    q  = r^2 s = J x,
    xq = s r^2 s = r^2 = r^2 r r^3 = J yp.

Here J=r^2 is nonidentity and central. Thus D8 is an explicit witness
that J survives in H, although scalar coefficients were impossible.

This witness can also be read as an exact cancellation lift of the
original C4 rectangle, with its two roles kept separate. The original
normalized C4 labels are rows (u,u^3,1) and columns (u^3,u,1).
In the nonzero coefficient ring

    K = Z[D8]/([r^2]+1),

put

    B_hat = [s] [u] + [r] [u^3] + [1],
    A_hat = [r^3] [u^3] + [r^2 s] [u] + [1]

as elements of K[C4]. In these expressions each first bracket is a
coefficient from D8 and each second bracket is an external group
label from C4; these two factors commute by the definition of an
ordinary group ring. The ring K is nonzero: as an abelian group it is
free on representatives of the four cosets of <r^2> in D8, with the
other representative in each coset identified with its negative.
The displayed four signed equations cancel the four pairs, so

    B_hat A_hat = 1.

The coefficient homomorphism K -> F2 that sends every D8 element to
1 is well-defined and reduces this identity to the original inverse
identity with its supports normalized at the new pivot. No map
D8 -> C4 is asserted or needed. Equivalently, the universal group H
has a quotient map to the original normalized C4 labels given by
J->1, x->u, y->u^3; D8 is a separate quotient witnessing J!=1.

The normalization at the pivot is essential when setting generators
equal to 1. Imposing row_0=col_0=1 as well as the distinct pivot
relation would add relations that are not part of this construction.
This explicit lift therefore strictly extends the scalar-phase test
on one and the same matching, rather than changing the matching to
the earlier successful one.

## Every admissible 3-by-3 matching has a surviving central sign

There is a short exhaustive classification at this support size,
requiring no computation. A matching of group products with distinct
row labels and distinct column labels cannot pair two cells in one
row or in one column: group cancellation would identify two support
labels. Call a matching obeying these restrictions admissible.

Move the pivot to (2,2), normalize its row and column to 1, and write
the remaining rectangle as

    [ a=xp   b=xq   c=x ]
    [ d=yp   e=yq   f=y ]
    [ g=p    h=q     1  ].

Call a,b,d,e internal cells and c,f,g,h boundary cells. If t is the
number of boundary-boundary pairs, then it also equals the number of
internal-internal pairs: after making either kind of pair, every
remaining pair uses one cell of each kind. Consequently t is 0, 1,
or 2.

There are exactly eight admissible matchings, forming three orbits
under independent swaps of the first two rows and first two columns:

* For t=0 all pairs are mixed. The allowed mixed-edge graph is the
  eight-cycle a-f-b-g-e-c-d-h-a, which has exactly two perfect
  matchings. A row swap interchanges them.
* For t=1 the internal pair is either (a,e) or (b,d). If it is (a,e),
  the remaining pairs must be either (b,f),(d,h),(c,g) or
  (b,g),(d,c),(f,h). A simultaneous row and column swap exchanges
  these two choices. A row swap exchanges the two choices of
  internal pair, giving four matchings in one orbit.
* For t=2 the internal pairs are (a,e),(b,d). The boundary pairs are
  either (c,g),(f,h) or (c,h),(f,g). A row swap exchanges these two
  matchings.

Each of the three representatives below admits a central sign
J!=1. Since J is central of order two, reversing a displayed pair
does not change its signed relation. Row and column permutations
also preserve existence of a signed realization.

### No boundary-boundary pairs: a cyclic group of order ten

Take pairs (a,f),(b,g),(e,c),(d,h). Their signed equations are

    xp=Jy,   xq=Jp,   yq=Jx,   yp=Jq.

The first, second, and fourth equations give

    p=Jx^(-2),   y=x^(-1),   q=x^(-3).

The third then gives x^5=J. Thus the signed universal presentation
is cyclic of order ten, with J=x^5. Conversely, in C10=<z>, the
assignment

    J=z^5,   x=z,   y=z^9,   p=z^3,   q=z^7

satisfies the four equations: the two sides of the equations are,
respectively, z^4, z^8, z^6, and z^2. In particular J!=1.

### One boundary-boundary pair: a cyclic group of order eight

Take pairs (a,e),(b,f),(d,h),(c,g). The equations are

    xp=Jyq,   xq=Jy,   yp=Jq,   x=Jp.

They give p=Jx, q=yx, x=y^2, and y^4=J. Hence the signed universal
presentation is cyclic of order eight. Conversely, in C8=<z>, set

    J=z^4,   x=z^2,   y=z,   p=z^6,   q=z^3.

The four pairs of products agree as prescribed: both sides are,
respectively, 1, z^5, z^7, and z^2. Again J!=1.

### Two boundary-boundary pairs: the dihedral witness

Take pairs (a,e),(b,d),(c,h),(f,g). Their equations are

    xp=Jyq,   xq=Jyp,   x=Jq,   y=Jp.

These are the same four equations as in the preceding D8 section,
with two of them reordered or reversed. The assignment
J=r^2, x=s, y=r, p=r^3, q=r^2s therefore provides the already
verified witness with J!=1.

This proves sign survival for all eight admissible 3-by-3 matchings,
including every such matching of actual distinct group supports.
Combined with the central-sign cancellation theorem, it gives a
self-contained proof that an F2 inverse pair with both supports of
size three cannot have a nonzero reverse defect. This bounded
classification is a worked certificate for the lifting method; it
does not extend the enumeration or its conclusion to larger support
rectangles, and no novelty claim for the support-three consequence
is intended.
