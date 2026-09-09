# Exterior kernels must be purely periodic and asymmetric

Date: 2026-09-08. Exact support reduction, without computation.
This does not prove that a full exterior kernel exists or that
the full exterior map is injective. The remaining possible
kernels are asymmetric tensors on finite periodic cores.

Use the two simultaneous candidates and the proved natural
injectivity from
[the scalar-conjugate artifact](kaplansky-two-sided-scalar-conjugate-natural-injections-2026-09-08.md).
Write

```
a=[[1,s_0],[t_0,0]],       b=[[1,s_1],[t_1,0]],
H_z=a+m_z^-1 b m_z,       z=omega or omega^2.
```

The complete exterior source map of `diag(H_z,b)` is
equivalent to the genuine simultaneous chart candidate by
the invertible changes already established there. Both `a,b`
are units, and `H_z` is injective on the full natural free
boundary module over `F_2` and `F_4`.

## The full source equations

Let `B_4` be the free `F_4` vector space on actual infinite
binary tails. Parametrize the full source by tensors `(X,Y)`
through `k_+,k_-`. Define

```
A=omega^2+s_0+t_0,       B=omega+omega^2 s_0+t_0,
C=omega^2+s_1+t_1,       D=omega+omega^2 s_1+t_1,

A_z=A+C,
B_z=B+z^2D.
```

The two projected target coordinates are

```
F_z,+(X,Y)=alt((C tensor A_z)X
                  +(D^sigma tensor B_z^sigma)Y),

F_z,-(X,Y)=alt((D tensor B_z)X
                  +(C^sigma tensor A_z^sigma)Y).     (1)
```

The source tensors are arbitrary; no flip symmetry is assumed
in the support reduction below.

For a tail `xi`, let `X_row,xi` be its coefficient vector in
the second tensor factor, and `X_col,xi` its coefficient
vector in the first tensor factor. Define the corresponding
vectors for `Y` in the same way. Let `F` be the finite union
of all basis tails appearing in either factor of `X` or `Y`.

The two character matrices used in the contractions are

```
M_b=[[C,omega D^sigma],[omega^2D,C^sigma]],

M_H=[[A_z,omega B_z^sigma],[omega^2B_z,A_z^sigma]].
```

They satisfy

```
M_b=diag(1,omega^2) b_character diag(1,omega),
M_H=diag(1,omega^2) H_z,character diag(1,omega).
```

Thus `M_b` is invertible and `M_H` is injective.

## Removing every nonperiodic tail from a full kernel

Assume `(X,Y)` is a kernel of (1). Consider any aperiodic
tail-equivalence class represented in `F`. Use the well-defined
integer height from the scalar-conjugate artifact, and choose
`xi` of maximal height in the intersection of that class with
`F`.

Alternatively, in an eventually periodic class, suppose `F`
contains a tail of positive preperiod depth. Choose `xi` of
maximal positive depth in that class. The following argument
works identically in both cases.

The tails

```
alpha=0xi,       beta=1xi
```

are outside `F`. Any tail obtained by prepending another digit
to either of them has height or positive depth two larger
than that of `xi`, and is outside `F` as well.

First contract each target exterior coordinate at the basis
tail `alpha`. No vector in the image of `b` applied to the
source support can contain `alpha`: `b` only creates prefix
`1`, while constants and deletions cannot reach this new
prefix-`0` tail. In the second tensor factor, `alpha` can
therefore arise only from the `s_0` creator of `H_z`, acting
on the column indexed by `xi`.

The resulting two contraction vectors are exactly

```
C X_col,xi+omega D^sigma Y_col,xi,
omega^2D X_col,xi+C^sigma Y_col,xi.
```

Neither vector has an `alpha` coefficient. Thus exterior
contraction loses no diagonal term, and the zero target gives

```
M_b (X_col,xi,Y_col,xi)=0.
```

Invertibility of `M_b` proves that both columns vanish.

Now contract the targets at `beta`. Contributions from the
second factor of (1) have disappeared, since their only
possible creator input would be the now-vanished `xi`
columns. The remaining contraction vectors are

```
A_z X_row,xi+omega B_z^sigma Y_row,xi,
omega^2B_z X_row,xi+A_z^sigma Y_row,xi.
```

These vectors have no `beta` coefficient. A constant or
deletion contribution would require a tail outside `F`; a
creator contribution would require a `xi` coefficient in a
row vector, which the vanished `xi` columns exclude. Hence

```
M_H (X_row,xi,Y_row,xi)=0.
```

Natural injectivity of `H_z` forces both rows to vanish. This
contradicts the choice of `xi` in the union of the source
supports.

The argument is class by class. Other tail classes cannot
create `alpha` or `beta`, but their possible entries in the
column and row vectors are still killed by the full matrices
`M_b` and `M_H`. It therefore also covers tensors mixing an
aperiodic class with an eventually periodic class.

**Support conclusion.** Every full kernel of (1) is supported
entirely on purely periodic tails. No positive preperiod and
no aperiodic tail can occur in either source factor.

This proof uses contractions of the full operator. It does
not infer the conclusion from a formal leading-creator
filtration on periodic tails.

## Exact necessary equations on periodic cores

Enlarge a finite purely periodic source support to the finite
union `F` of its complete periodic cores. Let `S` denote
deletion of the first digit on a core. It is a permutation of
`F`. Each tail `xi` has a unique preceding bit: the first bit
of `S^-1 xi`.

If the preceding bit of `xi` is `1`, the tail `0xi` is
outside `F` and outside the image of `b` on `F`. The first
contraction argument above therefore still applies, giving

```
X_col,xi=Y_col,xi=0
  whenever the preceding bit of xi is 1.            (2)
```

Thus second-factor support lies only on core tails whose
preceding bit is zero.

For a tail with preceding bit zero, `beta=1xi` is outside
the core. Contracting (1) at `beta` gives the exact relation

```
M_H (X_row,xi,Y_row,xi)
  +M_b(z) (X_col,xi,Y_col,xi)=0,                     (3)

M_b(z)=[[C,omega z D^sigma],
        [omega^2 z^2D,C^sigma]].
```

Here

```
M_b(z)=diag(1,omega^2 z^2)
          b_character diag(1,omega z)
```

is invertible. The possible diagonal `beta` coefficient in
the contraction cancels automatically. In the plus coordinate
it occurs twice with coefficient
`X_(xi,xi)+omega^2 zY_(xi,xi)`; the minus coordinate has the
same paired cancellation. Thus (3) is an equality of full
vectors, not merely an equality modulo the line spanned by
`beta`.

These are necessary equations for the full kernel. The
remaining target coefficients on the periodic cores have not
been eliminated here.

## The full map is injective on flip-symmetric sources

Suppose additionally that `tau X=X` and `tau Y=Y`. By the
support conclusion, it suffices to consider periodic cores.
For preceding-bit-one tails, (2) kills rows as well as columns
by symmetry. At each remaining tail, rows equal columns, so
(3) becomes

```
(M_H+M_b(z))(X_row,xi,Y_row,xi)=0.
```

The terms involving `b` cancel, leaving

```
M_H+M_b(z)
  =[[A,omega B^sigma],[omega^2B,A^sigma]]
  =diag(1,omega^2) a_character diag(1,omega).
```

This matrix is invertible. All remaining rows vanish, and
therefore `X=Y=0`.

**Symmetric-source conclusion.** The complete map (1) is
injective on the subspace where both source tensors are
flip-symmetric. On that subspace the additional diagonal
term `E_(z^-1) Psi_b D_z` vanishes, so the same injectivity
statement also holds for the original map `Phi_g`.

This excludes a global kernel lying wholly in the symmetric
leading-cancellation subspace. It does not exclude a general
asymmetric source whose different terms cancel. The unresolved
case is an asymmetric finite source on one or more actual
periodic cores, satisfying (2), (3), and the remaining core
target equations. No group-ring splitting conclusion is
drawn from this reduction.

## A separate next-layer classification by reversed necklaces

The highest-creator calculation in the scalar-conjugate
artifact has joint kernel

```
X=omega^2Y,       tau Y=Y.
```

The simultaneous deletion-intertwiner equations appearing in
the next-layer analysis are

```
(t_i tensor I)Y=(I tensor t_i)Y,       i=0,1.        (4)
```

Here is an exact classification of finite symmetric tensors
satisfying (4). It classifies these auxiliary equations; it
does not assert that an arbitrary full kernel satisfies
`X=omega^2Y` or (4) globally.

Let `U` be the image of contraction of `Y` by arbitrary dual
forms in either factor. Symmetry makes the two images equal.
Then `Y` belongs to `U tensor U` and induces an isomorphism
`Y:U^* -> U`. Equation (4) implies that `U` is invariant
under both deletions and that this isomorphism intertwines
`t_i` with its dual.

In fact

```
U=t_0U+t_1U.
```

To see this, let a dual form `lambda` annihilate the right
side. Both dual deletions kill `lambda`, so (4) makes both
deletions kill `Y lambda`. The map `(t_0,t_1)` is jointly
injective, since `s_0t_0+s_1t_1=I`. Thus `Y lambda=0`,
and the isomorphism forces `lambda=0`.

Let `F` be the finite union of the basis supports of `U`.
Deletion invariance makes `F` closed under deletion of its
first bit. The displayed equality gives every element of
`F` a predecessor in `F`. Consequently deletion is a
permutation of this finite set, so `F` is a union of purely
periodic cores.

For a purely periodic tail

```
alpha=(b_0 b_1 ... b_(n-1))^infinity
```

with primitive period length `n`, define

```
J alpha=(b_(n-1) ... b_1 b_0)^infinity.
```

This definition uses the cut at the initial bit of the actual
tail. It obeys `J^2=I` and `J S=S^-1 J`, where `S` deletes
the first bit on a periodic core.

The coefficient form of (4) is

```
Y_(i alpha,beta)=Y_(alpha,i beta).
```

If `Y_(alpha,beta)` is nonzero and the first bit of `alpha`
is `i`, this moves its coefficient to `(S alpha,i beta)`.
The latter tail must be the unique periodic predecessor of
`beta`. Iterating gives

```
firstbit(S^k alpha)=firstbit(S^-(k+1) beta)
```

for every integer `k`, which is equivalent to `beta=J alpha`.
The coefficients are constant along each periodic core.
Conversely, for any core `C`, the tensor

```
E_C=sum_(alpha in C) alpha tensor J alpha
```

satisfies (4). Its flip is `E_(J C)`. Therefore all finite
symmetric solutions of (4) are the finite linear combinations
of

```
sum_(alpha in C union J C) alpha tensor J alpha,     (5)
```

one tensor for each pair of reversed primitive binary
necklaces. A self-reversed core is included only once in
the union. The statement includes diagonal tensors in
characteristic two; flip symmetry is not being identified
with the image of `I+tau`.

This classification identifies the possible finite tensors
for that next-layer compatibility condition. The full
symmetric-source injectivity proved above shows that these
tensors, with `X=omega^2Y`, do not themselves supply nonzero
full kernels. Cancellation involving additional asymmetric
terms remains a separate question.

## Bounded finite probe and exact remaining scope

After the analytic support reduction, one capped,
single-core MSI probe used the two reversed primitive cores
of `(001011)^infinity` and `(110100)^infinity`. Their twelve
rotations, together with one prefix layer, gave twenty-four
source tails and forty-eight output tails. For each of
`z=omega,omega^2`, the complete restricted source map had
column rank `1152/1152`. The probe completed normally in
2.895 seconds; it left no running job.

This finite calculation found no kernel in those two source
windows. It is independent of the proofs above and does not
establish injectivity on other periodic cores or on the full
boundary module. The proved reduction leaves precisely the
general asymmetric finite periodic-source problem described
after (3). Neither a full exterior injection nor a group-ring
splitting has been established here.
