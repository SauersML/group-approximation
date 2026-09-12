# Every target class occurs in an arbitrarily small two-projection angle

Date: 5 September 2026. A precise obstruction to the proposed
projection-homotopy approach to mixed realization. This is not a
counterexample to LXXVI and does not assert that realization fails.

Let `D` be separable, simple, stably finite, pure, and real rank zero.
Set `B=D tensor K`, `F=(D tensor Z) tensor K`, and write
`phi:B->F` for first-factor inclusion. Let `X` be compact metrizable.
The all-base full order-reflection theorem is used only when passing
from exact corner realization to global increasing suprema below.

## 1. An increasing reduction to constant source projection corners

Real rank zero and separability give an increasing projection
approximate unit `(p_n)` of `B`. Since the Z factor is unital,
`P_n=phi(p_n)` is an approximate unit of `F`. For every positive
contraction `b in C(X,F)`, compactness of its range makes

`b_n=P_n b P_n -> b`

uniform in norm. Each `b_n` belongs to the corner of the **constant
actual source projection** `P_n`.

Although the positive elements `b_n` need not increase, their Cu
classes do. Indeed, with `t_n=b^(1/2)P_n`,

`t_n*t_n=b_n`, `t_n t_n*=c_n=b^(1/2)P_n b^(1/2)`.

The positive sections `c_n` increase to `b` in norm, and hence

`[b_n]=[c_n]`, `[b_n] <= [b_(n+1)]`,
`sup_n[b_n]=[b]`, and `[b_n]<=[b]`.                  (1)

Thus the realization problem already reduces to positive sections
in constant source projection corners. No local bundle patching is
needed for this reduction.

More precisely, under the known full order reflection, the following
two assertions are equivalent:

* the first-factor map is surjective on `Cu(C(X,D))`;
* every positive contraction in every corner
  `C(X,phi(p)Fphi(p))`, with `p in B` a projection, has a Cu class
  in the first-factor image.

Only the reverse implication needs proof. Lift every `[b_n]` to a
source class `x_n`. Order reflection and (1) give `x_n<=x_(n+1)`.
Its supremum maps to `[b]`, because Cu morphisms preserve increasing
suprema. This does not replace norm convergence by an unjustified
assertion that the source classes are increasing.

There is also a sandwich version. Given `y'<<[b]`, choose
`y'<<y''<<[b]`. Equation (1) puts `y''<=[b_n]` for some `n`,
so `y'<<[b_n]` and then
`y'<=[(b_n-epsilon)_+]` for some `epsilon>0`. Any corner sandwich
between this cutoff and `[b_n]` is therefore a sandwich between
`y'` and `[b]`.

## 2. Universal encoding by two individually trivial projections

Fix a source projection `p`, write `P=phi(p)`, and let
`a in C(X,PFP)` be an arbitrary positive contraction. For
`0<=t<=1`, define the rectangular isometry and two projections

`W_t = column( sqrt(P-t a), sqrt(t a) )`,

`Q_0 = diag(P,0)`,

`Q_t = W_t W_t*`
`    = [[P-t a, sqrt(t a(P-t a))],`
`       [sqrt(t a(P-t a)), t a]]`.                    (2)

All formulas use functional calculus in the unital corner `PFP`.
Since `W_t*W_t=P`, the projection `Q_t` is globally equivalent
to the constant source projection `Q_0`, by an explicitly given
partial isometry. Thus no nontrivial projection bundle or clutching
class is involved in (2).

Nevertheless its angle compression is

`(1-Q_0)Q_t(1-Q_0)=diag(0,t a)`.                     (3)

For every `t>0`, the Cu class in (3) is exactly `[a]` under the
standard stabilization identification. The scalar weights in the
two-patch construction may both be identically one, so they are
nested and never vanish. The second projection is individually
trivial as a bundle, with the explicit trivialization `W_t`.

Consequently realization of arbitrary mixed angle remainders in
this particularly restricted two-patch configuration is equivalent
to the corner realization assertion in Section 1. With the already
proved order reflection, it is equivalent to full target realization.
This is an exact identification of the remaining difficulty, not a
new sufficient condition presented as though it were easier.

## 3. The encoding survives arbitrarily small norm separation

Direct multiplication of the difference in (2) gives

`(Q_t-Q_0)^2=diag(t a,t a)`.

Hence the exact norm formula is

`||Q_t-Q_0|| = sqrt(t ||a||)`.                       (4)

For any prescribed radius `rho>0`, choose `0<t<rho^2`. The two
projections then lie within `rho`, but their angle remainder still
has the arbitrary Cu class `[a]`.

There is even an explicit small projection homotopy all the way to
coincidence. For `0<=s<=t`, use `Q_s` from (2). It stays in the
same `rho`-ball about `Q_0`. The unitary

`U_s = [[sqrt(P-s a), -sqrt(s a)],`
`       [sqrt(s a),   sqrt(P-s a)]]`

lies in the unital matrix corner, satisfies `U_0=1`, and obeys
`U_s Q_0 U_s*=Q_s`. Every member of the homotopy has the same
projection bundle class. On the other hand, its angle remainder
has class `[a]` for every `s>0` and class zero at `s=0`.

This proves the following obstruction to a specific proposed method:
weak homotopy equivalence or local contractibility of the individual
projection embedding spaces does not by itself control the Cu class
of the Gram configuration. Even a norm-small, explicitly trivial
homotopy of those embeddings can erase an arbitrary mixed class.
Such a homotopy must be supplemented by spectral/cutoff control if
it is to be used for realization.

## 4. The entire ambiguity is visible in a two-by-two Gram matrix

Take the columns `Z_1=column(P,0)` and `Z_2=W_t`. Both initial
projections are the same actual source projection `P`. Their Gram
matrix is

`G_t = [[P, sqrt(P-t a)], [sqrt(P-t a), P]]`.          (5)

The two diagonal entries already lie in the source image exactly.
The fixed scalar Hadamard unitary diagonalizes (5) as

`diag(P+sqrt(P-t a), P-sqrt(P-t a))`.

The first summand is invertible in the `P` corner. For `0<t<=1`
and `0<=u<=1`,

`(t/2)u <= 1-sqrt(1-tu) <= t u`.

Functional calculus therefore identifies the second summand's Cu
class with `[a]`. Thus

`[G_t]=[Q_0+Q_t]=[P]+[a]` for `t>0`.                (6)

This recovers the earlier exact two-patch decomposition, but now
shows that its mixed angle term can be completely arbitrary even
with fixed, equal Gram diagonals and no bundle topology.

We do not infer realization of `[a]` solely from realization of
`[P]+[a]`: that separate inference would require an appropriate
compact-summand removal/cancellation argument. The equivalence in
Section 2 concerns realization of the actual angle remainder (3),
so it does not depend on an unstated cancellation theorem for a
section algebra.

## 5. Why invertible angle padding does not produce the needed supremum

A tempting local repair replaces `a` by `a+epsilon P`. For every
`epsilon>0`, this element is invertible in the `P` corner and has
Cu class `[P]`. It converges to `a` in norm as `epsilon` decreases
to zero, but this is a decreasing family; its constant Cu classes
do not recover `[a]` by increasing suprema. If `[a]!=[P]`, the
replacement has already lost the desired hereditary information.

The same problem appears when one enforces a uniform positive
angle gap by padding: the gap makes the remainder a projection
class, but it changes the class that the realization argument must
retain. Equation (1) supplies a legitimate increasing approximation,
whereas this invertible padding does not.

The result proved here is therefore a precise methodological
obstruction and a sharper equivalent formulation of the remaining
target-realization problem. It does not prove that a lift fails to
exist. RR0 projection compression and Cu suprema reduce the problem
to the constant-corner angle model, but neither those operations nor
the established projection-space homotopies currently construct its
arbitrary mixed remainder in the source.

## Dependencies

- The already proved all-base first-factor order reflection:
  `stw99-lxxvi-rr0-full-order-reflection-audit-2026-09-05.md`.
- The exact two-patch decomposition and its positive special cases:
  `stw99-lxxvi-rr0-two-patch-angle-realization-2026-09-05.md`.

All projection, norm, Gram, and compression identities used in this
artifact are proved explicitly above. No new source survey or
unverified literature theorem is used. Frozen artifacts were not
modified, and no new Cairn closure node is asserted.
