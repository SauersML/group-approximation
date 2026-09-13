# Three explicit torsion generators for the binary Pestov construction

2026-09-13. Written proof; not Lean-verified. The generator bound improves
from eighteen involutions to three elements of orders `7,2,2`, without
changing the group, its universal locally finite core, or its finite
centralizer embeddings. The algebraic statement below is independent of
the dynamical construction.

## 1. A ring-theoretic theorem

Let `R` be a nonzero unital `F_2`-algebra, generated as a unital algebra by
`u,u^{-1},p`, where `u` is a unit and `p^2=p`. No commutation between `u`
and `p` is assumed. For elementary roots write `e_ij(a)=I+a E_ij`.
Define

\[
c=\begin{pmatrix}0&0&1\\1&0&1\\0&1&0\end{pmatrix},\qquad
t=e_{12}(1-p)e_{13}(p),\qquad
w=\begin{pmatrix}0&u&0\\u^{-1}&0&0\\0&0&1\end{pmatrix}.
\]

**Theorem.** These three matrices generate `EL_3(R)`. Their respective
orders are exactly `7,2,2`. Moreover

`<c,t> = EL_3(F_2[p]) <= EL_3(R)`.                        (1)

If `p` is neither `0` nor `1`, this finite subgroup is naturally
`SL_3(F_2) x SL_3(F_2)`, and `ct` has order `12`.

All three generators belong to `EL_3(R)`: `c` is a constant determinant-one
matrix over `F_2`, `t` is displayed as a product of roots, and

`w = e_12(u)e_21(u^{-1})e_12(u)`.                         (2)

Their orders follow from `c^7=I`, `c != I`, and direct multiplication for
`t,w`. Neither of the latter matrices is the identity: `p,1-p` cannot
both vanish and a unit in a nonzero ring is nonzero.

## 2. Decode the idempotent by an explicit word

The following constant matrices explain the construction:

\[
t_0=e_{12}(1),\quad t_1=e_{13}(1),\quad
c t_0=\begin{pmatrix}0&0&1\\1&1&1\\0&1&0\end{pmatrix},\quad
P=c t_1=\begin{pmatrix}0&0&1\\1&0&0\\0&1&0\end{pmatrix}.
\]

They satisfy `(ct_0)^4=I` and `P^3=I`, with exact orders `4` and `3`.
Put

`z=(ct)^4`, `h=[z,t]^2`, with `[a,b]=aba^{-1}b^{-1}`.

We claim the exact identities

`z=(1-p)I+pP`,             `h=e_23(p)`.                  (3)

These identities may be checked separately at `p=0` and `p=1`. This is
a proof for every idempotent in every `R`, since all the entries concerned
lie in the image of the universal coefficient algebra
`F_2[s]/(s^2-s) ~= F_2 x F_2`. Centrality of `p` in `R` is unnecessary.

At `p=0`, `z=I`, so `h=I`. At `p=1`, `z=P` and `t=t_1`.
Conjugation by `P` sends `e_13(1)` to `e_21(1)`, so

`[P,t_1]^2 = (e_21(1)e_13(1))^2 = e_23(1)`.

For the last equality, the product is
`I+E_21+E_13+E_23`; in characteristic two its square is `I+E_23`.
This proves (3) without invoking simplicity or classifying subgroups of
`SL_3(F_2)`.

Conjugating `h` by `z` and `z^2` now gives `e_31(p)` and `e_12(p)`.
The three directed roots `e_12(p),e_23(p),e_31(p)` give the other three
by the elementary commutator identity, using `p^2=p`. In particular
`e_13(p)` belongs to `<c,t>`. Hence

`t e_13(p) = e_12(1-p)`.

Direct constant multiplication gives

`c e_12(a)c^{-1}=e_23(a)`,
`c^2 e_12(a)c^{-2}=e_31(a)`                              (4)

for every coefficient `a` (the entries of `c` are central scalars).
Apply (4) to `a=1-p`; its square is again itself. Spare-index
commutators give all six roots with coefficient `1-p`. Multiplying
corresponding roots with coefficients `p` and `1-p` gives all six
constant roots `e_ij(1)`.

We have recovered every root over the coefficient algebra
`F_2[p]`; the reverse inclusion in (1) was immediate. For nontrivial `p`,
evaluation at `0,1` identifies that algebra with `F_2 x F_2`, so its
elementary group is the direct product in section 1. Under this
identification, `ct` has components of orders `4,3`, hence order `12`.

## 3. Recover the unit and all ring coefficients

Let `Gamma=<c,t,w>`. The preceding section puts all constant elementary
matrices, and therefore all constant permutation matrices, in `Gamma`.
In particular the constant swap

`s=e_12(1)e_21(1)e_12(1)`

belongs to `Gamma`. Equation (2) yields

`d=ws=diag(u,u^{-1},1)`.

Consequently

`d e_13(1)d^{-1}=e_13(u)`,
`d^{-1} e_13(1)d=e_13(u^{-1})`.                          (5)

Conjugate by constant permutation matrices to obtain every root with
coefficient `u` or `u^{-1}`. The decoder already supplied every root
with coefficient `p`. To finish, let `R_0` be the set of coefficients
`a` such that all six `e_ij(a)` belong to `Gamma`. Root addition and

`[e_ik(a),e_kj(b)]=e_ij(ab)` for pairwise distinct `i,k,j`

show that `R_0` is a unital subalgebra of `R`. It contains `u,u^{-1},p`,
so `R_0=R`. Thus `Gamma=EL_3(R)`, proving the theorem.

## 4. Apply it to Pestov 9.1 and to the universal host

For any infinite minimal binary subshift, its crossed-product ring
`R=LC(X,F_2) semidirect Z` has exactly the required generators: the shift
unit `u`, its inverse, and the letter-one cylinder idempotent `p`.
Products of translates of `p` and `1-p` give the cylinder idempotents,
and their sums give all locally constant functions. Thus **every binary
instance of the repository's characteristic-two Pestov construction has
the three explicit torsion generators above**.

Both letters occur in an infinite minimal binary subshift, so `p` is
nontrivial. These groups are therefore quotients of the single fixed
free product

`(SL_3(F_2) x SL_3(F_2)) * C_2`,                          (6)

with the finite factor embedding injectively: its two generators map to
`c,t`, and the last involution maps to `w`. This does not claim that
(6) is a presentation of the quotient; the dynamical language determines
additional relations. The group in (6) is independent of the subshift.

In particular the fixed group with universal odometer factor is now an
**infinite simple Kazhdan LEF group generated by elements of orders
`7,2,2`, containing every countable locally finite group**. The universal
matrix core and all finite-centralizer embeddings constructed previously
are unchanged. Its sofic, hyperlinear and operator-MF consequences remain.
No minimality claim for the number of group generators is made.

## 5. Verification and scope

The constant matrix calculations in section 2 were checked on MSI by a
single bounded Python 3.12 process: `c` has order `7`, `ct_0` has order
`4`, `ct_1` has order `3`, and the squared commutator specializes to
`I,e_23(1)` at the two idempotent values. The two conjugation identities
in (4) were also checked. The full argument above explains why these
two finite evaluations certify the coefficient identity for an arbitrary
possibly noncentral idempotent. Equations (2) and (5) are ring identities
using only the two-sided inverse of `u`.

The elementary decoder is the new algebraic ingredient here. All
simplicity, property-(T), and LEF inputs are the existing 9.1 theorem.
This is a written proof, not a Lean formalization or a global priority
claim.

The [Cairn receipt](pestov91-three-generators-cairn-receipt-2026-09-13.json)
records successful check and preview on the archived source snapshot at
`6cb3014e6f3100ad9a6176588502f6f43dd092d5` with this change overlaid.
Cairn 2.13.1 parsed 10,198 claims and 10,459 routes, with no baseline or
final graph errors. Both new claims and the strengthened universal-host
and centralizer claims resolved as established. The MSI run used one
Python 3.12 process and took 32.277 seconds.

The archive-backed runner retained Cairn's parser, lint, solver, check
and preview policies, replacing source and HEAD loading. Artifact paths
were checked against the exact tracked manifest plus the delta, and
revision-pinned artifacts against the warm repository's Git objects.
This receipt and paragraph were added afterward. These checks validate
the research-graph wiring, not the mathematical proof by Lean.
