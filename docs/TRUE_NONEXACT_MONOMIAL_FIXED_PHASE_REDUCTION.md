# Nonexact monomial domination reduces exactly to fixed-point phases

Date: 2026-08-11

## Outcome

Let

```text
P=<S | R>
```

be finitely presented and let `w` belong to `Rad_sof(P)`.  For an arbitrary
finite monomial representation of the free group `F(S)`, the character
defect of a word splits exactly into

```text
permutation moved mass + phase energy on its fixed points.       (NMF1)
```

The linear sofic-radical inequality uniformly controls the first summand of
the witness by the total relator defect.  Consequently the optimal monomial
domination constant is finite if and only if one scalar constant involving
only the **fixed-point phase energy** is finite.  This statement does not
assume that the underlying permutation chart is an exact `P`-set and does
not assume permutation stability.

Thus the nonexact monomial overlap left in
`TRUE_EXACT_COVER_MONOMIAL_DISCRIMINANT.md` is narrower than arbitrary base
instability: a counterexample must place essentially all witness energy in
phases over points already fixed by `w`.

## 1. Exact motion--phase decomposition

Let `X` be a nonempty finite set and let

```text
U:F(S)->T^X semidirect Sym(X)                         (NMF2)
```

be a monomial unitary representation.  Write `rho` for its underlying
permutation action.  For every `g in F(S)` there are phases
`zeta_g(x) in T` such that

```text
U(g)e_x=zeta_g(x)e_(rho(g)x).                         (NMF3)
```

Define

```text
m_X(g)=|{x:rho(g)x!=x}|/|X|,                          (NMF4)

phi_U(g)=1/|X| sum_(x:rho(g)x=x)(1-Re zeta_g(x)).     (NMF5)
```

Let

```text
delta_U(g)=1-Re tr_X(U(g)).                           (NMF6)
```

**Lemma 1 (exact decomposition).**  For every `g`,

```text
delta_U(g)=m_X(g)+phi_U(g).                           (NMF7)
```

**Proof.**  If `rho(g)x!=x`, the `x`-th diagonal matrix coefficient of
`U(g)` is zero, so that column contributes `1` to `(NMF6)`.  If `x` is
fixed, its diagonal coefficient is `zeta_g(x)` and its contribution is
`1-Re zeta_g(x)`.  Average over `X`.  End proof.

In particular every term in `(NMF7)` is nonnegative.  Put

```text
M_R(U)=sum_(r in R)m_X(r),
Phi_R(U)=sum_(r in R)phi_U(r),
D_R(U)=sum_(r in R)delta_U(r)=M_R(U)+Phi_R(U).        (NMF8)
```

## 2. The base contribution is already controlled

Since `w in Rad_sof(P)`, Theorem 2 of
`TRUE_LINEAR_SOFIC_RADICAL_INEQUALITY.md` gives a finite constant `C_cl`
such that every finite `F(S)`-action satisfies

```text
m_X(w)<=C_cl M_R(U).                                  (NMF9)
```

Define the optimal monomial and fixed-phase constants

```text
C_mon=sup_(U:D_R(U)>0) delta_U(w)/D_R(U),             (NMF10)

C_fix=sup_(U:D_R(U)>0) phi_U(w)/D_R(U).               (NMF11)
```

The suprema range over all finite monomial representations, with arbitrary
underlying finite `F(S)`-actions and arbitrary phase orders.

**Theorem 2 (nonexact fixed-phase reduction).**

```text
C_fix<=C_mon<=C_cl+C_fix.                             (NMF12)
```

In particular,

```text
C_mon<infinity  iff  C_fix<infinity.                  (NMF13)
```

**Proof.**  The first inequality follows from
`phi_U(w)<=delta_U(w)`.  For the second, use `(NMF7)--(NMF9)`:

```text
delta_U(w)
 =m_X(w)+phi_U(w)
 <=C_cl M_R(U)+phi_U(w)
 <=(C_cl+C_fix)D_R(U).
```

Take the supremum.  End proof.

There is a useful sequence form.  If

```text
delta_(U_n)(w)/D_R(U_n)->infinity,                    (NMF14)
```

then

```text
phi_(U_n)(w)/D_R(U_n)->infinity,                      (NMF15)

m_(X_n)(w)/delta_(U_n)(w)->0.                         (NMF16)
```

Indeed `(NMF9)` bounds the numerator in `(NMF16)` by
`C_cl D_R(U_n)`, while `(NMF14)` says this is negligible compared with the
witness defect.  Thus growing permutation degree, failure of exactness, and
motion of the radical word are not themselves the monomial obstruction.

## 3. Geodesic fixed-phase constant

For a fixed point of `g`, write `t_g(x) in [-1/2,1/2]` for a principal
argument of `zeta_g(x)`, and set

```text
psi_U(g)=1/|X| sum_(x:rho(g)x=x)|t_g(x)|^2.           (NMF17)
```

On the principal interval,

```text
8|t|^2<=1-cos(2 pi t)<=2 pi^2|t|^2.                  (NMF18)
```

Define

```text
C_geo=sup_(U:D_R(U)>0)
 psi_U(w)/(M_R(U)+sum_(r in R)psi_U(r)).              (NMF19)
```

Zero denominators contribute zero; `(NMF9)` then also forces zero witness
motion, and `(NMF18)` handles the phase term.

**Theorem 3 (chordal--geodesic comparison).**

```text
(4/pi^2) C_geo<=C_fix<=2 pi^2 C_geo.                  (NMF20)
```

**Proof.**  Write `Psi_R=sum_r psi_U(r)`.  Equations `(NMF8)` and `(NMF18)`
give

```text
M_R+8 Psi_R<=D_R<=M_R+2 pi^2 Psi_R.                  (NMF21)
```

For the upper bound,

```text
phi_U(w)/D_R
 <=2 pi^2 psi_U(w)/(M_R+8 Psi_R)
 <=2 pi^2 psi_U(w)/(M_R+Psi_R).                      (NMF22)
```

For the lower bound,

```text
phi_U(w)/D_R
 >=8 psi_U(w)/(M_R+2 pi^2 Psi_R)
 >=(4/pi^2) psi_U(w)/(M_R+Psi_R).                    (NMF23)
```

Take suprema.  End proof.

Combining Theorems 2 and 3, monomial domination on arbitrary nonexact
charts is equivalent to the one partial-holonomy inequality

```text
psi_U(w)
 <=C (M_R(U)+sum_(r in R)psi_U(r)).                  (NMF24)
```

The term `M_R` charges the points on which a relator loop does not close;
the remaining terms see only the phases of loops which do close.

## 4. Exact charts and transitive reduction

If the underlying action factors through `P`, then every relator fixes
every point.  The finite permutation image is sofic, so radical membership
also makes `w` fix every point.  Hence `M_R=0`, and `(NMF19)` becomes exactly
the phase-holonomy ratio treated by
`TRUE_EXACT_COVER_MONOMIAL_DISCRIMINANT.md`.

The transitive restriction is in fact available without first invoking
irreducibility.

**Proposition 4 (one transitive base orbit suffices).**  The suprema
`C_mon`, `C_fix`, and `C_geo` are unchanged if one restricts them to
monomial representations whose underlying `F(S)`-action on `X` is
transitive.

**Proof.**  Decompose `X` into permutation orbits `X_i`.  Every coordinate
subspace `ell^2(X_i)` is invariant under all monomial matrices, so `U` is
the dimension-weighted direct sum of its orbit restrictions `U_i`.
The quantities `m_X(g)`, `phi_U(g)`, `psi_U(g)`, and `delta_U(g)` are the
same dimension-weighted averages of the corresponding quantities for the
`U_i`.  Each quotient defining the three constants is therefore a weighted
average of the orbit quotients, with weights proportional to the orbit
denominators.  An orbit with zero denominator also has zero witness
numerator: its relators act identically, so it factors through `P`, and its
monomial image is sofic and kills `w`.  Hence the quotient of `U` is at most
the largest quotient of one transitive orbit.  The reverse inequality is
immediate.  End proof.

In particular an irreducible monomial representation is necessarily
transitive, but Proposition 4 is stronger: reducibility and mixtures can be
removed directly at the fixed-phase level.

## 5. The phase-insensitive character constant is the same

The universal radical constant is usually written with

```text
q_U(g)=1-|tr_X(U(g))|^2.                              (NMF25)
```

Let

```text
C_mon^q=sup_(U:sum_R q_U(r)>0)
 q_U(w)/sum_(r in R)q_U(r).                           (NMF26)
```

**Theorem 5 (exact monomial affine reduction).**

```text
C_mon^q=C_mon.                                        (NMF27)
```

**Proof.**  The conjugate double `U tensor conjugate(U)` is again monomial,
now on `X times X`, and

```text
delta_(U tensor conjugate(U))(g)=q_U(g).              (NMF28)
```

Therefore `C_mon^q<=C_mon`.

Conversely, fix a monomial representation `V` of dimension `d` and put

```text
V_M=1^(direct sum M) direct sum V,
t_M=d/(M+d).                                          (NMF29)
```

This is monomial, and direct calculation gives

```text
q_(V_M)(g)
 =2t_M delta_V(g)-t_M^2|1-tr_d(V(g))|^2.             (NMF30)
```

After division by `2t_M`, the quotient in `(NMF26)` converges as
`M->infinity` to the affine quotient of `V` in `(NMF10)`.  Taking the
supremum over `V` gives `C_mon<=C_mon^q`.  End proof.

Zero relator denominators cause no exception.  In the affine case they
force every relator matrix to be the identity; in the phase-insensitive
case they force every relator matrix to be scalar, so the conjugate double
factors through `P`.  Its finitely generated linear image is sofic, and
radical membership forces its image of `w` to be the identity.

Combining `(NMF12)`, `(NMF20)`, and `(NMF27)`, the monomial restriction of
the universal phase-insensitive domination constant is finite exactly when
the partial geodesic fixed-phase constant `(NMF19)` is finite.

## 6. Scope and the remaining gate

The theorem does not bound `C_fix`.  It proves that no separate quantitative
permutation-exactification theorem is needed merely to remove the **motion
part** of monomial character defects.  The still-open nonexact gate is now
precisely `(NMF24)`: fixed-point phase holonomy must be controlled by closed
relator phases plus the small mass on which relator loops fail to close.

For a hyperlinear nonsofic monomial witness with relator defect tending to
zero and witness defect bounded below, `(NMF15)--(NMF16)` say that the
underlying permutations already move `w` on asymptotically zero mass.  The
macroscopic witness is necessarily phase cancellation over its fixed
points.  This is the exact common boundary between the normal-character
TRUE program and the clock/Schur-curvature FALSE program.
