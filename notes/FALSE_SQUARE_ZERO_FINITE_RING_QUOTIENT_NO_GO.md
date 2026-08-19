# Finite coefficient-ring quotients erase the internal-stable-letter survivor

Date: 2026-08-11

## 1. Outcome

The explicit residual-finiteness quotients of the **original** square-zero
Kun--Thom pair cannot amplify the paired class whose stable letter lies in
`Q`, as constructed in `FALSE_SQUARE_ZERO_BS_KUN_THOM_PAIR.md`.  In fact
every finite quotient of the Laurent coefficient ring already identifies
the positive and Laurent subrings.  In the resulting finite group quotient
the image of `Gamma` is normal, that original Baumslag--Solitar subgroup
acts trivially on the finite coset set, and its augmentation transgression
is zero.

This is an exact no-go theorem, not a poor scaling observation.  The live
analytic search must use phase microstates which do not factor through a
finite coefficient ring.

The theorem does **not** apply to the stronger fold-aligned subgroup in
`FALSE_RADICAL_BS_PAIRED_KUN_THOM_DOUBLE.md`.  There the stable letter is
`c=(c_0,s)` with nontrivial external substitution projection `s in L`, so
its finite coset action need not be trivial.  That external component is
exactly what escapes the argument below.

## 2. Positive and Laurent images coincide in every finite ring

Retain the notation

`R_+=C[x_1,...,x_d]`,
`R=C[x_1^(+-1),...,x_d^(+-1)]`                       `(FRQ1)`

from the square-zero construction.  Let

`phi:R->S`                                             `(FRQ2)`

be any unital homomorphism to a finite ring.  The element `phi(x_i)` is a
unit of the finite group `S^x`, so it has some finite order `m_i>=1`.
Consequently

`phi(x_i^(-1))=phi(x_i)^(m_i-1) in phi(R_+)`.          `(FRQ3)`

Every Laurent monomial is therefore in the image of the positive
polynomial ring, and the reverse inclusion is automatic.  Hence

`phi(R_+)=phi(R)`.                                     `(FRQ4)`

The argument uses neither commutativity nor the square-zero structure
beyond the definitions in `(FRQ1)`; finiteness of the target unit group is
the entire reason.

## 3. Collapse of the finite coset action

Suppose `(FRQ2)` is compatible with finite images of the external actions,
as in the quotients

`C_ell[(Z/mZ)^d]`,
`Q->SL_3(F_ell)`, `L->SL_d(Z/mZ)`                     `(FRQ5)`

used to prove residual finiteness.  Write bars for the corresponding group
images.  Equation `(FRQ4)` gives

`bar(E_r(R_+))=bar(E_r(R))`.                           `(FRQ6)`

Therefore

`bar(Gamma)=bar(E_r(R)) semidirect bar(Q)`             `(FRQ7)`

inside

`bar(G)=bar(E_r(R)) semidirect (bar(Q) times bar(L))`. `(FRQ8)`

The subgroup in `(FRQ7)` is normal: the elementary factor is preserved by
the monomial action of `bar(L)`, while `bar(Q)` commutes with `bar(L)`.
Thus the finite coset action factors through `bar(L)`.

The original marked subgroup

`B=<h,c> ~= BS(1,p+1)`                                `(FRQ9)`

is contained in `E_r(R) semidirect Q`, so

`bar(B)<=bar(Gamma)`.                                  `(FRQ10)`

Normality of `(FRQ7)` now implies that `bar(B)` acts trivially on every
coset in `bar(G)/bar(Gamma)`, not merely on the identity coset.

## 4. The augmentation transgression vanishes

Let `P=bar(G)/bar(Gamma)` and

`I_P=Aug_(F_p)(P)`.                                   `(FRQ11)`

By `(FRQ10)`, the restriction to `B` of the permutation module `F_p[P]`
is trivial.  The augmentation sequence

`0->I_P->F_p[P]->F_p->0`                              `(FRQ12)`

therefore splits as a sequence of `B`-modules: any chosen point of the
nonempty set `P` gives a `B`-fixed section of the augmentation.  Its
connecting map is identically zero,

`H_2(B,F_p)->H_1(B,I_P)=0`.                           `(FRQ13)`

In particular the explicit paired bar class `[Z_p]` has zero image in
every finite coefficient-ring quotient, although its transgression in the
infinite coset module is nonzero by `(SQ38)`.

Here `[Z_p]` denotes the class with internal stable letter
`c in Q`.  The fold-aligned class `(RB18)` has stable letter `(c_0,s)` and
is outside the scope of `(FRQ13)`.

This explains the analytic gap sharply.  Residual finiteness of `G` does
not approximate the nonnormal pair `(G,Gamma)` in a way which retains the
marked augmentation class; all of the natural finite ring quotients make
the subgroup image normal first.

## 5. Computational consequence

Do not sweep the parameters `(ell,m)` in `(FRQ5)` looking for positive
marked mass from the original internal-stable-letter class.  The answer is
exactly zero for every such quotient.  A finite-quotient incidence audit
of the fold-aligned class remains meaningful because its stable letter is
visible in the `L` quotient.

The remaining viable finite-dimensional models must violate at least one
of the hypotheses above.  Concretely they may use:

1. nonexact local cone truncations with boundary error measured in
   normalized Hilbert--Schmidt norm;
2. monomial/permutation charts carrying a nontrivial phase table which
   does not descend from a finite coefficient ring; or
3. genuinely projective matrix microstates of the square-zero pair.

The load-bearing statistic remains trace visibility of the marked
translation `h`.  Equation `(FRQ13)` shows that it cannot come from the
obvious residual tower and prevents a large but mathematically sterile
finite-quotient campaign.
