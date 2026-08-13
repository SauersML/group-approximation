# Nonamenable stabilizers fill the radical loop in `ell^2`

Date: 2026-08-11

## 1. Outcome

The spectral alternative in
`FALSE_REAL_FILLING_ESCAPE_DICHOTOMY.md` can be decided for the explicit
stable polynomial/Laurent double.  The marked parallel-edge homology class
has a nonamenable stabilizer.  A regular-representation divergence equation
then builds an actual finite-energy `ell^2` filling of the marked loop in
the infinite radical cover.

Thus the inverse spectral moment

`integral_((0,infinity)) lambda^(-1)dmu_b(lambda)`       `(NSF1)`

is finite for this candidate.  The infinite-cover spectral-tail route is
closed here.

There is nevertheless a useful quantitative finite-cover consequence.  A
Kazhdan subgroup in the stabilizer fills, with one uniform norm bound, the
difference between the marked loop and its subgroup-orbit average.  Hence
the minimum real filling norm is comparable, up to a fixed additive
constant, to the filling norm of that invariant average.  Any real-filling
divergence—and therefore any FALSE certificate from this route—must be
carried entirely by this one transfer mode.

## 2. A nonamenable divergence equation

Let `J` be a finitely generated group and choose a finite symmetric
generating set `T`.  On the right regular representation put

`D:directSum_(s in T) ell^2(J)->ell^2(J)`,
`D((xi_s))=sum_(s in T) xi_s(s-1)`.                    `(NSF2)`

Here multiplication is right convolution.  Its adjoint is the right
gradient.  The following standard form of the Kesten criterion is the only
analytic input.

**Lemma 1 (nonamenable divergence).**  If `J` is nonamenable, then `D` is
surjective.  In particular there are `xi_s in ell^2(J)` such that

`sum_(s in T)xi_s(s-1)=delta_1`.                       `(NSF3)`

**Proof.**  The kernel of `D^*` consists of right-invariant vectors and is
zero because `J` is infinite.  Nonamenability says that the right gradient
`D^*` is bounded below: this is the spectral-gap form of Kesten's criterion.
Therefore `D` has closed dense range, hence is onto.  End proof.

If `J` has property `(T)`, the same statement is uniform in finite
quotients.  Namely, for every finite quotient `J/J_0`, the specialized
operator `D_(J/J_0)` maps onto the orthogonal complement of the constants,
and it has a right inverse there of norm at most one fixed constant
`C_J`.  This is the Kazhdan inequality applied to the right regular
representations of all the quotients.

## 3. Stabilized homology classes have `ell^2` fillings

Let

`partial_2:C_2->C_1`                                    `(NSF4)`

be a boundary map between finite-rank free `Z[F]`-modules.  Give their
`ell^2` completions the standard Hilbert norms.  Let `b in C_1` be a
finitely supported cycle.  Suppose a subgroup `J<=F` fixes the ordinary
homology class of `b`:

`(s-1)[b]=0 in H_1(C_*)` for every `s in J`.            `(NSF5)`

For each `s in T`, choose a finitely supported chain `c_s in C_2` with

`partial_2 c_s=(s-1)b`.                                 `(NSF6)`

**Theorem 2 (nonamenable-stabilizer filling).**  If `J` is nonamenable,
then there is `z in ell^2(C_2)` such that

`partial_2z=b`.                                         `(NSF7)`

**Proof.**  Choose the coefficients `xi_s` from Lemma 1 and define

`z=sum_(s in T) xi_s c_s`.                              `(NSF8)`

The product in `(NSF8)` means the convergent translate sum

`xi_s c_s=sum_(j in J)xi_s(j) j c_s`.                  `(NSF9)`

It is an `ell^2` chain.  Indeed multiplication by the fixed finite chain
`c_s` is a finite matrix of convolution operators, hence has norm at most
its coefficient `ell^1` norm.  Boundary commutes with the `F`-action, so
`(NSF3)` and `(NSF6)` give

`partial_2z`
` =sum_s xi_s(s-1)b`
` =delta_1 b=b`.                                       `(NSF10)`

End proof.

This theorem explains why ordinary nontriviality of `[b]` does not exclude
an `ell^2` filling.  The infinite translate sum in `(NSF8)` has no finite
algebraic support, and its existence is exactly the discontinuity of the
ordinary homology quotient in the `ell^2` topology.

## 4. Uniform finite-cover localization

Assume now that `J` has property `(T)`.  Let `L_n normal F` be finite-index
subgroups, put `J_n=J intersect L_n`, and specialize `(NSF4)--(NSF6)` to
the regular finite `F/L_n`-cover.  Denote the specialized marked cycle by
`b_n` and let

`P_n=(1/|J/J_n|)sum_(j in J/J_n)j`                    `(NSF11)`

be the orthogonal projection onto the `J`-invariant chains.

**Theorem 3 (orbit-average reduction).**  There is a constant `C`,
independent of `n`, and a two-chain `u_n` such that

`partial_2u_n=b_n-P_nb_n`, `||u_n||_2<=C`.             `(NSF12)`

Consequently, writing `Fill_R,2` for the minimum real filling norm,

`Fill_R,2(P_nb_n)`
` <=Fill_R,2(b_n)`
` <=Fill_R,2(P_nb_n)+C`.                               `(NSF13)`

In particular the marked real filling norms are unbounded if and only if
the invariant-average filling norms are unbounded.

**Proof.**  Apply the finite-quotient form of Lemma 1 to obtain vectors
`xi_(s,n) in ell^2(J/J_n)` satisfying

`sum_s xi_(s,n)(s-1)=delta_(J_n)-P_n delta_(J_n)`,
`sum_s||xi_(s,n)||_2^2<=C_J^2`.                        `(NSF14)`

Set

`u_n=sum_s xi_(s,n)c_(s,n)`.                           `(NSF15)`

The finite convolution maps in `(NSF15)` have norms bounded independently
of the quotient: the chain modules are finite sums of regular `F/L_n`
modules, and the Schur bound uses only the fixed coefficient `ell^1` norms
of the `c_s`.  This gives one constant `C` and, exactly as in `(NSF10)`,

`partial_2u_n=(1-P_n)b_n`.                             `(NSF16)`

For the upper bound in `(NSF13)`, add `u_n` to a minimum filling of
`P_nb_n`.  For the lower bound, apply the contraction `P_n` to a minimum
filling of `b_n`; equivariance gives a filling of `P_nb_n` of no larger
norm.  End proof.

The average in `(NSF11)` is rational rather than integral.  Theorem 3 is a
real-filling localization; it does not remove the integral discriminant
correction.

There is an exact cover-theoretic form of the invariant term.  Suppose the
finite complexes above are covers of one finite presentation complex for a
group `D`, obtained from a quotient `pi:D->F`.  Put

`K_n=pi^(-1)(L_n)`,
`H_n=pi^(-1)(J L_n)`,
`m_n=[H_n:K_n]=|J/(J intersect L_n)|`.                `(NSF16a)`

The cover `Y_(K_n)->Y_(H_n)` has degree `m_n`.  Let

`J_n^!:C_*(Y_(H_n),R)->C_*(Y_(K_n),R)`                `(NSF16b)`

be constant lift, the sum of all lifts of every cell.

**Proposition 4 (exact quotient scaling).**  If `b_(H_n)` is the marked
loop in the intermediate cover, then

`P_n b_n=(1/m_n)J_n^! b_(H_n)`                        `(NSF16c)`

and

`Fill_R,2(P_n b_n;Y_(K_n))`
` =m_n^(-1/2) Fill_R,2(b_(H_n);Y_(H_n))`.              `(NSF16d)`

Consequently `(NSF13)` becomes

`m_n^(-1/2) Fill_R,2(b_(H_n))`
` <=Fill_R,2(b_n)`
` <=m_n^(-1/2) Fill_R,2(b_(H_n))+C`.                  `(NSF16e)`

**Proof.**  The deck orbit of one lift of the marked loop is exactly the
set of `m_n` lifts of `b_(H_n)`, which proves `(NSF16c)`.  Constant lift
multiplies squared cellular norm by `m_n`.

Every filling of `P_nb_n` may be averaged over the deck group without
changing its boundary or increasing its norm.  An invariant chain is
uniquely the constant lift of a chain downstairs.  Therefore a minimum
filling has the form `(1/m_n)J_n^!z`, where `z` is a minimum filling of
`b_(H_n)`.  Its norm is

`(1/m_n)sqrt(m_n)||z||=m_n^(-1/2)||z||`,              `(NSF16f)`

proving `(NSF16d)`.  Combine with Theorem 3 for `(NSF16e)`.  End proof.

Thus the surviving real criterion is no longer an unspecified invariant
mode: it is **super-square-root filling growth** in the intermediate
subgroup tower `H_n`.

## 5. The explicit stable Laurent double

Use the stable integral pair

`Gamma=EL_r(Z[x_1,...,x_d])`,
`N=EL_r(Z[x_1^(+-1),...,x_d^(+-1)])`,
`r>=d+4`, `d>=3`,                                      `(NSF17)`

and the symmetric double notation

`D=G *_Gamma G`, `F=G *_N G`,
`R_0=ker(D->F)`.                                       `(NSF18)`

Take

`h=e_12(x_1^(-1)) in N minus Gamma`,
`w=i_2(h)i_1(h)^(-1)`.                                 `(NSF19)`

Under the Bass--Serre homology isomorphism,

`(R_0)_ab`
` ~=ker(Z[F/Gamma]->Z[F/N])`,
`[w]=delta_(hGamma)-delta_Gamma`.                       `(NSF20)`

The stabilizer of this vector already contains the much smaller constant
lower-right elementary group

`J=EL_3(Z)=SL_3(Z)`,                                   `(NSF21)`

embedded on the coordinates `3,4,5` and acting trivially on all remaining
coordinates.  Indeed `J<=Gamma` and every element of `J` commutes with `h`,
so it fixes both cosets in `(NSF20)`.  The group `J` has property `(T)` and
is nonamenable.  The stable range gives `r>=d+4>=7`, so this block is
available.

Using the constant subgroup is quantitatively stronger than using the full
lower-right polynomial elementary group: the averaging degree in a finite
quotient is now only the size of the image of one fixed `SL_3(Z)`.

Apply Theorem 2 to any finite presentation chain complex of `D`, viewed in
the `R_0`-cover.  The marked loop has an `ell^2` filling.  Equivalently, for
its spectral measure under `partial_2 partial_2^*`,

`mu_b({0})=0`,
`integral_((0,infinity))lambda^(-1)dmu_b(lambda)<infinity`. `(NSF22)`

The first assertion was proved independently by the tempered-harmonic
argument in `FALSE_REAL_FILLING_ESCAPE_DICHOTOMY.md`; Theorem 2 supplies the
strictly stronger inverse-moment assertion.

Now take any nested residual chain `L_n normal F` and pull it back to finite
covers of `D`.  Theorem 3 gives

`Fill_R,2(b_n)=Fill_R,2(P_nb_n)+O(1)`.                 `(NSF23)`

Proposition 4 sharpens this to

`Fill_R,2(b_n)`
` =m_n^(-1/2)Fill_R,2(b_(H_n))+O(1)`,                 `(NSF24)`

where `H_n=pi^(-1)(J L_n)` and `m_n=|J/(J intersect L_n)|`.

Therefore Corollary 2 of the real-filling note can prove FALSE on this
tower precisely when the intermediate filling norms grow faster than
`sqrt(m_n)`.  All noninvariant Kazhdan modes admit one uniform real decoder.

## 6. Consequence for the remaining FALSE lane

The result closes the optimistic possibility that ordinary nontriviality of
the radical word in `(R_0)_ab` forces a bad near-zero spectral tail.  It does
not: the nonamenable stabilizer explicitly fills that word in `ell^2`.

The live finite-cover alternatives are now reduced to the same invariant
transfer sector from two independent directions:

1. real filling escape is equivalent, up to `(NSF23)`, to escape of the
   `J`-orbit average;
2. integral filling escape is automatic, but after the noninvariant real
   part is filled uniformly its excess lies in the paired discriminant
   correction.

Thus the next exact object has two equivalent descriptions:

* the rational invariant cycle `P_nb_n`, with denominator `m_n`; or
* the marked loop in the intermediate cover `Y_(H_n)`, whose real filling
  must be compared with `sqrt(m_n)`.

One should compute its transfer holonomy in the fixed-rank base lattice.
Persistent bounded-order pairing proves FALSE by
`FALSE_TRANSFERRED_FILLING_PAIRING_FORMULA.md`; a common fixed-kernel
filling would instead close the tower by
`FALSE_FIXED_KERNEL_COVER_NO_GO.md`.
