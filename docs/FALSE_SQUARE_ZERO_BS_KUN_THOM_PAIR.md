# A square-zero Baumslag--Solitar survivor inside a Kun--Thom pair

Date: 2026-08-11

## 1. Outcome

There is a residually finite Kazhdan infranormal pair `Gamma<G` containing
an explicit Baumslag--Solitar subgroup whose paired mod-`p` two-cycle
survives every double-coset stabilizer.  This removes the global algebraic
obstruction encountered by the coefficient-localized construction.

Fix an odd prime `p` and put

`q=p+1`, `A=Z[1/q]`.                                  `(SQ1)`

Let `V=A^3`, let `Q=SL_3(A)` act on `V` in the standard way, and form the
commutative square-zero `A`-algebra

`C=A directSum V`,
`(a,v)(b,w)=(ab,aw+bv)`.                               `(SQ2)`

Thus `V^2=0`, and `Q` acts on `C` by unital ring automorphisms, trivially
on `A` and standardly on `V`.

Choose `d>=3`, put

`R_+=C[x_1,...,x_d]`,
`R=C[x_1^(+-1),...,x_d^(+-1)]`,                        `(SQ3)`

and let `L=SL_d(Z)` act on `R` by monomial substitutions.  The actions of
`Q` and `L` commute.  For an even `r>=4`, define

`Gamma=E_r(R_+) semidirect Q`,
`G=E_r(R) semidirect (Q times L)`.                     `(SQ4)`

**Theorem 1.**  The groups in `(SQ4)` are residually finite Kazhdan
groups, and `Gamma<G` is infranormal and nonnormal.

Inside `G`, there is a subgroup `B~=BS(1,q)` and a character
`chi:B->mu_p` for which

`H_2(B,F_p)/`
` (ker beta_1+ker beta_chi`
`  +sum_(g in G) im H_2(B cap g Gamma g^(-1),F_p))`
` ~=F_p`.                                              `(SQ5)`

The generator is an explicit finite bar cycle whose ordinary Bockstein is
a marked element outside every conjugate of `Gamma`.  Consequently its
augmentation-module transgression is nonzero.

This is not by itself the complete FALSE proof: the remaining task is to
turn this exact derived class into a trace-visible finite-dimensional
unitary model along finite quotients.  The stronger aligned construction
in `FALSE_RADICAL_BS_PAIRED_KUN_THOM_DOUBLE.md` also makes the stable
letter visible in the external substitution quotient and identifies the
ordinary Bockstein with an explicit fold word in the full sofic radical.

## 2. The global pair

Both rings in `(SQ3)` are finitely generated unital rings.  The universal
lattice theorem gives property `(T)` to `E_r(R_+)` and `E_r(R)` for
`r>=3`.  The higher-rank groups

`Q=SL_3(Z[1/q])`, `L=SL_d(Z)`                           `(SQ6)`

also have property `(T)`.  Property `(T)` is closed under extensions, so
both groups in `(SQ4)` are Kazhdan.

The compression semigroup of `Gamma` in `G` contains every element of
`Gamma` and every nonnegative elementary substitution

`I+e_ij in SL_d(Z)`.                                   `(SQ7)`

Indeed, such a substitution sends `N^d` into `N^d`, hence maps `R_+` into
itself; it commutes with `Q`.  The matrices `(SQ7)` generate `L` as a
group.  Their conjugates of `E_r(R_+)` generate all of `E_r(R)`: for every
`v in Z^d`, choose `A_0 in SL_d(Z)` and `w in N^d` with `A_0w=v`; then the
monomial `x^v` is the `A_0`-image of `x^w`, and

`e_ij(a+b)=e_ij(a)e_ij(b)`                             `(SQ8)`

handles arbitrary Laurent polynomials.  The coefficients in `C` are
fixed by `L`, so the same argument includes the whole square-zero ideal.
Thus the compression semigroup generates `G`, proving infranormality.

The inclusion is not normal.  A determinant-one sign substitution sends
`x_1` to `x_1^(-1)`, and hence sends a positive elementary root outside
`E_r(R_+)`.

For completeness, the pair is residually finite by explicit equivariant
finite quotients.  If the external component of an element of `G` is
nontrivial, separate it in a finite quotient of `Q times L`.  Otherwise,
choose a nonzero Laurent entry of its elementary matrix.  Select a prime
`ell` not dividing `q` and an exponent modulus `m` so that this entry
survives in

`C_ell[(Z/mZ)^d]`, `C_ell=F_ell directSum F_ell^3`,     `(SQ9)`

where the second summand remains square-zero.  Reduction

`Q->SL_3(F_ell)`, `L->SL_d(Z/mZ)`                       `(SQ10)`

makes `(SQ9)` equivariant.  The resulting finite semidirect product
separates the element.  Hence `G`, and its subgroup `Gamma`, are residually
finite.  This proves Theorem 1.

## 3. The exact Baumslag--Solitar subgroup

Let `a=(0,e_1) in V <= C`; then `a^2=0`.  Let

`f=x_1+x_1^(-1) in R`,
`P=diag(1,-1,1,-1,...,1,-1) in M_r(A)`.                `(SQ11)`

The matrix `P` is invertible and has trace zero.  Put

`h=1+a f P in E_r(R)`,                                 `(SQ12)`

and let

`c=diag(q,1,q^(-1)) in Q <= Gamma`.                    `(SQ13)`

To justify the membership in `(SQ12)`, write `t=af`.  Since `t^2=0`,
`1-t=(1+t)^(-1)`, and each two-by-two diagonal block

`diag(1+t,1-t)`                                        `(SQ14)`

is elementary by the standard `w(1+t)w(-1)` factorization.  Their block
product is `h`.

The action of `c` sends `a` to `qa`, so

`c h c^(-1)=1+qafP=h^q`.                              `(SQ15)`

Moreover `h` has infinite order because

`h^n=1+nafP`                                           `(SQ16)`

in characteristic zero.  Projection to the external `Q`-factor and
`(SQ16)` show that

`B=<h,c> ~= Z[1/q] semidirect Z ~= BS(1,q)`.           `(SQ17)`

Write `U=ker(nu:B->Z)` for its translation subgroup.  Since `q=1 mod p`,
the character

`chi(h)=zeta_p`, `chi(c)=1`                            `(SQ18)`

is well defined.

## 4. The paired bar cycle

Let `O=Z[zeta_p]`, `pi=1-zeta_p`.  In the normalized integral bar complex
of `B`, put

`Z_p=sum_(j=1)^p [h^j|h]`
`    -[c|h]-[ch|c^(-1)]+[c^(-1)|c]`.                  `(SQ19)`

The direct calculation from
`FALSE_LOCALIZED_BS_PAIRED_SURVIVOR.md` depends only on `(SQ15)` and gives

`partial Z_p=p[h]`,
`partial_chi Z_p=pi[c^(-1)]`.                          `(SQ20)`

Thus the ordinary and cyclotomic Bocksteins are

`beta_1([Z_p])=[h]`, `beta_chi([Z_p])=-[c]`.           `(SQ21)`

The presentation complex of `BS(1,q)` is aspherical.  Its relator has
exponent sums `0` and `1-q=-p`, so

`H_2(B,F_p)=F_p[Z_p]`.                                 `(SQ22)`

Fox calculus with `(SQ18)` gives

`H_1(B,O_chi)=O/pi O`,                                 `(SQ23)`

generated by `[c]`.  Consequently both Bocksteins in `(SQ21)` are
injective on `(SQ22)`.

## 5. No nontrivial translation enters any stabilizer

For `g in G`, set

`S_g=B cap g Gamma g^(-1)`.                            `(SQ24)`

We prove

`S_g cap U=1`.                                         `(SQ25)`

Let `0!=s in A=Z[1/q]`.  A nontrivial element of `U` has the form

`h^s=1+safP`.                                          `(SQ26)`

Suppose, for contradiction, that `g^(-1)h^s g in Gamma`.  Reduce the
coefficient ring modulo its square-zero ideal.  Write `g_0` for the
resulting elementary matrix over

`A[x_1^(+-1),...,x_d^(+-1)]`.                          `(SQ27)`

The external `Q`-component sends `a` to a nonzero vector `w in V`; the
external `L`-component sends `f` to

`f_v=x^v+x^(-v)`                                      `(SQ28)`

for a nonzero primitive vector `v in Z^d`.  Square-zero terms in `g`
commute with the infinitesimal part of `(SQ26)`, because `V^2=0`.
Therefore the infinitesimal matrix of the conjugate has the form

`s w f_v g_0^(-1) P g_0`                              `(SQ29)`

up to reversing `g_0` and `g_0^(-1)`, which is immaterial below.

Choose a coordinate of `w` which is a nonzero scalar `b in A`.  Since the
conjugate is assumed to lie in `Gamma`, the corresponding component of
`(SQ29)` is a matrix over the positive polynomial ring

`A[x_1,...,x_d]`.                                      `(SQ30)`

Its determinant must therefore belong to that ring.  On the other hand,

`det(s b f_v g_0^(-1)Pg_0)`
` =(sb)^r det(P) f_v^r`.                               `(SQ31)`

The two extreme terms of `f_v^r` are `x^(rv)` and `x^(-rv)`, each with
coefficient one.  Since `v!=0`, at least one of these exponent vectors has
a negative coordinate, and that extreme term cannot cancel.  Hence

`f_v^r notin A[x_1,...,x_d]`,                          `(SQ32)`

contradicting `(SQ30)--(SQ31)`.  This proves `(SQ25)`.

The restriction of `nu:B->Z` to `S_g` now has trivial kernel.  Therefore
`S_g` is isomorphic to a subgroup of `Z`, and is trivial or infinite
cyclic.  In either case

`H_2(S_g,F_p)=0`.                                      `(SQ33)`

This is stronger than merely showing that the paired class avoids the
stabilizer image: every polynomial double-coset stabilizer has homological
dimension at most one.

## 6. Paired quotient and augmentation transgression

Equations `(SQ21)--(SQ23)` and `(SQ33)` give the claimed exact quotient

`H_2(B,F_p)/`
` (ker beta_1+ker beta_chi+sum_g im H_2(S_g,F_p))`
` =F_p[Z_p]`.                                          `(SQ34)`

Let

`I=Aug_(F_p)(G/Gamma)`.                                `(SQ35)`

Shapiro's lemma applied orbitwise to

`0->I->F_p[G/Gamma]->F_p->0`                           `(SQ36)`

gives

`directSum_(B g Gamma) H_2(S_g,F_p)`
` ->H_2(B,F_p) -> H_1(B,I)`.                           `(SQ37)`

The first term maps to zero by `(SQ33)`.  Hence the connecting map is
injective and

`delta([Z_p])!=0 in H_1(B,I)`.                         `(SQ38)`

Its ordinary Bockstein remains the marked translation `[h]`, where
`h` lies outside every conjugate of `Gamma` by `(SQ25)`.

## 7. What remains for FALSE

The construction now has all of the exact algebraic features which were
previously separated among incompatible examples:

1. `Gamma<G` is a residually finite Kazhdan infranormal nonnormal pair;
2. the marked subgroup is the explicit finitely presented group
   `BS(1,p+1)`;
3. its paired class is represented by the finite bar chain `(SQ19)`;
4. both Bocksteins are injective; and
5. every double-coset stabilizer has zero second homology.

The unresolved step is analytic rather than group-theoretic.  One must
choose finite quotients of `(SQ4)` and realize `(SQ38)` by unitary models
whose normalized Hilbert--Schmidt mass stays positive.  Equivalently, the
finite orbit covers must not dilute the cyclotomic carry represented by
`[c]`.  The determinant argument in Section 5 prevents exact stabilizer
absorption; the next task is to convert that qualitative exclusion into a
uniform quantitative lower bound along a finite quotient tower.
