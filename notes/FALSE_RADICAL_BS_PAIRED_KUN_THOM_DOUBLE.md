# A paired Baumslag--Solitar class marking an explicit Kun--Thom radical word

Date: 2026-08-11

## 1. Outcome

The square-zero Kun--Thom pair admits a cleaner Baumslag--Solitar subgroup
whose ordinary Bockstein is an explicit fold element in the full sofic
radical of the symmetric double.  Its stable letter has nontrivial external
substitution projection.  Since every conjugate of the polynomial subgroup
has trivial substitution projection, every double-coset stabilizer lies in
the translation subgroup of `BS(1,p+1)`.  The paired class therefore
survives all stabilizers.

This gives, in one construction:

1. a residually finite Kazhdan infranormal nonnormal pair `Gamma<G`;
2. an explicit nontrivial word `w in Rad_sof(G *_Gamma G)`;
3. an explicit finite bar cycle with ordinary Bockstein equal to the fold
   label of `w`;
4. an injective cyclotomic Bockstein; and
5. zero contribution from every double-coset stabilizer.

The remaining step toward FALSE is quantitative Hilbert--Schmidt
realization of this exact paired class.

## 2. The square-zero Kun--Thom pair

Fix an odd prime `p`, put `q=p+1`, `A=Z[1/q]`, and let

`V=A^3`, `Q=SL_3(A)`.                                  `(RB1)`

Form the commutative square-zero algebra

`C=A directSum V`, `V^2=0`,                            `(RB2)`

with `Q` acting trivially on `A` and standardly on `V`.  For `d>=3` and
even `r>=4`, put

`R_+=C[x_1,...,x_d]`,
`R=C[x_1^(+-1),...,x_d^(+-1)]`,                        `(RB3)`

`Gamma=E_r(R_+) semidirect Q`,
`G=E_r(R) semidirect (Q times L)`, `L=SL_d(Z)`.         `(RB4)`

Theorem 1 of `FALSE_SQUARE_ZERO_BS_KUN_THOM_PAIR.md` proves that both
groups are residually finite and Kazhdan, and that `Gamma<G` is
infranormal and nonnormal.

Let

`rho_L:G->L`                                           `(RB5)`

be the external substitution projection.  Then

`rho_L(g Gamma g^(-1))=1`                              `(RB6)`

for every `g in G`.

The normal closure of `Gamma` is

`N=normalClosure_G(Gamma)=E_r(R) semidirect Q`.        `(RB7)`

Indeed, it is contained in the kernel of `rho_L`; conversely, conjugates
of the positive elementary roots under `L` generate all Laurent elementary
roots, while `Q<=Gamma`.  Thus `G/N~=L`.

## 3. An explicit strict-compressor fold

Let `a=(0,e_1) in V`, and put

`P=diag(1,-1,1,-1,...,1,-1) in M_r(A)`.                `(RB8)`

As before, `1+afP` is elementary for every `f in R`: each alternating
two-by-two diagonal block is

`diag(1+af,1-af)=w(1+af)w(-1)`.                       `(RB9)`

In `L`, take the commuting nonnegative transvections

`t=I+e_12`, `s=I+e_13`.                                `(RB10)`

They are genuine compressors of `Gamma`.  With column-vector conventions,

`t^(-1)e_2=e_2-e_1=:v`, `s v=v`.                       `(RB11)`

Define

`gamma=1+a x_2 P in Gamma`,
`h=t^(-1) gamma t=1+a x^v P`.                          `(RB12)`

The exponent `v=e_2-e_1` has a negative coordinate, so `h notin Gamma`.
On the other hand `h in N` by `(RB7)`; more precisely it is the inverse
conjugate of the polynomial element `gamma` by the strict compressor `t`.

Let

`c_0=diag(q,1,q^(-1)) in Q`,
`c=(c_0,s) in Q times L <=G`.                          `(RB13)`

The `Q`-component sends `a` to `qa`, while `(RB11)` says that the
substitution component fixes `x^v`.  Therefore

`c h c^(-1)=1+qa x^vP=h^q`.                           `(RB14)`

The element `s` has infinite order, and `h` has infinite order because

`h^n=1+na x^vP`.                                      `(RB15)`

Projection to `L` and `(RB15)` prove

`B=<h,c> ~= Z[1/q] semidirect Z ~= BS(1,q)`.           `(RB16)`

Write `nu:B->Z` for the stable-letter exponent and `U=ker(nu)`.

## 4. The paired cycle

Since `q=1 mod p`, define

`chi(h)=zeta_p`, `chi(c)=1`.                           `(RB17)`

Let `O=Z[zeta_p]`, `pi=1-zeta_p`.  The normalized integral bar chain

`Z_p=sum_(j=1)^p [h^j|h]`
`    -[c|h]-[ch|c^(-1)]+[c^(-1)|c]`                   `(RB18)`

satisfies

`partial Z_p=p[h]`,
`partial_chi Z_p=pi[c^(-1)]`.                          `(RB19)`

Consequently

`beta_1([Z_p])=[h]`, `beta_chi([Z_p])=-[c]`.           `(RB20)`

The standard aspherical presentation of `BS(1,q)` and its Fox complex give

`H_2(B,F_p)=F_p[Z_p]`,
`H_1(B,O_chi)=O/pi O [c]`.                             `(RB21)`

Both Bocksteins in `(RB20)` are therefore injective.

## 5. Every stabilizer lies in the translation subgroup

For `g in G`, set

`S_g=B cap g Gamma g^(-1)`.                            `(RB22)`

An element of `B` with stable-letter exponent `m` has substitution
projection

`rho_L(b)=s^m`.                                        `(RB23)`

By `(RB6)`, every element of `g Gamma g^(-1)` has trivial substitution
projection.  Since `s` has infinite order, `(RB23)` implies

`S_g<=U`                                               `(RB24)`

for every `g`.

The inclusion of the translation subgroup induces zero on the relevant
twisted first homology:

`H_1(U,O_chi)->H_1(B,O_chi)` is zero.                  `(RB25)`

Indeed, in the Lyndon--Hochschild--Serre five-term sequence for

`1->U->B->Z->1`,                                      `(RB26)`

the map

`H_1(B,O_chi)->H_1(Z,(O_chi)_U)=F_p`                  `(RB27)`

is an isomorphism: both sides are generated by the stable-letter class
`[c]`.  Thus the preceding fiber map has zero image.

Naturality of the cyclotomic Bockstein and `(RB24)--(RB25)` give

`beta_chi(im(H_2(S_g,F_p)->H_2(B,F_p)))=0`.            `(RB28)`

Since `beta_chi` is injective by `(RB20)--(RB21)`, every stabilizer map in
degree two is zero.  Therefore

`H_2(B,F_p)/`
` (ker beta_1+ker beta_chi`
`  +sum_g im H_2(S_g,F_p))`
` =F_p[Z_p]`.                                          `(RB29)`

For `I=Aug_(F_p)(G/Gamma)`, Shapiro's lemma and

`0->I->F_p[G/Gamma]->F_p->0`                           `(RB30)`

now show that the connecting homomorphism is injective on `[Z_p]`:

`delta([Z_p])!=0 in H_1(B,I)`.                         `(RB31)`

Its ordinary Bockstein is exactly the fold label `[h]`.

## 6. The explicit sofic-radical word

Form the symmetric double

`D=G *_Gamma G`,                                      `(RB32)`

with vertex embeddings `i_1,i_2`, and put

`w=i_2(h)i_1(h)^(-1)`.                                 `(RB33)`

The complete-radical theorem for a Kun--Thom symmetric double says

`Rad_sof(D)=ker(D->G *_N G)`,                          `(RB34)`

where `N` is the normal closure of `Gamma` in `G`.  Since `h in N`,
`(RB33)` lies in this kernel.  Since `h notin Gamma`, the normal-form
theorem for amalgamated free products shows `w!=1`.  Hence

`1!=w in Rad_sof(D)`.                                  `(RB35)`

Under the Bass--Serre relation-module identification, the fold class of
`w` is

`e_h=delta_(hGamma)-delta_Gamma in Aug_Z(G/Gamma)`.     `(RB36)`

Thus `(RB20)` and `(RB31)` are not merely unmarked homology: the ordinary
Bockstein is the exact group element indexing the radical edge `(RB36)`.

## 7. Remaining analytic statement

The algebraic construction reduces FALSE to a quantitative realization of
one fixed finite cycle.  It is enough to produce finite-dimensional
unitary models of the double `(RB32)` for which

1. the normalized Hilbert--Schmidt defects of every fixed relator tend to
   zero; and
2. the fold word `(RB33)` stays a positive normalized Hilbert--Schmidt
   distance from the identity.

The paired class `(RB18)` supplies the exact obstruction to simultaneous
ordinary and cyclotomic integral repair, and `(RB29)` proves that no
double-coset stabilizer absorbs it.  What is not yet proved is a uniform
finite-quotient lower bound: qualitative nonabsorption must be upgraded to
a marked-discriminant ratio tending to infinity, or equivalently to a
small-phase model whose tensor amplification retains `(RB33)`.
