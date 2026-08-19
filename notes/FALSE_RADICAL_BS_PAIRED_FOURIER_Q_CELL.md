# An exact paired Fourier--Q cell for the radical fold

Date: 2026-08-11

## 1. Outcome

The diagonal clock block from
`FALSE_RADICAL_BS_Q_BIMODULE_EXTENSION.md` realizes the Laurent-side
marked element, but by itself it does not exhibit the common positive-side
operator whose two inverse compressor conjugates give the fold.  There is
an exact finite-dimensional enlargement which does.

Fix an odd prime `p`, put `q=1+p`, and, for `n>=2`, let

`A_n=Z/p^n Z`, `V_n=A_n^3`, `Q_n=SL_3(A_n)`.          `(PFQ1)`

Let

`c_0=diag(q,1,q^(-1))`, `a=e_1`.                      `(PFQ2)`

On

`H_n=ell^2(Q_n times V_n times V_n)`                  `(PFQ3)`

there are two exact `Q_n`-covariant representations of the additive
module `V_n`:

* a translation representation `A_n(v)`; and
* a multiplier representation `D_n(v)`.

There are also unitaries `U_n,T_n,C_n` such that

`U_n A_n(v) U_n^(-1)=D_n(v)`,                         `(PFQ4)`

`[T_n,A_n(v)]=1`,
`T_n D_n(v)T_n^(-1)=D_n(v)^q`,                        `(PFQ5)`

and `C_n` commutes with `U_n,T_n` while acting by `c_0` on both additive
representations.  All these statements are exact.  Here `C_n` realizes
the coefficient-`Q_n` component of the Baumslag--Solitar stable letter;
the external substitution component `s` is part of the remaining global
covariance problem.

Define two choices for the strict compressor letter by

`S_(0,n)=U_n^(-1)`,
`S_(1,n)=U_n^(-1)T_n^(-1)`.                           `(PFQ6)`

They have identical forward action on the entire common translation
module:

`S_(0,n) A_n(v)S_(0,n)^(-1)`
` =S_(1,n) A_n(v)S_(1,n)^(-1)`                        `(PFQ7)`

for every `v`.  On the inverse conjugate of the marked element they give

`S_(0,n)^(-1)A_n(a)S_(0,n)=D_n(a)`,
`S_(1,n)^(-1)A_n(a)S_(1,n)=D_n(a)^q`.                 `(PFQ8)`

Consequently the fold is `D_n(a)^(q-1)=D_n(a)^p`, and

`tr_(H_n)(D_n(a)^p)=0`,
`||D_n(a)^p-1||_2^2=2`.                               `(PFQ9)`

Thus the local cell simultaneously has a literal common positive module,
identical forward compressor covariance, exact `Q_n` covariance, exact
coefficient-side `q`-scaling on the Laurent side, and a macroscopic fold.
This is stronger than a clock model in which the common positive operator
has not yet been constructed.

The remaining global problem is to replace the one finite additive module
in this theorem by a finite Frobenius model of the full square-zero Laurent
tangent module, so that the Fourier exchange in `(PFQ4)` is the actual
monomial substitution by the strict compressor on every tested tangent and
base-elementary generator.

## 2. The two additive representations

Use the perfect pairing

`<y,x>=y^T x/p^n mod Z`, `x,y in V_n`,                `(PFQ10)`

and write `e(z)=exp(2 pi i z)`.  In the basis
`delta_(g,x,y)` of `(PFQ3)`, define

`A_n(v)delta_(g,x,y)=delta_(g,x+g^(-1)v,y)`,          `(PFQ11)`

`D_n(v)delta_(g,x,y)`
` =e(<y,g^(-1)v>)delta_(g,x,y)`.                      `(PFQ12)`

Both maps are additive representations:

`A_n(v+w)=A_n(v)A_n(w)`,
`D_n(v+w)=D_n(v)D_n(w)`.                              `(PFQ13)`

Let the coefficient group act by

`L_n(u)delta_(g,x,y)=delta_(ug,x,y)`.                 `(PFQ14)`

Direct substitution gives the exact covariance identities

`L_n(u)A_n(v)L_n(u)^(-1)=A_n(uv)`,
`L_n(u)D_n(v)L_n(u)^(-1)=D_n(uv)`.                    `(PFQ15)`

These formulas explain the `g^(-1)` in `(PFQ11)--(PFQ12)`: the fiber
coordinates themselves can remain fixed under left `Q_n`, while the two
families transform by the standard module action.

## 3. Fourier exchange

Choose the finite Fourier transform `F_n` on `ell^2(V_n)` with convention

`F_n tau_z F_n^(-1)=M_z`,                             `(PFQ16)`

where `tau_z` is translation by `z` and
`M_z delta_y=e(<y,z>)delta_y`.  Let `J` swap the two `V_n` factors and put

`U_n=1_(ell^2(Q_n)) tensor J(F_n tensor 1)`.           `(PFQ17)`

On the fiber over `g`, `(PFQ11)` is translation by `g^(-1)v` in the
first `V_n` coordinate.  Equation `(PFQ16)` followed by the swap therefore
gives `(PFQ4)` simultaneously for every `v`.

The operator `U_n` acts identically on every `g`-fiber, so

`[U_n,L_n(u)]=1`                                      `(PFQ18)`

for all `u in Q_n`.

## 4. A right bimodule gauge which fixes translations and shears multipliers

Put

`K_n=q^(-1)c_0^T in GL_3(A_n)`                       `(PFQ19)`

and define the permutation unitary

`T_n delta_(g,x,y)`
` =delta_(g c_0,c_0^(-1)x,K_n y)`.                   `(PFQ20)`

It commutes with every left `Q_n` operator in `(PFQ14)`.  Moreover,
applying `T_n^(-1)`, then `(PFQ11)`, then `T_n`, changes the first fiber
coordinate by

`c_0^(-1)(c_0 g^(-1)v)=g^(-1)v`.                     `(PFQ21)`

This proves the first identity in `(PFQ5)`.

For the multiplier family, the phase after the same conjugation is

`<K_n^(-1)y,c_0 g^(-1)v>`
` =<y,K_n^(-T)c_0 g^(-1)v>`
` =q<y,g^(-1)v>`,                                     `(PFQ22)`

because `(PFQ19)` gives `K_n^(-T)c_0=qI`.  This proves
the second identity in `(PFQ5)`.

Finally set

`C_n=L_n(c_0)`.                                       `(PFQ23)`

Equations `(PFQ15)` imply

`C_n A_n(a)C_n^(-1)=A_n(a)^q`,
`C_n D_n(a)C_n^(-1)=D_n(a)^q`.                        `(PFQ24)`

Left/right commutation and `(PFQ18)` show

`[C_n,T_n]=[C_n,U_n]=1`.                              `(PFQ25)`

Thus the coefficient component `c_0` of the Baumslag--Solitar stable
letter commutes with either compressor choice in `(PFQ6)` and scales both
marked additive realizations correctly.  To represent the actual element
`c=(c_0,s)`, one must additionally represent the commuting external
substitution `s` and verify that it fixes the marked Laurent monomial.

## 5. Common forward covariance and the visible inverse fold

Since `T_n` commutes with every `A_n(v)`, `(PFQ6)` gives

`S_(1,n)A_n(v)S_(1,n)^(-1)`
` =U_n^(-1)T_n^(-1)A_n(v)T_nU_n`
` =U_n^(-1)A_n(v)U_n`
` =S_(0,n)A_n(v)S_(0,n)^(-1)`.                       `(PFQ26)`

This is `(PFQ7)`.  In the opposite conjugation direction, `(PFQ4)` and
`(PFQ5)` give

`S_(0,n)^(-1)A_n(a)S_(0,n)=D_n(a)`,                  `(PFQ27)`

`S_(1,n)^(-1)A_n(a)S_(1,n)`
` =T_nD_n(a)T_n^(-1)=D_n(a)^q`.                      `(PFQ28)`

The distinction between `(PFQ26)` and `(PFQ27)--(PFQ28)` is the strict
compressor geometry: the positive forward image is common, while the
inverse conjugate lies outside the common positive subgroup and carries
the fold.

To prove `(PFQ9)`, average `(PFQ12)` over the final coordinate `y`.  For
every fixed `g`, the vector `g^(-1)a` is primitive, hence
`p g^(-1)a` is nonzero in `V_n` when `n>=2`.  Nontrivial-character
orthogonality gives

`(1/|V_n|)sum_(y in V_n)e(<y,p g^(-1)a>)=0`.          `(PFQ29)`

The remaining `g,x` averages do not change zero.  Thus
`tr(D_n(a)^p)=0`; the identity

`||W-1||_2^2=2-2 Re tr(W)`                            `(PFQ30)`

proves the second part of `(PFQ9)`.

## 6. What this closes and what it does not

The theorem closes the local compatibility which a diagonal clock alone
does not address.  The relative gauge `T_n` commutes with the literal
common positive additive representation, not with the Laurent multiplier.
The Fourier wall `U_n` turns that harmless common-side gauge into the
macroscopic Laurent fold.

The abstract external group can still be added at the level of its own
presentation after diffuse
multiplicity amplification: tensor the compressor choices in `(PFQ6)`
with a long-cycle unitary so their spectral measures tend to Haar, then
apply the prescribed-generator completion theorem separately in the two
sectors.  This observation addresses only the external presentation
relations.  It does not prove that the resulting matrix for the second
transvection `s` fixes `D_n(a)`, which is one of the monomial-covariance
conditions below.

It remains to construct, on one finite Frobenius module, additive families
for all tested elements of

`sl_r(V[x_1^(+-1),...,x_d^(+-1)])`                    `(PFQ31)`

and the base elementary group so that `U_n` implements the actual strict
monomial substitution rather than an abstract Fourier exchange.  The
fixed-base square-zero jet formulas in `notes/NOTEPAD.md` provide exact
one-chart candidates, but their simultaneous multi-compressor atlas was
not completed.  No claim about a full microstate of `G` or its double is
made here.

## 7. Exact endpoint needed from the remaining completion

For clarity, faithfulness of a limiting model of the whole double is not
an additional requirement.  The following elementary endpoint is enough.

**Proposition (marked compatible-pair endpoint).**  Suppose there are
finite-dimensional maps

`phi_(i,n):G -> U(k_n)`, `i=0,1`,                     `(PFQ32)`

such that

1. both sequences are asymptotic homomorphisms in normalized HS norm;
2. for every `gamma in Gamma`,

   `||phi_(0,n)(gamma)-phi_(1,n)(gamma)||_2 ->0`;      `(PFQ33)`

3. for the marked `h` in `(RB12)`,

   `liminf_n ||phi_(1,n)(h)phi_(0,n)(h)^(-1)-1||_2>0`.
                                                               `(PFQ34)`

Then a hyperlinear nonsofic group exists.

**Proof.**  The two limiting homomorphisms into the tracial matrix
ultraproduct agree on `Gamma` by `(PFQ33)`.  The universal property of the
amalgamated free product therefore gives a homomorphism

`Psi:D=G *_Gamma G -> product_omega U(k_n)`.          `(PFQ35)`

Its image is hyperlinear.  Condition `(PFQ34)` says that the radical word

`w=i_2(h)i_1(h)^(-1)`                                 `(PFQ36)`

survives in `im(Psi)`.  If `im(Psi)` were sofic, the composite map from
`D` to that sofic group would have to kill every element of
`Rad_sof(D)`, in particular `w`, contradicting `(PFQ34)`.  Hence
`im(Psi)` is hyperlinear and nonsofic.  End proof.

The paired cell gives `(PFQ33)` and `(PFQ34)` exactly on the additive
`Q_n`-covariant compressor window: the common operators are `A_n(v)` and
their common forward images `(PFQ7)`, while `(PFQ9)` gives the marked
lower bound.  The sole missing input to the proposition is extension of
these assignments to asymptotic homomorphisms on every fixed window of
the full vertex group `G`, with agreement on every fixed element of
`Gamma`.
