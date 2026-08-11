# FALSE lane: an exact Mackey model for the shear sector

Date: 2026-08-10

This note constructs the missing nontrivial central sector of the cyclic
radical shear as an **exact infinite-dimensional representation**.  It does
not prove that the sector is MF.  Its purpose is to replace an abstract
projective-cocycle existence problem by one concrete C-star algebra whose MF
property would finish the FALSE lane.

## 1. The cyclic radical shear

Let `G` act on a tree with trivial edge stabilizers and let `r in G` be a
primitive hyperbolic element.  Put

`C=<r> isomorphic Z`,                                      `(MPS1)`

so `C_G(r)=C`.  Let `chi:C->C^x` be the parity character

`chi(r^n)=(-1)^n`.                                        `(MPS2)`

The free-stabilized radical construction in the notebook has exactly this
form: `G=H*<a>` and `r=[r_0,a]`, where
`1!=r_0 in Rad_sof(H)`.

Put `B=G times <z>`, where `z^2=1`, and let

`A=C times <z>`.

Define the involution

`alpha(r^n,z^e)=(r^n,z^(e+n mod 2))`                    `(MPS3)`

and form

`J=B *_((A,id),(A,alpha)) B`.                           `(MPS4)`

The earlier centralizer-shear theorem proves that `z` is a nontrivial
central element of `Rad_sof(J)`.

## 2. Mackey parity pairing

Let

`pi_0=Ind_C^G(1)`,  `pi_1=Ind_C^G(chi)`.               `(MPS5)`

**Theorem (Mackey parity pairing).**  There is a unitary `U` between the
Hilbert spaces in `(MPS5)` such that

`U pi_1(c) U^* = chi(c) pi_0(c)` for every `c in C`.    `(MPS6)`

**Proof.**  Mackey restriction over `C\G/C` gives

`Res_C Ind_C^G(sigma)`
`  ~= directSum_t Ind_(L_t)^C(sigma^t|_(L_t))`,         `(MPS7)`

where `L_t=C intersect tCt^(-1)`.  Tensoring an induced representation by
`chi` tensors its inducing character by `chi|_(L_t)`.  It is therefore
enough to prove

`chi|_(L_t) times chi^t|_(L_t)=1`.                     `(MPS8)`

This is automatic when `L_t=1`.  Otherwise take a nonzero element of
`L_t` and write it as

`r^m=t r^n t^(-1)`,  `m,n!=0`.                         `(MPS9)`

Translation length in the tree is invariant under conjugacy.  Since `r` is
hyperbolic,

`|m| length_T(r)=|n| length_T(r)`,

and hence `n=+-m`.  Consequently

`chi(r^m) chi(r^n)=(-1)^(m+n)=1`.                      `(MPS10)`

The same calculation applies to every element of `L_t`.  Thus `(MPS8)`
holds on every Mackey summand, and summing the resulting equivalences gives
`(MPS6)`.  End proof.

Notice that malnormality is not required.  Possible axis inversion causes
`n=-m`, which preserves parity and is harmless.

## 3. An exact negative-central representation

On the Hilbert space of `pi_0`, define two representations of `B` by

`beta_1(g,z^e)=(-1)^e pi_0(g)`,                         `(MPS11)`

`beta_2(g,z^e)=(-1)^e U pi_1(g) U^*`.                  `(MPS12)`

For `r^n z^e in A`, equations `(MPS3)` and `(MPS6)` give

`beta_2(alpha(r^n,z^e))`
` =(-1)^(e+n) U pi_1(r^n) U^*`
` =(-1)^(e+n) (-1)^n pi_0(r^n)`
` =beta_1(r^n,z^e)`.                                   `(MPS13)`

The universal property of the amalgam therefore gives an exact
representation

`Pi:J->U(K_Mac)`                                       `(MPS14)`

whose restrictions to the two vertices are `beta_1,beta_2`.  Crucially,

`Pi(z)=-1_(K_Mac)`.                                    `(MPS15)`

Thus the projective `-1` sector is not obstructed at the level of
infinite-dimensional representation theory.  It exists canonically as the
pair of the quasi-regular representation and its parity-induced companion.

## 4. A single concrete MF target

Let

`A_Mac=C^*(Pi(J)) subset B(K_Mac)`.                    `(MPS16)`

**Corollary.**  If `A_Mac` is MF, then a hyperlinear nonsofic group exists.

**Proof.**  Embed `A_Mac` into a norm matrix corona and lift a countable
dense family.  Passing the coordinate matrices to their normalized
Hilbert--Schmidt ultraproduct gives a group homomorphism from `Pi(J)` into a
tracial matrix ultraproduct.  Its kernel may be nontrivial, but `(MPS15)`
shows that the image of `z` remains the scalar `-1`, at Hilbert--Schmidt
distance `2` from the identity.  The resulting image group is hyperlinear.

If that image group were sofic, the composite homomorphism from `J` to this
sofic group would have to kill `z`, because `z in Rad_sof(J)`.  It does not.
Hence the image group is nonsofic.  End proof.

This is strictly more concrete than the abstract projective-sector
criterion: it asks whether the one explicitly generated algebra `(MPS16)`
is MF.

There is some additional structure.  Since `C` is amenable, both induced
representations in `(MPS5)` are weakly contained in the regular
representation of `G`: every representation of `C` is weakly contained in
`lambda_C`, induction preserves weak containment, and

`Ind_C^G(lambda_C) ~= lambda_G`.                        `(MPS17)`

Therefore each vertex algebra in `(MPS16)` is a quotient of `C_r^*(G)`.
In the application, `G=H*Z` is C-star simple: a free product of two
nontrivial groups, one of which has more than two elements, is a Powers
group and has simple reduced group C-star algebra.  Hence the two nonzero
representations of `C_r^*(G)` in `(MPS5)` are faithful.  Each vertex algebra
in `(MPS16)` is therefore actually isomorphic to `C_r^*(G)`, not merely a
quotient.

This does not by itself prove MF.  It is not known here that `C_r^*(G)` is
MF, and even MF vertex algebras require compatible norm-corona embeddings
across the twisted edge.  The observation nevertheless localizes the target
to two faithful tempered copies of one reduced group C-star algebra rather
than an unspecified cocycle sector.

## 5. Why Paddock does not close this target

Paddock's rounding theorem (arXiv:2203.02525v5, especially Lemma 3.26)
starts with a state-dependent approximately tracial representation of a
finitely presented star algebra generated by self-adjoint unitaries.  It
produces a normalized-Frobenius approximate representation on a **nonzero**
spectral subspace.  The theorem is dimension-independent, but it gives no
positive lower bound on the output subspace's dimension divided by the
input dimension.

That is valuable for passing from arbitrary states to maximally entangled,
tracial models.  It does not pass in the other direction from the exact
infinite representation `(MPS14)` to operator-norm microstates for
`A_Mac`, and it cannot force an operator-norm-visible sector of negligible
relative rank to acquire positive normalized trace.  Consequently it is an
upstream tracial-normalization tool, not the MF certificate required in
`(MPS16)`.

The live target is now:

> prove that the C-star algebra generated by the Mackey-paired induced
> representations `(MPS11)--(MPS16)` is MF.

This remains open.
