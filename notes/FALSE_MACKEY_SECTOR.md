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

## 5. The exact Paddock gate, and why the Mackey model misses it

Paddock's rounding theorem (arXiv:2203.02525v5, especially Definitions
3.24--3.25 and Lemma 3.26) starts with a state-dependent approximate
representation `phi` of a finitely presented star algebra generated by
self-adjoint unitaries.  In addition to small relation error in the state
norm, it assumes approximate traciality:

`||phi(s)sqrt(rho)-sqrt(rho)phi(s)||_F -> 0`           `(MPS18)`

for every generator.  It then produces a normalized-Frobenius approximate
representation on a nonzero spectral subspace.

There is a useful correction to the first superficial objection.  No lower
bound on the output subspace's relative dimension is needed **if** the input
models keep `z=-1` exactly: compression to any nonzero subspace still makes
`z` the scalar `-1`, and the output Hilbert--Schmidt norm is normalized by
the output dimension.  Subject to the self-adjoint-generator encoding, a
sequence satisfying Paddock's hypotheses and retaining `z=-1` would already
produce a hyperlinear image in which the radical element survives.  It
would solve the FALSE lane.

The unmet hypothesis is `(MPS18)`, not output dimension.  The exact Mackey
representation `(MPS14)` does not provide approximately central finite-rank
density matrices.  Already its first vertex restriction

`pi_0=Ind_C^G(1)`                                      `(MPS19)`

is nonamenable.  Indeed `G=H*Z` is nonamenable, while the cyclic subgroup
`C` is amenable.  If `C` were coamenable in `G`, amenability of `C` and of
the homogeneous action `G/C` would imply amenability of `G`, a
contradiction.  Thus `C` is not coamenable.  An invariant state for
`pi_0(G)` on `B(ell^2(G/C))` would restrict to a `G`-invariant mean on the
diagonal algebra `ell^infinity(G/C)`, so no such state exists.

In particular, a net of finite-rank density matrices satisfying

`||[pi_0(g),sqrt(rho_i)]||_F -> 0`, `g in G`,          `(MPS20)`

would yield an invariant state by a weak-star limit and is impossible.
Hence finite-dimensional compressions of the exact Mackey representation
cannot supply Paddock's approximate-tracial input.

Paddock is therefore a sharp conditional converter: it shows that
state-dependent tracial models with `z=-1` are enough, but it does not
manufacture those models from an operator-norm MF embedding or from the
exact induced representation.  The self-adjoint-unitary presentation
requirement is an additional encoding task, but `(MPS18)--(MPS20)` is the
prior obstruction.

The live target is now:

> prove that the C-star algebra generated by the Mackey-paired induced
> representations `(MPS11)--(MPS16)` is MF.

This remains open.
