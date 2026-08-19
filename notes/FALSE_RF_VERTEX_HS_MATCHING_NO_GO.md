# Residually finite vertex models cannot retain the parity witness

Date: 2026-08-11

## Purpose

`FALSE_COINDUCED_PARITY_MODEL.md` writes the explicit central-radical group

`E_s=A_s semidirect (G_0 *_Gamma G_0)`

as an amalgam of two residually finite groups

`E_s=J_1 *_(A_s semidirect Gamma) J_2`.

Since the final one-involution endpoint now needs only normalized
Hilbert--Schmidt approximation, it is natural to try to match honest finite
quotients, or arbitrary honest finite-dimensional representations, of the
two vertices only in normalized Hilbert--Schmidt norm.  The theorem below
rules out that entire strategy.  It strengthens the observation that exact
compatible finite quotients kill the central witness: even asymptotically
compatible exact vertex representations kill it.

## Setup

Use the compressed Kun--Thom pair `Gamma<G_0`.  Thus `Gamma` has property
`(T)`, there is a strict compressor `t in G_0`, and one may choose
`gamma in Gamma` such that

`h=t^(-1) gamma t notin Gamma`.                         `(RVH1)`

Let

`D=G_1 *_Gamma G_2`, `s=i_2(h)i_1(h)^(-1)`.           `(RVH2)`

This is a special case of the primitive fold word used in the coinduced
parity construction.  It is cyclically reduced of length two and hence has
infinite order.  Define

`A_s=F_2[D]/I(1+s)`, `E_s=A_s semidirect D`,           `(RVH3)`

and, with `z=(1+s)v`, put

`H=A_s semidirect Gamma`, `J_i=A_s semidirect G_i`.   `(RVH4)`

The previous notes prove

`E_s=J_1 *_H J_2`, `1!=z=[v,s] in Rad_sof(E_s)`.      `(RVH5)`

Both `J_i` are residually finite.

We use normalized Hilbert--Schmidt norm throughout.

## Asymptotic gluing lemma

**Lemma 1.**  Let `K=K_1 *_L K_2` be a countable group amalgam.  Suppose

`pi_(i,n):K_i -> U(d_n)`                               `(RVH6)`

are honest unitary representations and

`||pi_(1,n)(ell)-pi_(2,n)(ell)||_2 ->0`               `(RVH7)`

for every fixed `ell in L`.  Then, after fixing one amalgam normal form for
each element of `K`, evaluation of that normal form using the two
representations gives maps

`Phi_n:K->U(d_n)`                                      `(RVH8)`

whose pointwise multiplicative defects tend to zero.  The restrictions of
`Phi_n` to the two vertex groups are asymptotic to the corresponding
`pi_(i,n)`.

**Proof.**  Fix `x,y in K`.  Reducing the concatenation of the chosen normal
forms of `x` and `y` to the chosen normal form of `xy` uses finitely many
vertex multiplications and finitely many replacements of an `L`-letter in
one vertex by the same `L`-letter in the other.  Vertex multiplications are
exact by `(RVH6)`.  Every replacement error tends to zero by `(RVH7)`, and
unitary invariance plus a finite telescoping sum proves

`||Phi_n(x)Phi_n(y)-Phi_n(xy)||_2 ->0`.

The same argument applied to a one-letter vertex normal form gives the last
assertion.  End proof.

The lemma is unchanged if the two representations initially have different
dimensions and are amplified to a common dimension before `(RVH7)` is
imposed.

## A quantitative exact-lamp obstruction

The one-orbit clutching form in `FALSE_COINDUCED_PARITY_MODEL.md` suggests
implementing the shear on the lamp algebra exactly, for example by a global
Boolean bit flip, and then trying to make only the two group actions close.
Property `(T)` gives a dimension-free obstruction to precisely that ansatz.

**Theorem 2 (exact lamp matching forces a Kazhdan gap).**  Let

`pi_i:J_i->U(d)`                                        `(RVH9)`

be honest finite-dimensional unitary representations whose restrictions to
the common normal subgroup `A_s` agree exactly.  Write `Z=pi_1(z)=pi_2(z)`
and let `delta` be the relative dimension of the `-1` eigenspace of `Z`.
Then

`max_(a in S)||pi_1(a)-pi_2(a)||_2`
` >=(kappa/2)sqrt(delta)`.                            `(RVH10)`

In particular, if `Z=-1`, the two restrictions to the fixed Kazhdan set
remain at distance at least `kappa/2`.

**Proof.**  Put

`V=pi_1(v)=pi_2(v)`,
`S_h=pi_2(h)pi_1(h)^(-1)`.                            `(RVH11)`

The two exact covariance relations on the common copy of `A_s` give the
matrix identity

`Z=[V,S_h]`.                                           `(RVH12)`

Indeed, expand the commutator in `(RVH12)`.  Conjugation first by
`pi_1(h)^(-1)` and then by `pi_2(h)` acts on the common lamp algebra exactly
as `i_2(h)i_1(h)^(-1)=s`; the resulting group identity is `z=[v,s]`.

The elementary commutator estimate and the finite-representation matching
theorem now give

`||Z-1||_2 <=2||S_h-1||_2`
` =2||pi_2(h)-pi_1(h)||_2`
` <=(4/kappa) max_(a in S)||pi_1(a)-pi_2(a)||_2`.     `(RVH13)`

Since `Z` is an involution with negative relative rank `delta`,

`||Z-1||_2=2sqrt(delta)`.                             `(RVH14)`

Rearranging `(RVH13)--(RVH14)` proves `(RVH10)`.  End proof.

Thus concentrating the clutching class on one regular `Gamma`-orbit does
not allow an exact implementation of that orbit flip followed by a small
perturbation of the `Gamma` action.  Positive negative-sector rank forces a
positive edge mismatch independent of the matrix dimension.

The exact lamp hypothesis in Theorem 2 is not essential for this conclusion.
Only the single commutator relation carrying the central sign is needed.

**Theorem 2A (robust finite-window parity bound).**  Let

`alpha_i:G_0->U(d)`, `i=1,2`,                            `(RVH14a)`

be honest finite-dimensional unitary representations, let `V,Z in U(d)`,
and suppose that `Z` is an involution.  Put

`S_h=alpha_2(h)alpha_1(h)^(-1)`,
`epsilon=max_(a in S)||alpha_1(a)-alpha_2(a)||_2`,       `(RVH14b)`

and assume only the approximate parity relation

`||Z-[V,S_h]||_2<=eta`.                                 `(RVH14c)`

If `delta` is the relative dimension of the `-1` eigenspace of `Z`, then

`sqrt(delta)<=eta/2+(2/kappa)epsilon`.                  `(RVH14d)`

Equivalently,

`delta<=(eta/2+(2/kappa)epsilon)^2`.                    `(RVH14e)`

**Proof.**  The finite-representation matching theorem applied to the two
honest representations in `(RVH14a)` gives

`||S_h-1||_2=||alpha_2(h)-alpha_1(h)||_2`
`             <=(2/kappa)epsilon`.                     `(RVH14f)`

For arbitrary unitaries `V,S`,

`||[V,S]-1||_2<=2||S-1||_2`.                           `(RVH14g)`

The triangle inequality, `(RVH14c)`, `(RVH14f)`, and `(RVH14g)` therefore
give

`2sqrt(delta)=||Z-1||_2`
` <=eta+(4/kappa)epsilon`.                              `(RVH14h)`

Dividing by two proves `(RVH14d)--(RVH14e)`.  End proof.

In particular, a sequence with a fixed lower bound `delta>=delta_0>0`
must satisfy the dimension-free alternative

`eta+(4/kappa)epsilon>=2sqrt(delta_0)`.                 `(RVH14i)`

Thus permitting an approximate Boolean/lamp implementation does not rescue
honest models of the two acting copies of `G_0`.  If the edge mismatch on
the fixed Kazhdan set and the one parity-relation defect both tend to zero,
then the negative central rank tends to zero.  A successful model must be
genuinely nonliftable already in at least one acting `G_0` sector; moving the
inexactness only into the lamp coordinates cannot work.

## The general matching no-go

**Theorem 3 (exact RF vertices cannot retain `z`).**  Let

`pi_(i,n):J_i->U(d_n)`                                 `(RVH15)`

be honest finite-dimensional unitary representations such that

`||pi_(1,n)(ell)-pi_(2,n)(ell)||_2 ->0`               `(RVH16)`

for every fixed `ell in H`.  Then

`||pi_(1,n)(z)-1||_2 ->0`,
`||pi_(2,n)(z)-1||_2 ->0`.                            `(RVH17)`

In particular these compatible vertex models cannot yield a tracial
ultraproduct image retaining `z`.

**Proof.**  Restrict `(RVH15)` to the two copies of `G_0`.  The finite
representation matching theorem in
`FINITE_REPRESENTATION_MATCHING_BARRIER.md`, applied to `(RVH1)`, says

`||pi_(1,n)(h)-pi_(2,n)(h)||_2`
` <=(2/kappa) max_(a in S)`
`       ||pi_(1,n)(a)-pi_(2,n)(a)||_2`,               `(RVH18)`

where `(S,kappa)` is a fixed Kazhdan pair for `Gamma`.  The right-hand side
tends to zero by `(RVH16)`.  Apply Lemma 1 to `(RVH5)` and choose the normal
form of `s` displayed in `(RVH2)`.  Then

`||Phi_n(s)-1||_2`
` =||pi_(2,n)(h)pi_(1,n)(h)^(-1)-1||_2 ->0`.          `(RVH19)`

The group identity `z=[v,s]` in `(RVH5)` and pointwise asymptotic
multiplicativity of `Phi_n` give

`||Phi_n(z)-[Phi_n(v),Phi_n(s)]||_2 ->0`.             `(RVH20)`

For unitaries `V,S`,

`||[V,S]-1||_2<=2||S-1||_2`.                         `(RVH21)`

Equations `(RVH19)--(RVH21)` show `||Phi_n(z)-1||_2->0`.  Since `z` belongs
to the common edge group, Lemma 1 and `(RVH16)` identify `Phi_n(z)`
asymptotically with each `pi_(i,n)(z)`.  This is `(RVH17)`.  End proof.

Because `z` is an involution, `(RVH17)` equivalently says that the relative
dimension of its `-1` eigenspace tends to zero.  In particular the failure
cannot be repaired by selecting a negative spectral corner of positive
normalized rank.

## Consequence for the FALSE program

Residual finiteness of `J_1` and `J_2` does not furnish the normalized-HS
endpoint of Corollary 10 in `FALSE_MACKEY_SPLIT_COCYCLE.md`.  Profinite
regular models, arbitrary exact finite-image models, and indeed arbitrary
honest finite-dimensional unitary representations of the two vertices all
fall under Theorem 3 once their edge restrictions are made asymptotically
compatible.

Therefore a successful compatible construction must use a genuinely
nonliftable normalized-HS almost-representation on at least one vertex.  At
the operator-norm level this is the compatible-corona gate already isolated
by Shulman's criterion; the theorem here shows that weakening only the edge
matching norm to normalized Hilbert--Schmidt norm does not make residual
finiteness of the vertices sufficient.

This result does not rule out Connes embeddability of the negative central
corner or of `E_s`.  It identifies where its exoticity must occur: inside a
vertex approximation, not merely in the final act of gluing two exact RF
vertex models.
