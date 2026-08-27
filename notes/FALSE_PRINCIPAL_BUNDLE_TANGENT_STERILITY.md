# Exact tangent absorption of the principal-bundle cocycle is sterile

Date: 2026-08-11

## 1. Outcome

The exact principal-bundle cocycle from
`FALSE_EXACT_PRINCIPAL_BUNDLE_EXTERNAL_COMPLETION.md` cannot be absorbed by
the most obvious fiberwise tangent functor.  That absorption makes the
whole vertex/external representation a global gauge conjugate of an
ordinary finite model.  If two such sectors agree exactly on the amalgam,
their fold word is killed.

This does not contradict the long Frobenius chain in
`FALSE_LONG_FROBENIUS_ELEMENTARY_COMPRESSOR.md`.  The long chain is
deliberately nonperiodic on every fixed window and closes only at a depth
which tends to infinity.  Its covariance may be asymptotically exact, but
it must not be replaced by the exact global gauge pullback below.

## 2. The tautological absorption formula

Let a finite group `K` act by automorphisms `alpha_k` on a group `P`, and
let

`rho:P->U(H)`                                          `(PTS1)`

be a finite-dimensional representation.  On

`calH=directSum_(x in K) H_x`,                         `(PTS2)`

define the untwisted vertex representation

`Pi(p)|_(H_x)=rho(alpha_(x^(-1))(p))`.                `(PTS3)`

Let `Lambda(k)` be left translation of the `K` index.  Then

`Lambda(k)Pi(p)Lambda(k)^(-1)=Pi(alpha_k(p))`,        `(PTS4)`

so `(Pi,Lambda)` is an exact representation of `P semidirect K`.

Now choose an arbitrary function

`varphi:K->U(H)`                                      `(PTS5)`

and let `W_varphi` be the block-diagonal unitary whose `x` block is
`varphi(x)`.  Define

`Pi_varphi(p)=W_varphi Pi(p)W_varphi^(-1)`,
`Lambda_varphi(k)=W_varphi Lambda(k)W_varphi^(-1)`.   `(PTS6)`

Equivalently,

`Pi_varphi(p)|_(H_x)`
` =varphi(x)rho(alpha_(x^(-1))(p))varphi(x)^(-1)`,    `(PTS7)`

and the fiber operator on the edge `x->kx` is

`varphi(kx)varphi(x)^(-1)`.                           `(PTS8)`

The latter is exactly the principal-bundle coboundary.  Formula `(PTS6)`
proves at once that `(Pi_varphi,Lambda_varphi)` is an exact covariant
representation.

But `(PTS6)` also proves sterility:

`(Pi_varphi,Lambda_varphi)` is unitarily equivalent to `(Pi,Lambda)`.
                                                               `(PTS9)`

No nontrivial sector has been created; only the gauge of one finite model
has changed.

## 3. Consequence for the radical double

Take two potentials `varphi_0,varphi_1` and the corresponding exact
representations of the finite semidirect model.  Suppose, after placing
them on one Hilbert space, that their restrictions to the image of
`Gamma` agree exactly.  The universal property then gives a
finite-dimensional unitary representation of

`D=G *_Gamma G`.                                      `(PTS10)`

Its image is a finitely generated linear group, hence residually finite by
Malcev's theorem and therefore sofic.  Every element of `Rad_sof(D)` is
killed by every homomorphism to a sofic group.  In particular the marked
word

`w=i_2(h)i_1(h)^(-1)`                                 `(PTS11)`

maps to the identity.

Thus an exact common-amalgam implementation of `(PTS6)` can never retain
the fold.  In direct calculations the same cancellation appears because
the vertex operator assigned to `h` is transported by the same potential
which created the constant fiber holonomy on the `t` edges.

## 4. Correct use of the principal bundle

The principal bundle remains useful for making the **external group law**
exact with a prescribed compressor matrix.  What is forbidden is absorbing
its cocycle into the entire vertex representation by `(PTS7)` at every
finite stage.

The long Frobenius construction instead supplies two vertex functors which
agree on a positive window of depth `M` but disagree on the inverse marked
element.  The first failure of exact periodicity occurs only at the next
depth.  Letting `M->infinity` makes every fixed positive word eventually
correct while the inverse fold remains macroscopic.

The outstanding simultaneous-coherence theorem must therefore satisfy:

1. exact or asymptotically exact external multiplication;
2. covariance on every fixed vertex word;
3. no global formula of the form `(PTS6)` for the whole vertex group; and
4. fold energy bounded away from zero.

This is the precise non-Cartan content of the remaining problem.
