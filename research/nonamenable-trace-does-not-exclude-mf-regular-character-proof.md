---
rg: 2
id: nonamenable-trace-does-not-exclude-mf-regular-character-proof
kind: route
title: "LEF regular models plus Kirchberg's (T)-dichotomy give the witness; Arveson-extended local lifts give the LLP lemma"
target: nonamenable-trace-does-not-exclude-mf-regular-character
requires:
  - continuum-many-simple-kazhdan-lef-groups
  - lef-implies-operator-mf
  - simple-kazhdan-group-lacks-factorization-property
  - elementary-group-trace-amenable-iff-ring-residually-finite
  - llp-non-rf-kazhdan-group-is-non-hyperlinear
  - elementary-groups-over-fg-rings-have-property-t
---

**(i) Witness.** By `continuum-many-simple-kazhdan-lef-groups` (see also
`simple-kazhdan-group-lacks-factorization-property`), `G = G_X` is finitely
generated, infinite, simple, Kazhdan and LEF.

*MF regular character.* Fix windows `W_1 ⊂ W_2 ⊂ ...` exhausting `G`. For
each `k` choose a finite group `Q_k` and a map `phi_k : G -> Q_k` that is
injective on `W_k` and satisfies `phi_k(gh) = phi_k(g) phi_k(h)` for
`g, h, gh` in `W_k`. Set `sigma_k = lambda_{Q_k} o phi_k`. For `g, h` fixed,
eventually `sigma_k(gh) = sigma_k(g) sigma_k(h)` exactly. For `g != e` fixed,
eventually `phi_k(g) != e`, so `lambda_{Q_k}(phi_k(g))` is a fixed-point-free
permutation matrix and `tr sigma_k(g) = 0`. This is the construction of
`lef-implies-operator-mf`, with the trace read off. So `delta_e` is an MF
character.

*Non-amenable.* `simple-kazhdan-group-lacks-factorization-property` shows
`G` lacks Kirchberg's factorization property. For the regular character this
is the statement that `tau_G` is not amenable on `C*(G)`; this is the form
used by `elementary-group-trace-amenable-iff-ring-residually-finite`.
Quasidiagonal traces are amenable, so `tau_G` is not QD either.

The ring `LC(X,F_2) rtimes Z` is finitely generated, simple and infinite.
So `G` lies in the scope of Corollary A of
`elementary-group-trace-amenable-iff-ring-residually-finite`.

**(ii) Lifting lemma.** Let `A = C*(G)`, let `B = prod_k M_{d_k}`, and let
`q : B -> B/K` be the quotient, with `K` either `(+) M_{d_k}` (the norm
corona) or the trace-norm ultrapower ideal `J_omega`. Let
`pi : A -> B/K` be a `*`-homomorphism with `tau = tr_omega o pi`.

Fix a finite set `F ⊂ G` with `e ∈ F = F^{-1}`, and let `O_F` be the
finite-dimensional operator system spanned by `F ∪ F·F`. By LLP, `pi|O_F`
has a ucp lift `psi : O_F -> B`. `B` is injective, so Arveson's theorem
extends `psi` to a ucp map `psi : A -> B`. Write `psi_k` for its
coordinates. For `g, h ∈ F`, the elements `psi(gh)` and `psi(g) psi(h)`
both lift `pi(g) pi(h)`, so `psi(gh) - psi(g) psi(h) ∈ K`. For both choices
of `K`, this gives

    lim_omega || psi_k(gh) - psi_k(g) psi_k(h) ||_2 = 0.

Also `lim_omega tr psi_k(g) = tr_omega(pi(g)) = tau(g)`.

Take an increasing exhaustion by sets `F`. The ucp maps are contractive and
`C[G]` is dense in `A`. A diagonal choice of coordinates then gives ucp maps
`A -> M_{d}` that are asymptotically multiplicative in 2-norm on all of `A`,
with traces tending to `tau`. That is Brown's definition of an amenable
trace.

No property (T) is used here. The case `K = J_omega` says: under LLP, every
hyperlinear trace is amenable. This is Ozawa's remark recorded in
`llp-non-rf-kazhdan-group-is-non-hyperlinear`.

**Sanity check against (i).** `delta_e` is MF on `G_X` and not amenable, so
by (ii) `C*(G_X)` fails LLP. This agrees with
`simple-kazhdan-lef-group-c-star-fails-llp`, where the failure is derived
from hyperlinearity.

**(iii) The Jacobson lane.** `J = F_2<S,T | TS=1>` is finitely generated.
`J` is not RF: in a finite quotient `J/I`, the image of `T` is a left inverse
of the image of `S`, hence a two-sided inverse, so `Q = 1 - ST ∈ I`. Hence
`I` contains the nonzero ideal `JQJ`. By
`elementary-group-trace-amenable-iff-ring-residually-finite`, `tau_E` is not
amenable for `E = EL_5(J)`. That is (A).

- (A) and (B) imply (H1). If `delta_e` were MF, (B) would make it amenable,
  contradicting (A).
- (A) and not-(B) hold for `G_X` by (i). So (B) is the only
  distinguishing input.
- Suppose (B) is proved by any tracially blind bridge, meaning one whose
  argument works verbatim for `K = J_omega` in (ii), such as LLP of `C*(E)`.
  Then every hyperlinear trace of `E` is amenable. By (A), `delta_e` is then
  not hyperlinear, so `E` is not hyperlinear, and `non-hyperlinear-group`
  follows.
- Independently: `E` is Kazhdan by `elementary-groups-over-fg-rings-have-property-t`
  and not RF (take `e_12(Q)` and the level argument of
  `elementary-group-trace-amenable-iff-ring-rf-proof`). So
  `llp-non-rf-kazhdan-group-is-non-hyperlinear` shows directly that LLP of
  `C*(E)` implies `E` is not hyperlinear. So the LLP bridge is at least as
  hard as `non-hyperlinear-group`. It proves strictly more than (H1), since
  (H1) only excludes the operator-norm models.

Property (T) appears here only in the *analysis* of the route: it is used to
show that the bridge overshoots. It is never an input to (H1).
