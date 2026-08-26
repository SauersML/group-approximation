---
rg: 2
id: sl3-hnn-finite-window-central-dual-gap
kind: claim
title: A finite canonical window charges every stable-letter-central SL3 matrix-range separator
distinct_from:
  sl3-hnn-central-dual-gap-vanishes: that is the sequential matrix-ultraproduct formulation; this is its exactly equivalent finitary form, with one finite canonical trace window and one tolerance for each separator norm cutoff and target gap.
  sl3-large-prime-hnn-matrix-range-capture: that asks for primal distance of the selected lattice tuple to the ucp matrix range; this is the smaller dual inequality only for bounded separators approximately central under the selected stable letter.
---

Fix `p>=11` and a finite presentation

```text
G_p=<Gamma,t | [t,Lambda]=1>,
Lambda=SL_3(Z), Gamma=SL_3(Z[1/p]),
```

together with word representatives for a fixed symmetric generating set
`S` of `Lambda`.  For a unitary assignment `x` to the presentation
generators, write `ev_x(w)` for word evaluation, `X_s=ev_x(s)`,
`T=ev_x(t)`, and

```text
h_d(B)=sup_(Y in MR_d(Lambda,S))
       Re sum_(s in S) tr_d(B_s^*Y_s).
```

The **finite central-dual gap claim** is:

> For every `M<infinity` and `epsilon>0`, there are a finite set
> `W subset G_p\{1}` and `delta>0` such that, in every dimension `d`, every
> unitary presentation assignment `x` satisfying
>
> ```text
> max_(r in R)||ev_x(r)-I||_2 <= delta,
> max_(w in W)|tr_d(ev_x(w))| <= delta,                         (FDG1)
> ```
>
> and every tuple `B=(B_s)_(s in S)` satisfying
>
> ```text
> sum_s||B_s||_2^2=1,       max_s||B_s||_op<=M,
> sum_s||T B_s T^*-B_s||_2^2<=delta,                            (FDG2)
> ```
>
> obey
>
> ```text
> Re sum_s tr_d(B_s^*X_s)-h_d(B) <= epsilon.                    (FDG3)
> ```

This is OPEN, and is exactly equivalent to
`sl3-hnn-central-dual-gap-vanishes`.  The equivalence is proved in the two
routes `finite-window-central-dual-implies-sequential` and
`sequential-central-dual-implies-finite-window`.

The quantifier over `M` is essential.  The separator theorem supplies a
uniform bound once a positive primal distance is fixed, but no universal
bound covers separators for all possible gaps.  Conversely `(FDG1)` uses
only scalar canonical moments, not a matrix-valued lifting hypothesis.
Thus this is a genuinely finite matrix-range endpoint: proving one family
of dimension-free inequalities `(FDG3)` closes the large-prime HNN route,
while failure at some fixed `(M,epsilon)` diagonalizes to a canonical
outlier microstate sequence.

The existing firewalls remain visible in this form.  Reduced or full LLP
would prove a much stronger universal lifting assertion and is unavailable;
one-letter, two-letter, endpoint-amplification, and fixed-lamp-frame data are
Morita-neutral.  Any proof of `(FDG3)` must therefore use actor covariance on
a finite mixed Britton window.  If the coset action
`Gamma curvearrowright Gamma/Lambda` is sofic, its finite atlases violate
`(FDG3)` for some fixed `M,epsilon`.

## Attempts

- **Universal lifting is unavailable.**  Replacing the selected finite
  window by LP of the lattice generator system would imply LLP of
  `C^*(SL_3(Z))`, contradicted by `sl3-generator-system-has-no-universal-lp`.
  The reduced algebra also has no LLP
  (`sl3-reduced-group-cstar-has-no-llp`).
- **Fixed frames are neutral.**  The one-letter, two-conjugate-letter,
  full-endpoint finite-actor, and fixed-lamp-frame constructions preserve an
  arbitrary pre-existing matrix-range gap exactly.  Consequently enlarging
  `W` by finitely many uncoupled base or lamp moments cannot prove `(FDG3)`.
  A viable window must test mixed Britton words with the same actor carrying
  both the lamp permutation and the lattice coordinates.
- **The exact finite-action atlas is excluded but approximate atlases remain.**
  Profinite co-density and the Kazhdan gap put every exact arithmetic atlas a
  fixed distance away, while a hypothetical sofic coset-action atlas would
  violate `(FDG3)`.  The unresolved finite inequality must therefore charge
  a noncorrectable approximate deck cocycle rather than another congruence
  representation.
