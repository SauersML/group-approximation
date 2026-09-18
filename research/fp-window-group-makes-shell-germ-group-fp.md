---
rg: 2
id: fp-window-group-makes-shell-germ-group-fp
kind: claim
title: A finitely presented window group makes the shell near shift group an ascending HNN extension, so the shell germ group is finitely presented
distinct_from:
  shell-ascending-gate-is-a-finite-window-inclusion: that reformulates the ascending clause of the germ gate as one finite window inclusion, and says nothing about finite presentation of the window group or of R_nu; this shows that the window inclusion identifies R_nu as the mapping torus of the window group, so finite presentation of that one finitely generated group implies both clauses of the gate.
  shell-germ-fp-is-an-ascending-hnn-gate: that is the two-clause criterion, finite presentation of R_nu together with the ascending exhaustion; this collapses the two clauses into the single clause that the window group is finitely presented.
  square-spiral-z2-near-shift-group-is-not-finitely-presented: that proves R_nu is not finitely presented for one enumeration of Z^2; this is a general implication, and its contrapositive turns that node into the statement that the width-two window group of the spiral is not finitely presented.
  virtually-cyclic-inputs-have-fp-shell-stabilizers: that proves the shell stabilizer clauses for virtually cyclic inputs by a central-subgroup argument; this gives a criterion for arbitrary inputs, and recovers the two-ended case as a calibration.
artifacts: []
---

**ESTABLISHED** by `fp-window-group-shell-germ-proof` (lane proof, elementary, not
independently reviewed; no novelty claimed; textbook inputs named there).

## Notation

As in `shell-ascending-gate-is-a-finite-window-inclusion`: `P` is an infinite group with
finite generating set `S`, `nu: P -> N` a bijection, `lambda_g(nu(h)) = nu(gh)` the
transported regular permutations, `s: n -> n+1`, and

    R = R_nu = <lambda(P), s>,    eta: R -> Z the near index,
    c_k = s^k lambda(P) s^-k,     W_N^eps = <c_(eps*j) : 0 <= j <= N>.

`F_nu = R_nu x_Z R_nu` and `Q = <rho(P), tau>` are the fiber product and the shell germ
group of `shell-germ-group-has-index-two-fiber-product`.

## Statement

Assume the finite window condition, item (2) of
`shell-ascending-gate-is-a-finite-window-inclusion`, for some `eps` in `{1,-1}` and some
`N >= 0`. Write `W = W_N^eps` and `t = s^eps`.

1. **Mapping torus.** `psi(w) = t^-1 w t` is an injective endomorphism of `W`, and
   `R_nu` is isomorphic to the ascending HNN extension

       W *_psi = < W, t | t^-1 w t = psi(w), w in W >,

   by the map that is the identity on `W` and on `t`. Equivalently
   `ker(eta) = union_(n >= 0) t^n W t^-n` is the direct limit of
   `W --psi--> W --psi--> ...`, and `R_nu = ker(eta) x| <t>`.
2. **One-clause gate.** `W` is finitely generated. If `W` is finitely presented, then
   `R_nu` is finitely presented, and hence so are `F_nu` and the shell germ group `Q`.
   So the two clauses of `shell-germ-fp-is-an-ascending-hnn-gate` collapse to the single
   requirement that one finitely generated group, the window group `W`, be finitely
   presented.
3. **Contrapositive.** If the window holds for `eps, N` and `R_nu` is not finitely
   presented, then `W_N^eps` is not finitely presented.

## Calibration: the two-ended input

Let `P = Z` with the zigzag enumeration `nu(0) = 0`, `nu(k) = 2k-1`, `nu(-k) = 2k` of
`one-ended-shell-inputs-admit-no-shift-normalizing-enumeration`. There
`s lambda_1 s^-1 = lambda_(-1)` near infinity, so the window holds with `eps = -1`,
`N = 0` and `W = W_0 = lambda(Z)` is infinite cyclic. Then `psi` is inversion, item 1
gives `R_nu = Z x|_(-1) Z`, the Klein bottle group, and item 2 gives `Q` finitely
presented. So the criterion is not vacuous, and it reproves the two-ended case of
`virtually-cyclic-inputs-have-fp-shell-stabilizers` at the level of the germ group.

## Corollary: the width-two window group of the square spiral

For the square spiral enumeration of `Z^2` the window holds with `eps = 1`, `N = 2`
(`square-spiral-z2-enumeration-passes-the-finite-window-gate`) and `R_nu` is not finitely
presented (`square-spiral-z2-near-shift-group-is-not-finitely-presented`). By item 3,

    W_2 = < lambda(Z^2), s lambda(Z^2) s^-1, s^2 lambda(Z^2) s^-2 >

is a finitely generated metabelian group that is **not** finitely presented. It is
metabelian because it is a subgroup of the metabelian group `R_nu`.

## What a first positive example now has to be

`one-ended-shell-inputs-admit-no-shift-normalizing-enumeration` and
`accessible-shell-inputs-admit-no-shift-normalizing-enumeration` force `N >= 1` for the
inputs they cover, so `W` properly contains `lambda(P)`. By item 2 the target is exactly:

- an input `P` that is not virtually cyclic,
- an enumeration whose window inclusion holds for some `eps` and `N`,
- with the window group `W_N^eps` finitely presented.

Two remarks, neither of them a claim about any particular enumeration.

- If the `N+1` conjugates `c_(eps*j)` pairwise commute near infinity and generate their
  direct product, then `W = P^(N+1)`, which is finitely presented as soon as `P` is. So
  a positive example does not need a new finite presentation theorem, only an enumeration
  whose junction corrections are mild.
- The spiral fails for a specific reason recorded in
  `square-spiral-z2-near-shift-group-is-not-finitely-presented`: its junction group is an
  infinite rank abelian group of diagonal line shifts, whose Laurent relation module is
  not tame. A positive window group must avoid that shape.

## Scope

- Item 2 is sufficient, not necessary. An ascending HNN extension can be finitely
  presented over a finitely generated base that is not finitely presented, so finite
  presentation of `R_nu` does not imply that of `W`.
- Nothing here is asserted about finite presentation of the shell envelope `E_nu` itself,
  for which the germ gate is not known to be necessary.
- `P` is not assumed finitely presented, only finitely generated.

DERIVATION
fp-window-group-shell-germ-proof
