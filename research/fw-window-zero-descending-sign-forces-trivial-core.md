---
rg: 2
id: fw-window-zero-descending-sign-forces-trivial-core
kind: claim
title: For an FW input, the descending sign of shell window zero forces the endomorphism core to be trivial, so window zero fails for every co-Hopfian FW input
distinct_from:
  fw-inputs-admit-no-twisted-shell-normalization: that rules out window zero for the ascending sign, where the shift conjugates the input into itself by an endomorphism twist, and treats the descending sign only when the inclusion is an equality; this treats the descending sign with a strict inclusion, which that node leaves open, and reduces it to triviality of the iterated image of the endomorphism.
  one-ended-shell-inputs-admit-no-shift-normalizing-enumeration: that is a regular-enumeration statement proved by an end count; this is a genuine-action statement proved from property FW, with no hypothesis on ends.
  eventually-periodic-genuine-shell-actions-give-fp-envelopes: that is the positive mechanism, where a finite-order twist forces a virtually abelian input; this is an obstruction for infinite-order descending twists.
requires:
  - fw-inputs-admit-no-twisted-shell-normalization
  - genuine-action-shell-envelopes-generalize-the-regular-shell
---

**ESTABLISHED** by `fw-window-zero-descending-sign-proof` (lane proof, elementary, not
independently reviewed; no novelty claimed for the ingredients, which are those of
`fw-inputs-admit-no-twisted-shell-normalization`).

## Statement

Notation as in `fw-inputs-admit-no-twisted-shell-normalization`: `P` is a group with
property FW, `rho : P -> Sym(N)` an action, `s : n -> n+1`, and all identities are read in
`NearSym(N)`.

Let `theta : P -> P` be a homomorphism with

    s rho_g s^-1 = rho_(theta(g))   for every g in P.                        (D1)

Write `P_inf = intersection over j >= 0 of theta^j(P)` for the **endomorphism core** of
`theta`.

1. **Core elements are finitary.** Every `h` in `P_inf` has finite `rho`-support.
2. **Window zero, descending sign.** Suppose `P != 1` and every `rho_g` with `g != 1` has
   infinite support. Then (D1) forces `P_inf = 1`. In particular `s rho(P) s^-1 <= rho(P)`
   is possible only if `theta` is injective, not surjective, and has trivial core.
3. **Co-Hopfian inputs.** If in addition `P` is co-Hopfian, that is every injective
   endomorphism of `P` is surjective, then (D1) is impossible: `theta` surjective gives
   `P_inf = P != 1`. Together with item 2 of the cited node, **window zero fails for both
   signs for every co-Hopfian FW input.**

Item 1 contains item 1 of the cited node as the case where `theta` is an automorphism:
then `P_inf = P`, and every element is finitary.

## Why it matters

The cited node closes the ascending sign, `s^-eps rho(P) s^eps <= rho(P)` with `eps = 1`,
for every FW input, and closes the descending sign only when the inclusion is an equality.
Its own scope line records the strict descending inclusion as untreated. This node treats
it, at the cost of leaving one structural escape: an input with a strictly descending chain
of isomorphic copies `P > theta(P) > theta^2(P) > ...` whose intersection is trivial.

- **Closed outright.** Co-Hopfian FW inputs. Irreducible lattices in higher-rank semisimple
  groups are co-Hopfian, so `SL_n(Z)` for `n >= 3` is an instance (cited, not read at
  source: Margulis superrigidity through Prasad's rigidity theorem).
- **Not closed.** An FW input that is not co-Hopfian and has trivial core. No such input is
  known to this lane, and the question is not addressed here.

## Consequence for the genuine-action shell route

`boone-higman-iff-simple-kazhdan-decidable-inputs` reduces
`boone-higman-conjecture` to inputs that are finitely generated, simple, Kazhdan and FA,
with solvable word problem. Property (T) implies FW. So for those inputs the
genuine-action shell route of `boone-higman-via-genuine-action-shell-envelopes` must supply
either

- a window `N >= 1` in the sense of `shell-ascending-gate-is-a-finite-window-inclusion`,
  with a finitely presented window group (`fp-window-group-makes-shell-germ-group-fp`), or
- a descending window-zero action whose endomorphism core is trivial, which by item 3
  requires the input not to be co-Hopfian.

Every positive instance the route has is eventually periodic, hence virtually abelian
(`eventually-periodic-genuine-shell-actions-give-fp-envelopes`), and an infinite virtually
abelian group is amenable, so it is never Kazhdan. So the route's known positive family is
disjoint from the input class the conjecture reduces to. That is a statement about the
route, not an obstruction to the conjecture.
