---
rg: 2
id: rank-two-bs-model-roots-need-infinite-order-witnesses
kind: claim
title: At a Baumslag--Solitar singular extreme the root of the conjugated element is never separated from F_- by finite, periodic, polycyclic or metabelian quotients, yet solvable wreath quotients separate it, so solvable (AA) and (AA_G) coincide; the rank-two test model G_2 is itself residually finite
distinct_from:
  magnus-prepend-towers-are-amenable-quotients-of-the-group: that reduces amenable towers to (AA_G) and names G_2 as the open test; this computes G_2 (it is an ascending HNN extension of F_3, hence residually finite and already sofic), kills every finite, periodic, virtually polycyclic and metabelian witness at an explicit element, and shows by Kaloujnine--Krasner induction that the shift-equivariance gap between (AA) and (AA_G) is empty for solvable and finitely supported witnesses.
  abelian-layer-alphabets-kill-magnus-pieces-of-rank-two: that kills uniform families of bounded-solvable layers at b_d; this gives a per-element solvable witness keeping u and b_1 and separating the root, and a different obstruction (at the root v, not at b_d) that no finite or metabelian witness can pass.
  bg-shift-chains-die-in-residually-linear-alphabets: that kills a whole infinite BG chain in residually linear or periodic alphabets at n = 1; this is a one-step separation obstruction inside the piece, valid at every rank, and it is passed by a linear solvable alphabet.
  peelable-extreme-one-relator-groups-are-sofic: that proves G_2 sofic by peeling; this uses G_2 only as a calibration of the amenable-quotient route and records that the route is strictly harder than peeling on it.
  amenable-alphabet-magnus-shift-dictionary-sofic: that is the dictionary with hypothesis (AA); this is about which witness classes can satisfy (AA) at a BS-type extreme.
artifacts:
  - research/rank-two-bs-model-roots-need-infinite-order-witnesses-proof.md
  - experiments/one-relator-rank-two-model-2026-09-17/rewrite.py
  - experiments/one-relator-rank-two-model-2026-09-17/rewrite.out
  - experiments/one-relator-rank-two-model-2026-09-17/lis.g
  - experiments/one-relator-rank-two-model-2026-09-17/lis.out
  - experiments/one-relator-rank-two-model-2026-09-17/search_window.py
  - experiments/one-relator-rank-two-model-2026-09-17/search_window.out
  - experiments/one-relator-rank-two-model-2026-09-17/verify_wreath.py
  - experiments/one-relator-rank-two-model-2026-09-17/verify_wreath.out
---

ESTABLISHED (written proof, unreviewed; the certificate and the finite-quotient
census in E are machine-checked).
Proof: [[rank-two-bs-model-roots-need-infinite-order-witnesses-proof]].

**Setting.** `G = <a,t | w>`, `t` of exponent sum zero, Magnus letters
`a_k = t^(-k) a t^k`, piece `B_0 = <a_0..a_n | W_0>`, `F_- = <a_0..a_(n-1)>`,
`F_+ = <a_1..a_n>`, kernel `N`. Conventions `x^s = s^(-1) x s`,
`[x,y] = x^(-1) y^(-1) x y`. The model of
[[magnus-prepend-towers-are-amenable-quotients-of-the-group]] is

    G_2 = <a,t | a_2^(-1) u a_2 = u^2>,   u = [a_0,a_1],   n = 2.

Its piece `B_0` is an HNN extension of `F_- = F(a_0,a_1)` with stable letter
`a_2`. Put `v = a_2 u a_2^(-1)`. Then `v^2 = u`, and `v` is not in `F_-`
(Britton). Put `b_1 = [a_0, a_1 a_0 a_1^(-1)]`.

**Theorem.**

* **A. The model is not a test of Pestov 4.10.** In the other coordinate
  (`a` as stable letter, `s_e = a^e t a^(-e)`) the relator's rewriting over
  `y_0..y_3` contains its bottom letter `y_0` exactly once. So `G_2` is an
  ascending HNN extension of `F_3`. Hence `G_2` is residually finite
  (Borisov--Sapir) and sofic. It also lies in
  [[peelable-extreme-one-relator-groups-are-sofic]] in both coordinates: the
  top `t`-letter `a_2` forms two syllables of exponent `-1` and `+1`.
* **B. Root lemma (all ranks).** Suppose `B_0` contains `c` in `F_-` and `g`
  with `g^(-1) c g = c^k`, `|k| >= 2`, and `r = g c g^(-1)` not in `F_-`. If
  `rho` is any homomorphism from `B_0` and `rho(c)` has finite order, then
  `rho(r)` lies in `<rho(c)>`, inside `rho(F_-)`. So no quotient in which
  `c` is torsion separates `r` from `F_-`. The excluded quotients include
  all finite, periodic and locally finite ones. They also include every
  finitely generated quotient in which `rho(F_-)` is profinitely closed,
  such as every virtually polycyclic one (Mal'cev). In particular `F_-` is
  not closed in the profinite topology of the residually finite group
  `G_2`.
* **C. Metabelian quotients of `G_2` fail.** `a_0^(-1) a_2 = [a,t^2]` and `u`
  both lie in `G'`. So in every metabelian quotient `pi(v)` equals
  `pi(a_0 u a_0^(-1))`, which lies in `pi(F_-)`. Every (AA_G) witness at
  `E_- = {v}` therefore has derived length at least 3, contains
  `<pi(u), pi(a_2)>` isomorphic to `BS(1,2)`, and has `pi(F_-)` not
  profinitely closed.
* **D. Induction: shift-equivariance is free.** Every homomorphism
  `rho : N -> L` extends to `pi : G -> L^Z ⋊ Z` (unrestricted), with
  `pi(t)` the shift. Coordinate 0 of `pi` restricted to `B_0` is `rho`. If
  `rho(a_k) = 1` for all but finitely many `k`, then `pi` lands in the
  restricted wreath product `L wr Z`. Consequences:
  - (AA) witnessed by solvable alphabets holds iff (AA_G) witnessed by
    solvable quotients holds. The derived length goes up by at most 1.
  - (AA) witnessed by finitely supported configurations in amenable groups
    implies (AA_G).
  - The strictness caveat of
    [[magnus-prepend-towers-are-amenable-quotients-of-the-group]] therefore
    lives only in configurations that are not finitely supported and whose
    alphabets lie in no amenable class closed under countable unrestricted
    powers (solvable groups of bounded length are such a class).
* **E. Certificate (the step asked for).** The following window
  configuration gives an explicit homomorphism
  `pi : G_2 -> L wr Z`, where `L <= GL_3(Z[1/2])` is upper triangular, hence
  solvable. Under `pi`, `u` and `b_1` survive and `pi(v)` is not in
  `pi(F_-)`:

      a_0 -> [[1,-1,-1],[0,1,-1],[0,0,1]],
      a_1 -> [[1,0,0],[0,-1,1],[0,0,-1]],
      a_2 -> diag(1,2,2),
      a_k -> 1  for all other k.

  The coordinate-0 image of `F_-` lies in `GL_3(Z)`, while
  `pi(v)_0 = [[1,1,1/2],[0,1,0],[0,0,1]]`. The search script finds 576 such
  configurations with small entries.

  Finite images of `G_2` from all 253 subgroups of index at most 8 were
  also checked. In 53 of them `u` survives, and `b_1` survives in all 53
  (e.g. `S_3`, `A_7`, `S_8`, `PSL(3,2)`). None separates `v` from `F_-`, as
  B predicts.

## What this decides

* **The question as posed is positive, and cheaply.** `G_2` has finite
  (even `S_3`) quotients keeping `u` and `b_1`, and solvable quotients that
  also separate the root `v`. The prediction that a positive answer "needs a
  non-solvable amenable layer" is false per finite set. Bounded solvability
  kills only uniform families; see D.
* **The real content is the root obstruction.** At a BS-type singular
  extreme `a_n^(-1) c a_n = c^k`, every (AA) witness must keep `c` of
  infinite order and use a non-LERF, non-periodic alphabet. At `G_2`, every
  (AA_G) witness must in addition have derived length at least 3. So the
  amenable-quotient route cannot reproduce soficity of this residually
  finite group through finite quotients. It is strictly harder than peeling
  here.
* **Not decided.** Full (AA_G) for `G_2`, i.e. every finite `E` at once. By
  D it is equivalent, for solvable witnesses, to `N` being residually
  solvable relative to `F_-` and `F_+` on `B_0`. It fails for solvable
  witnesses if `B_0` meets the solvable residual `G_2^(omega)`.

## Next step

The model `G_2` is closed, so move to a genuinely open model: an unpeelable
relator from [[no-magnus-envelope-one-relator-groups-sofic]]. For it, test
two things:

* whether its piece meets the solvable residual `G^(omega)`, which would kill
  solvable witnesses outright by D;
* whether its singular extreme contains a BS-type root, which would kill
  finite and periodic witnesses by B.
