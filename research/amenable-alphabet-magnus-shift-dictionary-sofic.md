---
rg: 2
id: amenable-alphabet-magnus-shift-dictionary-sofic
kind: claim
title: A one-relator group is sofic when its Magnus kernel has amenable quotients that separate the piece from its Magnus subgroups, with no condition on the extreme exponents
distinct_from:
  nonsingular-magnus-extremes-separable-piece-sofic: that needs nonzero exponent sums at both extremes and a residually finite piece with separable Magnus subgroups, and builds a locally finite alphabet by solving equations; this assumes an amenable alphabet outright and has no exponent hypothesis, so it applies at singular extremes, where every locally finite alphabet is dead.
  relative-soficity-extension-theorem-withdrawn: that is the withdrawn extension theorem behind the dead residually-amenable-quotient route, which asks for a sofic radical and a residually amenable quotient of G; here the amenable groups are quotients of the Magnus kernel, they need to separate only finitely many piece elements from F_-, F_+ and 1, and the fold supplies the rest.
  magnus-staggered-chain-sofic: that asks for soficity of the whole kernel; this needs only amenable quotients of the kernel that are faithful enough on the one piece B_0, and the kernel need not be residually amenable.
  hnn-folds-into-free-coset-wreath: that is the fold, given a quotient and a sofic coset action; this manufactures both from an amenable quotient of the kernel.
artifacts:
  - research/amenable-alphabet-magnus-shift-dictionary-sofic-proof.md
---

ESTABLISHED (written proof, unreviewed). Proof:
[[amenable-alphabet-magnus-shift-dictionary-sofic-proof]].

**Setting.** `G = <a,t | w>`, `t` of exponent sum zero in `w`,
`a_i = t^(-i) a t^i`, and a cyclic permutation of `w` rewritten as
`W_0(a_0,...,a_n)` with `n >= 1` and both `a_0`, `a_n` occurring. The piece is
`B_0 = <a_0,...,a_n | W_0>`, with Magnus subgroups `F_- = <a_0..a_(n-1)>` and
`F_+ = <a_1..a_n>`. The Magnus kernel is

    N = ker(G ->> Z) = < a_j (j in Z) | W_j = W_0(a_j,...,a_(j+n)) (j in Z) >.

**Theorem.** Suppose:

* **(AA)** for all finite `E_- <= B_0 \ F_-`, `E_+ <= B_0 \ F_+` and
  `E_1 <= B_0 \ {1}` there are an **amenable** group `Q` and a homomorphism
  `psi : N -> Q` with `psi(E_-) cap psi(F_-) = {}`,
  `psi(E_+) cap psi(F_+) = {}` and `1 not in psi(E_1)`.

Then `G` is sofic. No hypothesis on the exponent sums `eps_0`, `eps_n` of the
extreme letters is used.

Equivalently, (AA) asks for configurations `x : Z -> Q`,
`W_0(x_j,...,x_(j+n)) = 1` for all `j`, whose coordinate-0 representation
`a_i -> x_i` of `B_0` separates the given finite sets: `psi(a_j) = x_j`.

## What is new, and what it isolates

* **The exponent hypothesis is removed.** In
  [[nonsingular-magnus-extremes-separable-piece-sofic]], the hypothesis (N)
  enters only through Lemma 2, which grows a *locally finite* alphabet by
  solving nonsingular equations. The coset-action step needs only that the
  finite-window images `pi_N(rho(N)) <= Q^(2N+1)` are amenable, and that holds
  for every amenable `Q`. That theorem is the special case in which `Q` is the
  locally finite group produced by Lemma 2.
* **The residual problem at a singular extreme is an extension problem in
  amenable groups.** For Baumslag--Gersten, `W_0 = a_1^(-1) a_0 a_1 a_0^(-2)`,
  (AA) follows from the open calibration
  [[bs12-extends-to-amenable-square-conjugation-chain]]: an amenable group
  containing `BS(1,2) = <x_0,x_1>` and a forward chain
  `x_(j+1)^(-1) x_j x_(j+1) = x_j^2`, `j >= 1`. Put `x_j = 1` for `j < 0`.
* **Which alphabets can work.** By
  [[bg-shift-chains-die-in-residually-linear-alphabets]], an alphabet for BG
  that satisfies (AA) is not residually periodic, not residually linear over
  any field, not residually solvable and not compact. In particular the `U(m)`
  alphabets suggested in Attempt 7 of [[one-relator-groups-sofic]] are dead.
  What remains is genuinely amenable and non-residually-linear, for instance
  locally solvable groups of unbounded derived length, or simple amenable
  groups.
* **Rank one needs nothing.** If `n = 1`, the edge groups are cyclic, and `G`
  is sofic iff `B_0` is, by amenable-edge HNN permanence. So BG itself is sofic
  classically (`B_0 = BS(1,2)`), and the content of (AA) at a singular extreme
  is for `n >= 2`. There BG serves as the model zero-exponent forward equation
  `X^(-1) u X = u^2`: if (AA) fails for BG with every amenable `Q`, then the
  dictionary cannot pass that equation with any amenable alphabet.

## Boundary

* **One direction only.** Soficity of `G` is not claimed to imply (AA).
* (AA) forces `B_0` to be residually amenable relative to `F_-`, `F_+`. So a
  piece that is not residually amenable, such as one containing a nonsofic
  seed, is out of reach, as for every quotient-based method.

## Attempts

1. **(AA) at the model singular extreme (w5-073, 2026-09-18).** *Holds.*
   [[baumslag-gersten-elementary-amenable-quotient-keeps-a]] gives a
   bi-infinite configuration of the `BG` Magnus kernel over an elementary
   amenable alphabet that is faithful on `B_0 = BS(1,2)`. It is built by an
   induced-module prepend tower and its shift endomorphism. So the
   exponent-free dictionary is not vacuous at singular extremes. The open
   work for `n >= 2` is separation of `B_0` from `F_-` and `F_+`.
