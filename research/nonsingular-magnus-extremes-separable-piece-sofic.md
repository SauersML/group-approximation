---
rg: 2
id: nonsingular-magnus-extremes-separable-piece-sofic
kind: claim
title: A one-relator group whose Magnus extremes have nonzero exponent sum and whose piece separates its Magnus subgroups is sofic
distinct_from:
  hnn-folds-into-free-coset-wreath: that is the embedding of an HNN extension into a free coset wreath product, given a quotient and a sofic coset action; this manufactures the quotient, a locally-finite-by-Z shift group, from finite quotients of the piece alone.
  rigid-magnus-groups-have-sofic-separating-quotients: that asks for separating quotients of the whole rigid class with stabilizer rho(F_-); this proves separating quotients exist, with an enlarged stabilizer, whenever both extremes are nonsingular and the piece separates F_- and F_+.
  peelable-extreme-one-relator-groups-are-sofic: that needs an extreme letter with one syllable or two syllables of equal absolute exponent; this allows any number of syllables and needs only a nonzero exponent sum at both extremes, together with separability in the piece.
  no-magnus-envelope-one-relator-groups-sofic: that is the rigid remainder with no amenable-edge envelope; this is a positive theorem using no envelope, whose hypothesis is residual finiteness of the piece relative to F_-, F_+.
  relative-amenable-hierarchy-magnus-one-relator-sofic: that uses tree actions of the piece with amenable edge stabilizers; this uses no tree actions and allows nonamenable free edges.
artifacts:
  - experiments/one-relator-alphabet-fold-2026-09-17/bs23_fixed_alphabet.py
  - experiments/one-relator-alphabet-fold-2026-09-17/bs23_fixed_alphabet.out
---

ESTABLISHED (written proof, unreviewed). Proof:
[[nonsingular-magnus-extremes-separable-piece-sofic-proof]].

**Setting.** Let `G = <a,t | w>`, where `t` has exponent sum zero in `w`.
Put `a_i = t^(-i) a t^i`, and let a cyclic permutation of `w` rewrite as
`W_0(a_0,...,a_n)` with `n >= 1`, where both `a_0` and `a_n` occur. The
Magnus piece is `B_0 = <a_0,...,a_n | W_0>`, with Magnus subgroups
`F_- = <a_0,...,a_(n-1)>` and `F_+ = <a_1,...,a_n>`, and

    G = < B_0, t | t^(-1) a_i t = a_(i+1)  (0 <= i < n) >.

**Theorem.** Let `eps_0` and `eps_n` be the exponent sums of `a_0` and `a_n`
in `W_0`. Suppose:

* **(N)** `eps_0 != 0` and `eps_n != 0`;
* **(S)** `B_0` is residually finite, and `F_-` and `F_+` are closed in the
  profinite topology of `B_0`.

Then `G` is sofic.

**Corollary (free pieces).** If `W_0` is primitive in `F(a_0,...,a_n)` (for
instance, if some interior letter `a_i`, `0 < i < n`, occurs exactly once) and
(N) holds, then `G` is sofic. Here `B_0` is free and (S) is M. Hall's theorem.
Example: `BS(1,2) = <a,t | t^(-1)at = a^2>` has `W_0 = a_1 a_0^(-2)`.

## Method (shift dictionary with a growing alphabet)

1. A configuration `x : Z -> P_inf` whose every window
   `(x_j,...,x_(j+n))` satisfies `W_0` gives `rho : G -> P_inf^Z rtimes Z`,
   with `a -> x` and `t -> shift`. Coordinate `0` of `rho` restricted to `B_0`
   is the representation `a_i -> x_i`.
2. Start with a finite quotient `r_0 : B_0 -> P` that separates the finitely
   many syllables needed. Extend the configuration one letter at a time, alternating
   forward (unknown `a_n`, exponent `eps_n`) and backward (unknown `a_0`,
   exponent `eps_0`). Each step is a nonsingular equation over a finite group,
   so it has a solution in a finite overgroup
   ([[kervaire-laudenbach-holds-for-hyperlinear]], the Gerstenhaber--Rothaus
   case). The alphabet `P_inf` is an increasing union of finite groups.
3. `H = rho(G) <= L rtimes Z`, where `L` is residually locally finite. So `H`
   is sofic. The coset action of `H` on `H/D` is sofic, where
   `D = intersect_N rho(F_-) ker(pi_[-N,N])`, by (C2) of
   [[separating-sofic-quotient-sets-make-an-action-sofic]], orbitwise
   soficity, and [[sofic-actions-restrict-to-co-amenable-subgroups]].
4. The fold of [[hnn-folds-into-free-coset-wreath]] works with any stabilizer
   `D >= rho(F_-)`. Membership in `D` or `sigma^(-1) D sigma` is detected at
   coordinate `0`, so separation in `P` suffices.

## Calibration and boundary

* **BS(2,3).** `W_0 = a_1^2 a_0^(-3)`, `B_0` is the trefoil group (LERF, by
  Scott), `eps = -3, 2`. The theorem gives soficity. With a *fixed* finite
  alphabet the window relation `x_(j+1)^2 = x_j^3` forces every `x_j` to have
  order prime to `6`, hence `x_j` and `x_(j+1)` commute, and `[a, t^(-1)at]`
  dies. This is the classical non-residual-finiteness, so the growth of the
  alphabet is essential and the targets are not residually finite.
* **Where the dictionary breaks.** If `eps_n = 0`, the forward step is an
  equation with zero exponent sum, which can be unsolvable in every overgroup.
  For Baumslag--Gersten, `W_0 = a_1^(-1) a_0 a_1 a_0^(-2)`, the forward step
  `X^(-1) x_j X = x_j^2` has no solution in any group once `x_j` has even order.
  Odd orders do not help. If all `x_j` are torsion, a descending-prime
  argument (`p | ord(x_j)` forces a prime `< p` dividing `ord(x_(j+1))`) gives
  `x = 1`. So **every** torsion-alphabet shift representation of BG kills
  `a`; the proof is in section 9 of the proof file.
* **Strict reduction, one direction only.** For the rigid remainder
  [[no-magnus-envelope-one-relator-groups-sofic]] with both extremes
  nonsingular, soficity follows from (S) for the piece, which is a statement
  about a one-relator group with a shorter relator. The converse is not
  claimed. Unpeelable extremes with two syllables of unequal absolute exponent
  are automatically nonsingular.
