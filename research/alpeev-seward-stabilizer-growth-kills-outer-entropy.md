---
rg: 2
id: alpeev-seward-stabilizer-growth-kills-outer-entropy
kind: claim
title: A factor whose stabilizers grow by index k carries at most 1/k of its Rokhlin entropy as outer entropy
distinct_from:
  rokhlin-supremum-dichotomy-with-centralized-self-copies: that is Seward's vanishing theorem for groups containing centralized finite subgroups next to a finite-supremum subgroup; this is the Alpeev–Seward bound for the outer entropy of a factor whose stabilizers are larger than those upstairs, with no finiteness input.
  seward-rokhlin-entropy-subadditivity: that is countable subadditivity of outer Rokhlin entropy (Seward, Part II, Corollary 2.5); this is the stabilizer bound of Part III, Theorem 1.11.
---

**ESTABLISHED (import).** Alpeev–Seward, *Krieger's finite generator theorem for actions of countable
groups III*, arXiv:1705.09707, Theorem 1.11. Let `G ↷ (X, mu)` be an aperiodic p.m.p. action and
`f : (X, mu) -> (Y, nu)` a factor map. Write `h^Rok_(G,mu)(Y)` for the outer Rokhlin entropy of the
sigma-algebra `f^-1(B(Y))` inside `X`.
- (i) If `|Stab_G(f(x)) : Stab_G(x)| >= k` for almost every `x`, then
  `h^Rok_(G,mu)(Y) <= (1/k) h^Rok_G(Y, nu)`.
- (ii) If the index is infinite almost everywhere, then `h^Rok_(G,mu)(Y) = 0`.

**Uses on main.**
- **Free actions.** If `X` is free and an infinite normal subgroup `N` acts trivially on `Y`, part (ii)
  applies. So every factor of a free action on which an infinite normal subgroup acts trivially has zero
  outer entropy. With `seward-rokhlin-entropy-subadditivity`, `h^Rok_G(X) = h^Rok_G(X | f^-1 B(Y))` for
  ergodic `X`.
- **Special case.** `factors-fixed-by-large-finite-subgroups-have-zero-outer-entropy` is the special case
  in which finite subgroups of unbounded order act trivially.

Verbatim text: [[alpeev-seward-stabilizer-growth-citation]].
