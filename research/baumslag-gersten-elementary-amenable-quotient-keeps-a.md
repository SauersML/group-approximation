---
rg: 2
id: baumslag-gersten-elementary-amenable-quotient-keeps-a
kind: claim
title: The Baumslag--Gersten group has an elementary amenable quotient in which a has infinite order
distinct_from:
  baumslag-gersten-group-is-neither-linear-nor-self-similar: that says every finite quotient of BG kills a; this gives an infinite elementary amenable quotient that keeps a of infinite order, so a is killed by residual finiteness and not by amenability.
  bg-shift-chains-die-in-residually-linear-alphabets: that kills a in every residually periodic, residually linear or residually solvable image; the quotient here is locally-solvable-by-Z, which that theorem allows, and this shows the allowance is realized.
  bs12-extends-to-amenable-square-conjugation-chain: that asks only for a one-sided forward chain faithful on BS(1,2); this is a homomorphism of BG itself, obtained from the shift endomorphism of the same tower, and gives a bi-infinite Magnus-kernel configuration.
  baumslag-gersten-mark-survives-opnorm-corona: that keeps a in an operator-norm corona, which is not amenable; this keeps a in an amenable, indeed elementary amenable, group.
artifacts:
  - research/bs12-amenable-square-chain-induced-tower-proof.md
---

ESTABLISHED (written proof, unreviewed). Proof:
[[baumslag-gersten-elementary-amenable-quotient-keeps-a-proof]], which
applies section 5 of [[bs12-amenable-square-chain-induced-tower-proof]].

**Theorem.** Let `BG = <a,t | (a^t)^(-1) a (a^t) = a^2>`, with
`a^t = t^(-1) a t`. There is a homomorphism `BG -> A` onto a subgroup of an
elementary amenable group `A = H_inf *_theta` such that the image of `a` has
infinite order. Here:
* `H_inf` is a countable locally solvable group;
* `theta` is an injective endomorphism of `H_inf`;
* `A` is the ascending HNN extension, which is locally-solvable-by-`Z`.

**The construction.** Let `Phi(K,c) = (Q[K] (x)_(Q[<c>]) Q_(1/2)) rtimes K`,
with new letter `e = 1 (x) 1`, so that `c^(-1) e c = e^2`. Iterate
`Phi` from `Z`. The inclusions fix the bottom letters, so the direct limit
`H_inf` carries a forward chain `y_0, y_1, ...` with
`y_(j+1)^(-1) y_j y_(j+1) = y_j^2`. `Phi` commutes with the limit, so
`H_inf = Phi(H_inf)`, and the complement inclusion is an endomorphism
`theta` with `theta(y_j) = y_(j+1)`. Send `a -> y_0` and `t -> tau`.

## Consequences

* **Where `a` dies.** In `BG`, `a` dies in every finite quotient, every
  residually linear quotient and every residually solvable quotient. It does
  **not** die in every amenable quotient. So `BG` is not a counterexample to
  "a sofic-by-amenability mechanism sees `a`". It separates residual
  finiteness from residual amenability at the element `a`.
* **Shift dictionary.** Put `x_j = tau^(-j) y_0 tau^j` for `j in Z`. This is
  a bi-infinite configuration of the Baumslag--Gersten Magnus kernel over an
  amenable alphabet, faithful on the piece `BS(1,2)`. So hypothesis (AA) of
  [[amenable-alphabet-magnus-shift-dictionary-sofic]] holds for `BG`: the
  dictionary passes the model singular zero-exponent step with an amenable
  alphabet. The "no" branch recorded in
  [[bs12-extends-to-amenable-square-conjugation-chain]], which would have
  killed the dictionary at every singular extreme of this type, is closed.
* **The mechanism.** The singular forward equation `X^(-1) u X = u^2` is
  never solved. What is solved is the backward equation
  `u^(-1) Y u = Y^2`, and it is solved universally and functorially. Here
  `Y` lies in an abelian normal subgroup, so the equation becomes linear:
  `(u^(-1) - 2).Y = 0`. The rank-one induced module is its universal
  solution. The direct limit then turns repeated prepending into forward
  growth.

## Boundary

* This is not a new soficity result: `BG` is sofic by amenable-edge HNN
  permanence, since its Magnus edges are cyclic (`n = 1`).
* We do not claim `BG` is residually amenable. Only `a`, and hence the
  whole piece `BS(1,2)`, is kept.
* We have not checked whether this quotient is in the literature.
