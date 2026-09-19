---
rg: 2
id: abelian-finite-expanders-have-recursively-bounded-order
kind: claim
title: A finite abelian group with a symmetric generating set of size at most L and Cheeger constant at least δ has order less than 2(4L^4/δ^2+1)^L, so abelian subgroups never carry short-expander growth
distinct_from:
  brin-thompson-torsion-orders-escape-every-recursive-bound: that gives large short-generated cyclic subgroups of 2V; this shows such subgroups, and all abelian ones, are useless as expander witnesses, whatever the ambient group.
---

**ESTABLISHED** by `abelian-finite-expanders-have-recursively-bounded-order-proof`
(lane proof, elementary, no imports; not independently reviewed; no priority
claimed; the mechanism is the classical one that expansion forces exponential
growth up to half the group).

**Statement.** Let `Γ` be a finite abelian group, `T` a symmetric generating set
with `|T| = k`, and `δ > 0` with `h(Γ,T) >= δ` (Cheeger constant as in
`finiteness-decidable-iff-finite-subgroup-profile-recursive`).
Then

```text
|Γ| < 2 (4k^4/δ^2 + 1)^k.
```

**Consequence (class kill).** Let `G` be any group with finite generating set
`S`, and let `X^δ_ab(L)` be `X^δ_G(L)` with `Γ` restricted to abelian subgroups.
Then `X^δ_ab(L) < 2(4L^4/δ^2+1)^L` for every `L >= 1`, a bound independent of
`G`. So no short-expander witness past a recursive bound is abelian. In
particular:

- The large cyclic subgroups of `2V` from
  `brin-thompson-torsion-orders-escape-every-recursive-bound` are not expander
  witnesses.
- A route from undecidable torsion to E through `X^δ` must build non-abelian
  finite subgroups out of the torsion. The named invariant is the growth of
  `T`-balls in `Γ`. The failing step is the Cheeger inequality applied to the
  balls, which forces growth `(1+δ/k)^r` up to half of `Γ`, while abelian balls
  grow like `(r+1)^k`.

The same proof bounds every finite group whose `T`-balls satisfy
`|B_T(r)| <= p_k(r)` for a fixed recursive family of polynomials `p_k`.
