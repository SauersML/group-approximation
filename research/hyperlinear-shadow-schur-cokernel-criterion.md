---
rg: 2
id: hyperlinear-shadow-schur-cokernel-criterion
kind: claim
title: A group compiles to a non-hyperlinear central extension of its hyperlinear shadow exactly when the shadow's Schur multiplier is not hit
distinct_from:
  twisted-factor-existence-is-equivalent-to-nonhyperlinearity: that shows any non-CE twist on any group, possibly a non-hyperlinear one with the trivial twist, is equivalent to the root; this concerns twists over a hyperlinear base only and gives an exact homological test on an arbitrary witness for when one can be extracted from it.
  torsion-dense-schur-multiplier-compiles-twisted-nonce: that turns one given non-CE multiplier into a torsion one by density in H^2; this starts from an arbitrary non-hyperlinear group, produces the central extension and its kernel D=coker(H_2 G -> H_2 Q), and localizes to Z/p whenever D is not divisible.
  schur-kernel-lies-in-hyperlinear-radical: that puts the Schur kernel of a nonsingular adjunction inside the radical of central extensions; this is the converse interface, reading the central part of any radical off the shadow map on H_2.
  hyperlinear-residual-restricts-along-amenable-quotients: that compares residuals of a normal subgroup and of the ambient group along an amenable quotient; this computes the relative coinvariants N/[N,G] of the ambient residual over a hyperlinear quotient.
  finite-kernel-nonrf-has-central-prime-reduction: that is the residually-finite, finite-kernel prime reduction; this is the hyperlinear, arbitrary-witness version, where marked closedness replaces finite-index passage and divisibility of the cokernel is the exact obstruction.
---

**Statement.** For a countable group `G` let `Res(G)` be its hyperlinear
residual (as in `mf-nonhyperlinear-collapse-structure`), write
`N = Res(G)`, call `Q = G/N` the *hyperlinear shadow* of `G`, and put

```text
D(G) = coker( H_2(G;Z) --> H_2(Q;Z) ).                        (SC0)
```

1. **(Identification.)** `N <= [G,G]` and `N/[N,G] = D(G)`.
2. **(Central shadow.)** `E(G) = G/[N,G]` is a central extension
   `1 -> D(G) -> E(G) -> Q -> 1` with `Res(E(G)) = D(G)`. So `E(G)` is
   non-hyperlinear iff `D(G) != 0`.
3. **(Exact interface.)** The following are equivalent.
   - (a) Some countable hyperlinear group has a non-hyperlinear central
     extension.
   - (b) Some countable group `G` has `H_2(G) -> H_2(G/Res G)` not surjective.
4. **(Prime localization.)** If `D(G)` is not divisible, then some finitely
   generated hyperlinear group `H` has a non-hyperlinear central extension
   `1 -> Z/p -> E -> H -> 1`. Consequently the following are equivalent.
   - (a') Some finitely generated hyperlinear group has a non-hyperlinear
     central extension by `Z/p`. Equivalently, by a finite group, or by a
     finitely generated abelian group.
   - (b') Some countable group `G` has `D(G)` not divisible.
5. **(Biography of a counterexample to the central compilers.)** Suppose every
   finite central extension of a hyperlinear group is hyperlinear, but the
   root `non-hyperlinear-group` holds. Then every non-hyperlinear group `G`
   has `D(G)` divisible. If moreover every central extension of a hyperlinear
   group is hyperlinear, then every non-hyperlinear `G` has `N = [N,G]`, and
   `H_2(G) -> H_2(Q)` is onto. So the passage `G -> G/[N,G]` returns exactly
   the shadow `Q`.

**Exact failing step (central compression of an arbitrary witness).** On a
witness `G` with `D(G) = 0`, forming `G/[Res G, G]` lands on the hyperlinear
shadow. This happens whenever every class of `H_2` of the shadow lifts to `G`,
for example when `Q = 1`, which covers every simple witness. Taking products
with hyperlinear groups, free products, or HNN/amalgam overgroups in which the
residual stays the normal closure of `Res G` never changes this: the new
coinvariants are a quotient of the old ones. A change can only come from new
residual elements outside that normal closure, that is, from a
non-hyperlinear quotient of the added hyperlinear pieces.

**Open gap.** When `D(G)` is divisible and nonzero, for example `Q` or `Z(p^infinity)`,
item 2 still gives a non-hyperlinear central extension of a hyperlinear group
by `D(G)`. It is not known that a finite central witness can be extracted. The
characters of a divisible group of finite order are trivial, so the fiber
twists `chi o delta` over `D(G)^` are never torsion classes. Item 4 and the
torsion-density node therefore both stop here.

The gap only occurs for shadows with a large Schur multiplier. If
`H_2(Q;Z)` is finitely generated, for example if the shadow `Q` is finitely
presented, then `D(G)` is finitely generated. It is then either `0` or not
divisible, and item 4 applies. Choosing different lifts of the generators does
not help either. Any subgroup `S <= E(G)` mapping onto `Q` satisfies
`S intersect D = delta(H_2 Q) = D`, and `E(G)` is hyperlinear iff `S` is,
because `E(G)` is a central quotient of `S x D`.

**Why this is the right invariant.** The central compilers already in the
graph (Schur kernel, HS stability, Deligne cover, torsion density) each start
from a chosen hyperlinear base and try to make one Schur class die. This
claim works from the other side. For *any* witness it names the exact group
of Schur classes that die (SC0), and it shows that the compilers reach the
witness exactly when that group is nonzero.

**First falsifiable step and calibration.**
- The first falsifiable step is the identification (SC0) via the five-term
  sequence, together with the equality `Res(E(G)) = D(G)`.
- On a hyperlinear `G`: `N = 1` and `D = 0`.
- On a non-hyperlinear central extension `E` of a hyperlinear `H` by `C`, as in
  `hs-stability-forces-nonhyperlinear-central-extension`: `D(E) = Res(E) <= C`.
  When `C` is finite this is non-divisible, and item 4 reproduces the prime
  central reduction.
- The argument uses only that the class is closed under subgroups and
  countable products, plus marked closedness in item 4. The same computation
  on the residually finite residual of Deligne's non-residually-finite
  central extension of `Sp_4(Z)` gives `D = 2Z` inside the centre `Z`, as it
  should.

No novelty is claimed for the homological algebra (Stallings--Stammbach
five-term sequence). The content is the exact interface (3), the prime
localization (4) and the isolation of the divisible gap.
