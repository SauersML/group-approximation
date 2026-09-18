---
rg: 2
id: magnus-prepend-towers-are-amenable-quotients-of-the-group
kind: claim
title: Relative one-relator prepend towers are functorial but circular, and any prepend-limit-HNN tower witnesses the Magnus dictionary exactly when the one-relator group itself has amenable quotients separating its piece
distinct_from:
  abelian-layer-alphabets-kill-magnus-pieces-of-rank-two: that kills towers with solvable layers of bounded derived length; this treats every prepend functor, including relative one-relator products and their quotients, and shows the tower mechanism itself adds nothing beyond amenable quotients of G.
  amenable-alphabet-magnus-shift-dictionary-sofic: that asks for amenable quotients of the Magnus kernel N (hypothesis (AA)); this shows every prepend-limit-HNN construction produces quotients of G, so it can only ever witness the stronger hypothesis (AA_G).
  baumslag-gersten-elementary-amenable-quotient-keeps-a: that is one successful tower at n = 1; this is the general equivalence and the tautology theorem for the one-relator prepend functor.
  bs12-extends-to-amenable-square-conjugation-chain: that is the n = 1 chain calibration; this is about all ranks n >= 1 and the relative one-relator product.
artifacts:
  - research/magnus-prepend-towers-are-amenable-quotients-of-the-group-proof.md
---

ESTABLISHED (written proof, unreviewed). Proof:
[[magnus-prepend-towers-are-amenable-quotients-of-the-group-proof]].

**Setting.** `G = <a,t | w>`, `t` of exponent sum zero, Magnus rewriting
`W_0(a_0,...,a_n)` involving `a_0` and `a_n`, `n >= 1`, piece
`B_0 = <a_0..a_n | W_0>`, Magnus subgroups `F_- = <a_0..a_(n-1)>`,
`F_+ = <a_1..a_n>`, kernel `N = ker(G ->> Z)`. For a group `K` and a tuple
`c = (c_1,...,c_n)` in `K` put

    P(K,c) = (K * <X>) / << W_0(X, c_1, ..., c_n) >>.

**Theorem.**

1. **Functoriality (holds).** For every injection `f : K -> L` with
   `f(c) = c'`, `P(L,c') = L *_K P(K,c)` canonically. Hence, whenever the
   relative Freiheitssatz `K -> P(K,c)` is injective, `P(f)` is injective,
   and `P` commutes with directed unions. The relative Freiheitssatz holds for
   every locally indicable `K` (Brodskii; Howie), and it can fail for amenable
   `K` with torsion at a singular extreme, e.g. `K = Z/6`,
   `W_0 = X c X^(-1) d` with `c` of order 2 and `d` of order 3.
2. **Circularity (the literal tower returns G).** Start from the free group
   `K_0 = F(z_1..z_n)` and prepend with `P`, identifying the old bottom
   `n` letters with the `c`'s. The stages are the Magnus truncations
   `B_0 *_(F) B_1 *_(F) ... *_(F) B_k`, the direct limit is the forward half
   `N_+ = <a_j (j >= 0) | W_j (j >= 0)>`, the complement inclusion is the
   Magnus shift `theta(a_j) = a_(j+1)`, and the ascending HNN extension
   `N_+ *_theta` **is `G`**. So the relative one-relator prepend step,
   without quotients, reproduces the group being studied and proves nothing.
3. **Universality (the exact reduction).** Call a *shift tower* any group `H`
   with an injective endomorphism `theta` and an element `y` such that
   `W_0(y, theta y, ..., theta^n y) = 1`. Every prepend-limit construction
   of the kind used for Baumslag--Gersten, with any prepend functor, is a
   shift tower, and every shift tower gives a homomorphism
   `G -> H *_theta`, `a -> y`, `t -> tau`, whose target is amenable iff `H`
   is. Conversely every homomorphism `G -> Q` to an amenable group gives an
   amenable shift tower. Hence:

   > amenable shift towers whose coordinate-0 window representations satisfy
   > (AA) exist **iff** **(AA_G)**: for all finite
   > `E_- <= B_0 \ F_-`, `E_+ <= B_0 \ F_+`, `E_1 <= B_0 \ {1}` there is a
   > homomorphism `pi : G -> Q`, `Q` amenable, separating `pi(E_-)` from
   > `pi(F_-)`, `pi(E_+)` from `pi(F_+)`, and `1` from `pi(E_1)`.

   (AA_G) implies (AA) (restrict to `N`), hence soficity of `G` by
   [[amenable-alphabet-magnus-shift-dictionary-sofic]].

## What this kills and what it leaves

* **Killed: prepend functors as a source of new information.** Whatever the
  prepend functor (abelian induced modules, relative one-relator products,
  wreath or permutational layers, amenable quotients of `P`), the output is an
  amenable quotient of `G` itself. The tower is a *method of constructing*
  such quotients, not a weaker target. The relative one-relator product is
  the universal prepend functor: every other prepend step with the new letter
  satisfying `W_0` factors through `P`, and `P` itself returns `G`.
* **The shape of the remaining problem.** At `n >= 2`, the Magnus route via
  amenable towers is exactly **residual amenability of `G` relative to the
  piece**, (AA_G). By [[abelian-layer-alphabets-kill-magnus-pieces-of-rank-two]]
  the witnesses must put `a` in normal layers of unbounded derived length or
  non-solvable ones. By item 1, if those layers are torsion (locally finite),
  the one-relator Freiheitssatz can fail at singular extremes, so the layers
  cannot simply be taken locally finite either.
* **Strictness caveat.** (AA) for `N` may be strictly weaker than (AA_G):
  a quotient of `N` need not be normalized by `t`. Any route to the weaker
  (AA) must therefore produce **non-shift-equivariant** amenable quotients of
  the kernel, i.e. configurations that are not orbits of one automorphism.

## Boundary

* No new soficity class and no counterexample. This is a strict reduction of
  the tower method (both directions proved) and a circularity obstruction for
  the literal relative one-relator prepend.
* The Freiheitssatz facts in item 1 are cited (Brodskii 1984; Howie 1981),
  and the torsion counterexample is checked in the proof.

## Next step

Decide (AA_G) at an explicit rank-two, doubly singular model, e.g.
`W_0 = a_2^(-1) u a_2 u^(-2)` with `u = [a_0,a_1]`, i.e.
`G_2 = <a,t | (a^(t^2))^(-1) [a, a^t] (a^(t^2)) = [a, a^t]^2>` with
`a^s = s^(-1) a s`: does `G_2` have an amenable quotient in which
`b_1 = [a_0, a_1 a_0 a_1^(-1)]` and `u` survive?
A negative answer kills the amenable-tower route at rank two; a positive one
needs a non-solvable amenable layer.
