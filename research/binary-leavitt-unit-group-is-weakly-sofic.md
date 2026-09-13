---
rg: 2
id: binary-leavitt-unit-group-is-weakly-sofic
kind: claim
title: The binary Leavitt unit group is weakly sofic
distinct_from:
  binary-leavitt-unit-group-is-f2-linear-sofic: that is normalized rank approximation over F_2, which implies this claim; this asks only for finite groups with arbitrary bi-invariant lengths, the weakest finite approximation property on record.
  openai-leavitt-unit-nonsofic: that proves the same group is not sofic; this asks whether it is weakly sofic, where every Kun--Thom-type mechanism is blind.
  metric-ultraproducts-of-finite-groups-are-surjunctive: that is the Gottschalk-side statement; together with leavitt-unit-group-nonsurjunctive it would refute this claim.
  residually-finite-doubles-are-weakly-sofic: that decides weak soficity of the Kun--Thom double through Glebsky's extension theorem; this group is simple and finitely presented with property FA, so no extension theorem can reach it.
---

**OPEN.** `R^x`, `R = L_(F_2)(1,2)`, is weakly sofic (Glebsky--Rivera): for some
`alpha > 0`, every finite set and every `eps > 0` admit a
`(Phi, eps, alpha)`-homomorphism into a finite group with a bi-invariant metric.

`R^x` is Khanh's finitely presented simple nonsofic group
(`fp-simple-nonsofic-via-leavitt-unit-group`). An explicit presentation with seven
generators and sixty relators is `leavitt-unit-group-steinberg-weyl-presentation`.

**Payoffs.**
- **Yes.** Thompson's group `V` embeds in `R^x`, so `V` would be weakly sofic. In this
  graph soficity and linear soficity of `V` are open (`thompson-v-is-sofic`,
  `thompson-v-is-f2-linear-sofic`), and no node records weak soficity of `V`. The check
  was bounded to this graph; no literature search was run. `R^x` would also be the first
  simple weakly sofic nonsofic group recorded in this graph.
- **No.** `R^x` would be the first non-weakly-sofic group. That confirms Glebsky--Rivera
  Conjecture 4.5 and, by `fixed-finite-relator-quotient-tests-local-permanence`,
  refutes quotient permanence of weak soficity.

**Reformulation (simple, finitely presented).** Let `a` range over tuples in finite
groups `Q` for the fixed presentation. `R^x` has no nontrivial finite quotient, so in
every `Q` the relator values normally generate `<a>`. The question is uniformity:

```text
R^x weakly sofic  <=>  for every K there are Q and a in Q^X such that some
                        generator a_x is not a product of <= K conjugates of
                        relator values r(a)^(+-1).
```

The direction `=>` is the triangle inequality. For `<=`, use Glebsky's capped
conjugation word length on `Q` and simplicity (Section 0 of
`simple-group-support-and-semisimple-rank-models-collapse-proof`). So a proof that `R^x` is
not weakly sofic is a uniform width bound over all finite groups. No such bound is known
for any group (`howie-pro-p-tuple-fails-the-profinite-certificate-at-a5`).

## Attempts

- **Permanence: dead.**
  - Suppose `R^x <= E` with `1 -> N -> E -> Q -> 1`, where `Q` is residually finite or
    amenable. Then `R^x ∩ N` is normal in `R^x`.
  - If it is trivial, `R^x` embeds in `Q`. That is impossible: `R^x` is not residually
    finite (simple and infinite), and not amenable (property (T), infinite).
  - So `R^x <= N`, and Glebsky's or Brude--Sasyk's theorem only moves the problem into
    the kernel.
  - Property FA puts `R^x` in a vertex group of every graph of groups, and finite
    presentation puts it in one stage of every directed union
    (`sofic-permanence-closure-omits-simple-fa-nonsofic-groups` records the same
    architecture for soficity).
- **Support-type models: dead.** By `simple-group-support-and-semisimple-rank-models-collapse`,
  models whose length is a monotone subadditive function of support in a finite action
  are sofic models. `R^x` is nonsofic.
- **Simple and symmetric targets, any lengths: dead.** By
  `simple-group-relator-width-in-finite-simple-targets`, the generators of `R^x` have uniformly
  bounded relator width in every symmetric, alternating, sporadic and bounded-rank Lie type
  group. So no weak model sequence of `R^x` stays in those classes. The survivors are classical
  groups of unbounded rank and non-simple, non-symmetric finite groups.
- **Rank-type models over any field: exactly linear soficity.** By item 2 of the same
  theorem, in every characteristic, weak models whose length is a monotone subadditive
  function of `rk(rho(h) - 1)` make `R^x` linear sofic over that field. Over `F_q` they
  exist iff `R^x` is `F_q`-linear sofic (`binary-leavitt-unit-group-is-f2-linear-sofic`
  for `q = 2`; `leavitt-el3-rank-models-over-finite-fields-are-trivial` would exclude
  them).
- **Ring-unit models: dead.**
  - *The models.* Let `A_n` be finite rings, `J` a two-sided ideal of `prod A_n`, and
    `B = prod A_n / J`. The image of `prod A_n^x` in `B^x` is a quotient of a product of
    finite groups.
  - *The obstruction.* `R` admits no nonzero unital ring homomorphism into any such `B`.
    Lift `s_i, t_i` to `prod A_n` and measure with the module-length rank
    `rk(x) = length(x A_n^k)`. The `2x2` matrix `T S` is `I_2` up to the four defects
    `t_i s_j - delta_ij`, and `rk(S) <= length(A_n)` for the row `S = (s_0, s_1)`. So some
    defect has rank at least `length(A_n)/4`.
  - *Conclusion.* Factorwise in `A_n / rad(A_n)`, a defect of proportional rank generates
    `1` with at most `16` terms, uniformly in `n`, and units lift modulo the radical. So
    `1 in J`.
  - *Scope.* Proof sketch, not separately landed. It kills models induced by approximate
    ring representations only, since a group model of `R^x` need not respect addition.
- **Defining characteristic, one unipotent layer (partial).**
  - *The layer.* For a tuple `a` in `GL(V)` put `U = ∩_x ker(a_x - 1)` and
    `W = sum_x im(a_x - 1)`. Every word has block form `[[0, A, B], [0, D, C], [0, 0, 0]]`
    in `W∩U`, `W/(W∩U)`, `V/(W+U)`.
  - *The estimate.* Triple commutators of group elements have rank at most
    `4(rk D_g + rk D_h)`. Since `R^x = gamma_3(R^x)`, each generator is a fixed element of
    `gamma_3(F(X))` times a fixed number `M` of relator conjugates. So
    `max_x rk(a_x - 1) <= C max_x rk(D_(a_x)) + M max_r rk(r(a) - 1)`.
  - *Where it stops.* The rank survives on the `D`-layer, but the next layer repeats the
    estimate with constants growing in the depth. Unipotent towers of unbounded depth are
    not controlled.
- **What is left.** Lengths not determined by one action or semisimple representation.
  These are capped conjugation word lengths on finite groups with large normal subgroups
  carrying small lengths, and ranks in characteristic `2` with deep unipotent structure.
  No construction of either kind is known for `R^x` or for `V`.
