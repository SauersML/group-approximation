---
rg: 2
id: affine-plus-defect-rule-is-injective-on-some-group
kind: claim
title: Some affine rule with one moved table entry over a finite field gives an injective automaton over some group
distinct_from:
  pair-distinct-ternary-rules-pre-injective-on-free-memory: that is the established pre-injectivity of such rules over free memory; this asks for injectivity over some group, which would make that group non-surjunctive.
  unbalanced-forward-tables-identify-memory-letters: that is the universal memory-collision statement over table groups; this is one explicit architecture for refuting it, fixing the shape of the encoder rule.
  ternary-three-address-injective-automata-have-balanced-rules: that is the open universal statement for three symbols and three memory elements; this asks for one injective single-defect affine rule over any field, memory size and group.
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

**OPEN.** There are a finite field `F_q`, a group `G` and a finite `M ⊂ G`, with a rule

```text
mu(x) = sum_(m in M) c_m x_m + c + t [ x|_M = p ],        c_m != 0,  t != 0,  p in F_q^M,
```

whose automaton over `G` is injective.

Every such rule is unbalanced: one table entry has moved. So a positive answer gives a strict
automaton (`unbalanced-effective-rule-certifies-strictness`, Proposition 1), and `G` is not
surjunctive.

## Attempts

- **Minimality.** These are the minimal unbalanced deformations of bijective linear rules. At each
  address exactly one context is insensitive, and it identifies `{p_m, p_m + t c_m^-1}`.
- **Excluded cases.**
  - **`q = 2`.** All pairs are `{0,1}`. Rectangle relations are forced, and three addresses are dead
    (`three-address-binary-injective-rules-are-balanced`).
  - **Sofic or amenable memory groups.** Injectivity there forces balance.
- **Ternary rules on three addresses pass the local screens.**
  - For `mu = x_1 + x_a + x_b + [x = (0,1,2)]` over `Z/3` the pairs are distinct.
  - Over free memory every finite perturbation is visible
    (`pair-distinct-ternary-rules-pre-injective-on-free-memory`), and no screen of Section 2 of the
    artifact applies.
  - The failure over `F(a, b)` is global, so the host must stop infinite defect cascades.
- **The linear part must be a unit (w4-bal-census).** For `q >= 3` a single moved entry at `p`
  occurs only at patterns containing the symbol `p_m`. So the rule is an avoidable patch, and
  injectivity makes the linear automaton injective
  (`avoidable-patches-of-affine-rules-inherit-linear-injectivity`). Either `G` already carries a
  linear strict automaton, or `sum_m c_m m` is a unit of `F_q[G]`. For the ternary example this means
  `1 + a + b` is a unit of `F_3[G]`.
- **Correction witnesses.** Write `L` for the linear part and `D(x) = t 1[x|_(gM) = p]` for the
  defect field.
  - If `x` has defects only on a set `B`, and `x + L^-1(D(x))` has none, the two configurations
    share an image. This needs `L` invertible in `F_q[G]`.
  - When `L` is invertible, injectivity is injectivity of `x -> x + L^-1 D(x)`. That is identity
    plus a sparse nonlinear correction.
  - No host is known where every such correction, finite or infinite, creates a new defect.
- **Decoder arithmetic.** On hosts with stably finite prime-field matrix algebras, a left inverse must
  use `x^q = x` (`formal-polynomial-strict-pairs-need-unstable-linearization`). In reduced form the
  indicator term has degree `(q-1)|M|`.
