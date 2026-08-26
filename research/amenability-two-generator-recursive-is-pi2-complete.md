---
rg: 2
id: amenability-two-generator-recursive-is-pi2-complete
kind: claim
title: Amenability is Pi-zero-two complete for two-generator recursive presentations, and containing a free subgroup is Sigma-zero-two complete
artifacts:
  - GroupApproximation/Computability/AmenableEnumeratedHardness.lean
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  second-level-rice-theorem-for-local-approximation-properties: that handles hereditary properties containing the residually finite groups and its positive branch is the residually finite bridge value, which contains free groups; amenability excludes free groups, so this needs a different two-generator family and a different upper bound (Kesten rather than finite models).
  mf-recognition-two-generator-recursive-is-pi2-complete: that classifies an approximation property; this classifies amenability, which is not closed in the space of marked groups and has no finite-model certificate, and reaches the same level through return probabilities.
  shift-raag-family-classifies-amenability: that is the group-theoretic switch; this is the complexity theorem it yields once the Kesten upper bound is added.
---

ESTABLISHED, unconditionally.  For recursive presentations on two
generators (and on any fixed finite number of generators),

```text
AMENABLE_rec2        is Pi^0_2-complete,
NONAMENABLE_rec2     is Sigma^0_2-complete,
METABELIAN_rec2      is Pi^0_2-complete,
CONTAINS-F2_rec2     is Sigma^0_2-complete,                            (AM1)
```

and the same holds for countably generated enumerated presentations.

**Upper bound (Kesten).**  For `G = <X | R>` with `X` finite let
`S = X u X^-1` and `N_{2n}` the number of words of length `2n` over `S`
that are trivial in `G`.  Kesten's theorem says `G` is amenable iff the
spectral radius of the simple random walk is `1`, i.e. iff

```text
for every k there is n with  N_{2n} >= (1 - 1/k)^{2n} |S|^{2n}.      (AM2)
```

The inner statement is certified by that many derivations, so it is
`Sigma^0_1`; hence amenability is `Pi^0_2`.  For countably many
generators, amenability is local, so quantify also over the finite
initial segments of the alphabet.  Containing `F_2` is `Sigma^0_2`: two
words generate freely iff every nontrivial reduced word in them is
nontrivial, a `Pi^0_1` condition.  Metabelian is `Pi^0_2`: every
commutator of commutators of words is trivial.

**Hardness.**  `TOT = {e : W_e = N}` is `Pi^0_2`-complete, and
[[shift-raag-family-classifies-amenability]] gives a computable
`e |-> G_{J_e}`, `J_e = {j + 1 : j in W_e}`, with `G_{J_e}` amenable iff
metabelian iff `e in TOT`, and containing `F_2` iff `e notin TOT`.

**Reading.**  Amenability is not a local approximation property (it is
not closed in the space of marked groups), so the second-level Rice
theorem does not apply to it; nevertheless it sits at exactly the same
level as soficity, hyperlinearity, MF and LEF.  The reason is Kesten's
criterion: a single number, the return probability, plays the role of the
finite model.

**Machine-checked hardness.**  `Computability/AmenableEnumeratedHardness.amenableCode_pi02Hard` and `nonamenableCode_sigma02Hard` are the second-level lower bounds on enumerated presentation codes (amenable groups are sofic, so the nonsofic seed is forbidden); the Kesten upper bound is paper-level.
