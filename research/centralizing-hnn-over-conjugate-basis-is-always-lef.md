---
rg: 2
id: centralizing-hnn-over-conjugate-basis-is-always-lef
kind: claim
title: The centralizing HNN extensions over conjugates of one generator are LEF for every index set, so one three-generator family separates LEF from residual finiteness
distinct_from:
  centralizing-hnn-over-conjugate-basis-is-always-sofic: that proves soficity through the sofic-by-amenable theorem; this proves the stronger local embeddability into finite groups by truncating the shift graph to a finite period, which needs no permanence theorem.
  centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed: that is the residual-finiteness criterion; together with this claim the family `H_J` is LEF for all `J` and residually finite exactly for closed `J`.
  lef-recognition-has-a-pi2-upper-bound: that is the complexity bound for LEF; this supplies a uniform family on which LEF is constant while residual finiteness is Pi-zero-three complete, so the two recognition problems are provably at different levels for a reason visible in one family.
---

ESTABLISHED.  For every `J <= Z` the group

```text
H_J = < a, b, s | [s, b^j a b^-j] = 1,  j in J > = A(Gamma_J) x| Z
```

is locally embeddable into finite groups.  Combined with
[[centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed]]:

```text
H_J is LEF for every J;   H_J is residually finite iff cl(J) = J.
```

So on the recursive presentations `H_{J_e}` of
[[residual-finiteness-three-generator-recursive-is-pi3-complete]] the LEF
question has the constant answer "yes" while the residual-finiteness
question is `Pi^0_3`-complete: the one-level gap between the two
recognition problems is realized inside a single three-generator family,
not merely by comparing two unrelated theorems.

**Mechanism.**  A ball of radius `r` in `H_J` only sees vertices `a_i, s_k`
with `|i|, |k| <= 2r` of the shift graph `Gamma_J`, and right-angled Artin
normal forms are local (parabolic subgroups on full subgraphs are
retracts).  Replacing `J` by the finite set `J n [-4r, 4r]` read modulo a
period `M > 8r + 1` produces a shift-invariant finite graph whose window
agrees with that of `Gamma_J`; the corresponding finitely generated
right-angled Artin group by `Z/M` is residually finite, and evaluation of
ball words in it is a local embedding.
