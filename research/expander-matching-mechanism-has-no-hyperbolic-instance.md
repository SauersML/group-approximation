---
rg: 2
id: expander-matching-mechanism-has-no-hyperbolic-instance
kind: claim
title: Inside a hyperbolic group every subgroup commuting with an infinite Kazhdan subgroup is finite, so the expander-matching mechanism has no hyperbolic instance
distinct_from:
  hyperbolic-compression-centralizer-rigidity: that shows a compressor of a non-elementary subgroup normalizes its centralizer, killing the finite-residual commutator witnesses; this is the commuting-factor step of the nonsoficity criterion, where the commuting group must be non-LEF, and it dies because that group is finite
  nonsofic-hyperbolic-group: that is the open target; this closes one way of reaching it, subgroup transfer of the Kazhdan-plus-commuting-factor witnesses, and says nothing about other mechanisms
artifacts:
  - c1168433:official/counterexample.tex
---

**ESTABLISHED** through `expander-matching-no-hyperbolic-instance-proof`.

Let `G` be word-hyperbolic, let `Γ <= G` be an infinite subgroup with property
(T), and let `J <= G` satisfy `[Γ, J] = 1`. Then `J` is finite.

**Consequences.**

1. **The criterion never fires.** The expander-matching criterion in the proof
   overview of `c1168433:official/counterexample.tex` (Proposition 2.3) takes a
   property (T) subgroup `Γ`, a finitely generated `J` with `[Γ, J] = 1` and
   `Γ ∩ J = 1`, and compressors moving both factors into `Γ`. Its conclusion is
   that soficity of the ambient group forces `J` to be LEF, and a
   contradiction comes only from a non-LEF `J`. Inside a hyperbolic group any
   such `J` is finite, hence LEF, so the criterion certifies nothing there.
2. **No subgroup transfer.** No group containing `Γ × J` with `Γ` infinite
   Kazhdan and `J` infinite embeds in a hyperbolic group. In particular
   `EL_D(R) <= L_(F_2)(1,2)^x`, which contains `Γ × J` with `J ≅ V`
   (counterexample.tex, Section 3 overview), embeds in no hyperbolic group, so
   soficity permanence under subgroups cannot carry that witness into the
   hyperbolic class.

**What it does not say.** It does not rule out nonsofic hyperbolic groups, and
it does not address mechanisms that use no infinite commuting factor, such as
the local-testability route `nonsofic-hyperbolic-via-cheeger-threshold`. It
also does not check the other recorded witnesses (coset wreath products, group
doubles) against hyperbolicity; they are certified through infranormal
Kazhdan pairs, where the normality test is already dead in hyperbolic groups
by `nonsofic-hyperbolic-via-kun-thom-centralizer`.

No novelty is claimed: this is an immediate consequence of the finiteness of
centralizers of non-elementary subgroups.
