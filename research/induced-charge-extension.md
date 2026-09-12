---
rg: 2
id: induced-charge-extension
kind: route
title: Induce the positive core's invariant charge up to the whole group
target: wreath-amenable-near-representation
requires: []
artifacts:
  - notes/TRUE_CHARGE_EXTENSION_NEEDS_COAMENABILITY.md
---

# Induce the positive core's invariant charge

`positive-core-bernoulli-ce` gives an honest sofic action `Γ ↷ X₀`, hence by
Elek–Szabó's set-level criterion a `W₀`-set `Ω₀` carrying an invariant finitely
additive probability charge with `μ(Fix(w)) = 0` for `w ≠ 1`. Extend it to `W`
the generic way: induce, forming `W ×_{W₀} Ω₀`.

This was the concrete first thing to try on the Kahl–Schneider lane, on the
reasoning that extending a finitely additive invariant measure is Hahn–Banach's
home ground whereas extending Connes embeddability across an amalgamated free
product over a nonamenable base is a named open problem — so the charge might
go through where the algebra does not.

Dead. The induced set fibres `W`-equivariantly over `W/W₀`, so an invariant
charge on it pushes forward to a `W`-invariant mean on `W/W₀`; since `W₀` maps
onto `Γ` under `W ↠ G`, there is a further `W`-equivariant surjection
`W/W₀ → W/(A ⋊ Γ) ≅ G/Γ`, giving a `G`-invariant mean on `G/Γ`. Property (T)
with infinite index forbids it (`no-invariant-mean-on-coset-space`).

**The comparison that motivated it was mis-drawn.** Hahn–Banach extends a
charge from a smaller family of sets to a larger one *with the same invariance
group*. It does not extend an invariant charge along a group inclusion, and the
object needing extension here is a charge for a group that does not preserve
the set it lives on. On this comparison the charge side is strictly worse off
than the algebra side: the obstruction here is a theorem, while Gao–Junge
Problem 1 is open.

Recorded so it is not attempted twice. What survives on the lane is only the
non-induced constructions — that is, the *near* freedom, which is the same
freedom every other live route on this branch is asking for.
