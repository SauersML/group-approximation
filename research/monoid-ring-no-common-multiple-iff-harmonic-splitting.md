---
rg: 2
id: monoid-ring-no-common-multiple-iff-harmonic-splitting
kind: claim
title: Two elements of a monoid ring have no nonzero common right multiple exactly when every configuration on the monoid splits into an a-harmonic and a b-harmonic configuration
distinct_from:
  thompson-f-amenable-iff-group-ring-is-ore: that turns amenability of F into the Ore condition for all pairs; this is a dual reformulation, valid for any monoid and field, of what it means for one pair to fail the Ore condition.
  thompson-f-p22-over-f2-exhaustive-degree-seven-census: that settles pairs positively by finite linear algebra; this names the infinite object a negative answer must produce.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that is a counting criterion on monomial sets; this is a linear criterion on configurations for a single pair.
artifacts:
  - research/artifacts/hl-f-p22-invariant-2026-09-13.md
---

**ESTABLISHED** through `monoid-ring-no-common-multiple-iff-harmonic-splitting-proof` (elementary linear
algebra; not independently reviewed; no priority claimed).

Let `M` be a monoid, `K` a field, and `a = Σ_s α_s s`, `b = Σ_s β_s s` in `K[M]`. A *configuration* is a
function `f : M -> K`. Put `(a* f)(m) = Σ_s α_s f(s m)`, and call `f` *a-harmonic* if `a* f = 0`.

1. `a K[M] ∩ b K[M] = 0` if and only if every configuration `f : M -> K` is a sum `f = g + h` with `g`
   a-harmonic and `h` b-harmonic.
2. Equivalently, `a* (ker b*) = a* (K^M)`: every value of `a*` is already a value of `a*` on b-harmonic
   configurations.
3. Over `K = F_2` with `a = Σ_{s ∈ A} s` and `b = Σ_{s ∈ B} s` for finite `A, B ⊆ M`: the pair has no
   nonzero common right multiple iff every `f : M -> F_2` is the XOR of an `A`-even and a `B`-even
   configuration. A configuration is `A`-even if `|{s ∈ A : f(s m) = 1}|` is even for every `m ∈ M`.

**For Thompson's F.** With `M` the positive monoid and `a, b ∈ K[S_(3,5)]`, item 1 is exactly what a
negative answer to Guba's Problem `P_(2,2)` must produce: a splitting of every configuration. By Guba's
alternative (pinned in `research/artifacts/thompson-f-ore-over-f2-2026-09-13.md` §1), one such pair over any
field proves `thompson-f-is-not-amenable`. Unlike a common multiple, a splitting is an infinite object:
it can't be certified by any finite restriction, which matches the records of that artifact.
