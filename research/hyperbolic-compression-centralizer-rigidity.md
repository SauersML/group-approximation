---
rg: 2
id: hyperbolic-compression-centralizer-rigidity
kind: claim
title: Conjugation compression cannot move a centralizer inside a hyperbolic group
invalidates:
  - non-rf-hyperbolic-via-compression-transplant
  - non-rf-hyperbolic-via-free-lamp-compression
distinct_from:
  finite-infranormal-subgroup-is-normal: that is the elementary normalizer lemma for a finite compressed subgroup, with no geometry in it; this is the hyperbolic statement that the centralizer of a non-elementary subgroup is one of those finite subgroups for every compressor, and its content is the consequence for the compression architecture
  hyperbolic-nonelementary-centralizer-finite: that is the finiteness input alone; this is the rigidity conclusion and the death of the finite-residual commutator witness in hyperbolic ambient groups
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Let `G` be word-hyperbolic, let `Γ ≤ G` be non-elementary, and suppose

```text
t Γ t^(-1) <= Γ.
```

Then

```text
C_G(Γ) = t C_G(Γ) t^(-1),
```

so every compressor of `Γ` normalizes `C_G(Γ)`.  In particular, for
`c ∈ C_G(Γ)` and `d = t c t^(-1)`,

```text
[d, a] = 1   for all a in Γ,   and hence   [d, a d a^(-1)] = 1.
```

## What this kills

This program's finite-residual witnesses are built on a strict compression
`tΓt^(-1) ⊊ Γ`, a centralizing element `c`, and a commutator in `d = tct^(-1)`
and elements of `Γ` that is nontrivial in the group and trivial in every
finite quotient — the finite quotients equalize the two images and make `d`
centralize `Γ` (`commuting-lamp-quotient-finite-residual`,
`literal-mark-quotient-finite-residual`).

Inside a hyperbolic ambient group with `Γ` non-elementary, the equalization
happens **in `G` itself**.  There is nothing left for a finite quotient to
kill, and the witness word is trivial rather than invisible.  So the entire
architecture — not the particular affine instance, the architecture — cannot
be transplanted into the hyperbolic category.  The same argument kills the
natural repair that replaces commuting lamps by free lamps, which is recorded
separately as `non-rf-hyperbolic-via-free-lamp-compression`.

## What it does not say

It says nothing about this program's actual witnesses, whose ambient groups
are wreath-type and contain `ℤ^2` in abundance, hence are not hyperbolic and
never claimed to be.  Nothing in the non-MF or non-soficity results is touched.

It also does not assert that hyperbolic groups admit strictly compressing
non-elementary subgroups at all.  Whether they do is a separate question; the
point here is that the answer does not matter, because the architecture dies
either way.

The hypothesis that cannot be dropped is non-elementarity.  For elementary
`Γ` the centralizer can be infinite (take `Γ = ⟨g⟩` inside its own elementary
closure) and the equality can fail; but then `Γ` has no property (T) and
carries none of the rigidity the architecture consumes.
