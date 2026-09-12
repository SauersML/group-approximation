---
rg: 2
id: birman-exact-sequence-does-not-virtually-split
kind: claim
title: For genus at least four the Birman exact sequence of a closed surface admits no section over a finite-index subgroup
distinct_from:
  finite-central-extension-rf-iff-virtually-splits: that decides residual finiteness of a finite central extension by whether it virtually splits; this is the failure of virtual splitting for one specific extension, the point-pushing extension of a closed-surface mapping class group, whose kernel is an infinite surface group.
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

**ESTABLISHED (literature import).** Chen--Salter, *The Birman exact sequence
does not virtually split*, arXiv:1804.11235v1, Theorem A. Read on 2026-09-12
from the PDF, extracted on MSI:

> "Theorem A. For g ≥ 4, the Birman exact sequence does not virtually split.
> Moreover, for any subgroup Γ ≤ I(Σg) of finite index in the Torelli group,
> there is no splitting σ : Γ → I(Σg,∗) of the Birman exact sequence restricted
> to Γ."

The sequence is their (1),

    1 → π1(Σg,∗) → Mod(Σg,∗) → Mod(Σg) → 1 ,

for `Σg` closed of genus `g ≥ 2` and `Σg,∗` the surface with one puncture `∗`.
Their definition, verbatim: a short exact sequence `1 → A → B → C → 1` "is said
to virtually split if there exists some finite-index subgroup C′ ≤ C and a
homomorphism g : C′ → B such that f∘g = id_C′".

So for `g ≥ 4` there is no finite-index `L ≤ Mod(Σg)` with a homomorphism
`s: L → Mod(Σg,∗)` whose composite with forgetting the puncture is the
inclusion of `L`.

**Scope.**
- **Genus 2:** the sequence does virtually split, through the six Weierstrass
  points (same paper, Introduction).
- **Genus 3:** not covered by Theorem A.
- **History:** the paper says Theorem A was announced in a 1990 preprint of
  G. Mess whose argument contains an error.
