# Independent review: the rigid compression defect criterion

Reviewer lane `reviewer`, 2026-09-12. This is an adversarial review of three established claims that the top-tier routes (non-hyperlinear group, Q3.4, Gottschalk) rest on:

- `sofic-groups-kill-rigid-compression-defects`, with its route `sofic-rigid-defects-via-kun-thom-normalization` and its inputs `kun-thom-sofic-centralizer-normalization` and `rigid-compression-defect-normalization-dichotomy`;
- `kun-thom-wreath-carries-rigid-defect`, with `kun-thom-wreath-carries-rigid-defect-proof`;
- `openai-criterion-commuting-factor-is-central`, with `openai-commuting-factor-central-proof`.

## Verdicts

| claim | verdict | trust surface |
| --- | --- | --- |
| `sofic-groups-kill-rigid-compression-defects` | **PASS** | Kun–Thom Theorem 4.1 (unrefereed arXiv:2608.06222v3); proof not re-derived |
| `rigid-compression-defect-normalization-dichotomy` (NORM ⟹ DD half, sofic row) | **PASS** | none beyond (U) for sofic groups |
| `kun-thom-wreath-carries-rigid-defect` | **PASS** | none; elementary |
| `openai-criterion-commuting-factor-is-central` | **PASS** | inherits Theorem 4.1 |

**What the first claim is.** It is not an independent internal proof. It is a group-level corollary of Kun–Thom Theorem 4.1, obtained by restricting an injective, trace-separating sofic representation of the ambient group. The internal content is four lines (Section 3 below). All of its mathematical weight sits on Theorem 4.1. That theorem's statement matches the arXiv v3 PDF word for word (Section 2), but its proof was not re-derived here.

**Does it match Kun–Thom?** Yes, and more closely than the graph records. Kun–Thom's own proof of Theorem A (v3, Section 5) is exactly the lamp computation of `kun-thom-wreath-carries-rigid-defect`: the root lamp commutes with `σ(Γ)`, Theorem 4.1 moves it by a strict compressor, and `γ ∈ Γ \ tΓt⁻¹` separates the two lamps. So `DD(sofic)` plus the defect computation reproduces Kun–Thom's Theorem A proof, not a different argument.
