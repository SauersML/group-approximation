---
rg: 2
id: non-open-sigma-infinity-needs-unbounded-sigma-depth
kind: claim
title: "Sigma^infinity fails to be open only where characters of unbounded finite Sigma-depth accumulate"
distinct_from:
  some-f-infinity-group-has-non-open-sigma-infinity: that claim asserts a group with non-open Sigma^infinity exists; this is an unconditional lemma describing what any such group must look like, and it is true whether or not such a group exists.
  every-f-infinity-group-has-open-sigma-infinity: that claim asserts openness for all groups of type F_infinity; this lemma proves openness only for groups whose invariants stabilize and says where openness can fail otherwise.
---

Let `G` be a group of type `F_∞` with character sphere `S(G)`. For a character
class `ψ ∈ S(G)` define its **Σ-depth**

`δ(ψ) = min{ n ≥ 1 : ψ ∉ Σ^n(G) }`, with `δ(ψ) = ∞` iff `ψ ∈ Σ^∞(G)`.

Then:

1. `δ` is lower semicontinuous: `{δ > n} = Σ^n(G)` is open for every `n`.
2. `Σ^∞(G)` is not open at a point `χ ∈ Σ^∞(G)` if and only if every
   neighbourhood of `χ` contains characters `ψ` with `δ(ψ) < ∞`; for any such
   sequence `ψ_k → χ` with `δ(ψ_k) < ∞`, the depths satisfy `δ(ψ_k) → ∞`.
3. Consequently, if the decreasing sequence `Σ^1(G) ⊇ Σ^2(G) ⊇ ⋯` takes only
   finitely many distinct values (equivalently, `Σ^n(G) = Σ^N(G)` for all
   `n ≥ N`), then `Σ^∞(G) = Σ^N(G)` is open. A group of type `F_∞` with
   non-open `Σ^∞(G)` has infinitely many distinct invariants `Σ^n(G)`.

The same statements hold verbatim for the homological invariants `Σ^n(G;Z)` of
a group of type `FP_∞`.

The proof is in `non-open-sigma-infinity-needs-unbounded-sigma-depth-proof`.
The only input is that each `Σ^n(G)` (and each `Σ^n(G;Z)`) is open in `S(G)`,
a theorem of Bieri and Renz for the homological invariants and of Renz for the
homotopical ones, which Zaremsky's Problem 1.13 itself takes as its starting
point.
