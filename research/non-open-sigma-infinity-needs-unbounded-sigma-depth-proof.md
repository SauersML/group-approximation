---
rg: 2
id: non-open-sigma-infinity-needs-unbounded-sigma-depth-proof
kind: route
title: "Proof that non-open Sigma^infinity forces characters of unbounded finite depth"
target: non-open-sigma-infinity-needs-unbounded-sigma-depth
requires: []
---

**Input.** For a group `G` of type `F_∞` every `Σ^n(G)` is open in `S(G)`, and
for `G` of type `FP_∞` every `Σ^n(G;Z)` is open (Bieri–Renz, *Valuations on free
resolutions and higher geometric invariants of groups*, Comment. Math. Helv. 63
(1988), for the homological invariants; Renz's 1988 Frankfurt thesis for the
homotopical ones). The argument below uses nothing else, so it applies to both
families; write `Σ^n` for either.

**(1) Lower semicontinuity.** By definition `δ(ψ) > n` iff `ψ ∈ Σ^m` for all
`m ≤ n`, and the invariants decrease (`Σ^{m+1} ⊆ Σ^m`), so `{δ > n} = Σ^n`,
which is open.

**(2) Where openness fails.** `Σ^∞ = {δ = ∞}`. A point `χ ∈ Σ^∞` is an interior
point iff some neighbourhood of `χ` lies in `Σ^∞`, i.e. contains no `ψ` with
`δ(ψ) < ∞`; this is the stated equivalence. Now let `ψ_k → χ` with
`δ(ψ_k) < ∞`. Fix `n`. Since `χ ∈ Σ^n` and `Σ^n` is open, `ψ_k ∈ Σ^n` for all
large `k`, so `δ(ψ_k) > n` for all large `k`. As `n` was arbitrary,
`δ(ψ_k) → ∞`.

**(3) Stabilization.** A decreasing sequence of sets with finitely many distinct
values is eventually constant: `Σ^n = Σ^N` for `n ≥ N`. Then
`Σ^∞ = ∩_n Σ^n = Σ^N`, which is open. Contrapositive: if `Σ^∞` is not open, the
`Σ^n` take infinitely many distinct values. (Directly: by (2) the finite depths
`δ(ψ_k)` are unbounded, and `ψ_k ∈ Σ^{δ(ψ_k)−1} \ Σ^{δ(ψ_k)}` exhibits a strict
drop at each of infinitely many indices.) ∎

**Model test.** For `G = F_2 × ⋯ × F_2` (`r` factors), `Σ^n(G)^c` is the set of
characters nonzero on at most `n` factors (Meier–Meinert–VanWyk), so the
invariants stabilize at `n = r` with `Σ^r(G) = ∅`, and `Σ^∞(G) = ∅` is open, as
(3) predicts. For `G = Z^2`, `δ ≡ ∞` and `Σ^∞ = S(G)` is open.
