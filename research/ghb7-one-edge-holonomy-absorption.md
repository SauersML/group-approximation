---
rg: 2
id: ghb7-one-edge-holonomy-absorption
kind: claim
title: Genuine vertex representations of GHB_2(7) agreeing exactly on a and b and almost on c glue flexibly
distinct_from:
  ghb7-flexibly-hs-stable: that is flexible HS stability of GHB_2(7), equivalently edge matching with all three edges almost agreeing; this is the one-edge form, where a and b already agree exactly and only the c-mismatch must be absorbed, which is equivalent to it by the split-abelianization reduction
  triangle-edge-matching-reduces-to-one-edge-holonomy: that is the general reduction of edge matching to one-edge holonomy absorption; this is the open instance for the triangle of GHB_2(7)
---

**OPEN.** Let `G = G_{HB_2}(7)` with vertex groups `X_0 = ⟨a,b⟩` (order 343), `X_1 = ⟨c,b⟩` and
`X_2 = ⟨c,a⟩` (order 2401), and edge groups `⟨a⟩, ⟨b⟩, ⟨c⟩` of order 7
(`cckw-ghb2-kms-group-structure`).

**Claim (HA).** For all `d_n` and genuine representations `ρ_{i,n} : X_i → U(d_n)` with

```text
ρ_{0,n}(b) = ρ_{1,n}(b),   ρ_{0,n}(a) = ρ_{2,n}(a)   exactly,   ||ρ_{1,n}(c) − ρ_{2,n}(c)||_2 → 0,
```

there are genuine representations `π_n : G → U(D_n)`, `D_n ≥ d_n`, `D_n/d_n → 1`, with
`||ρ_{i,n}(x) − P_n π_n(x) P_n*||_2 → 0` for every `i` and every `x ∈ X_i`.

**Equivalent forms.** By `triangle-edge-matching-reduces-to-one-edge-holonomy`, whose hypothesis
(SPLIT) holds by `ghb7-triangle-vertex-groups-split-abelianizations`, (HA) is equivalent to (EM) for
this triangle, hence to `ghb7-flexibly-hs-stable`.

**What (HA) asks, concretely.** After `b` and `a` agree exactly, a useful restricted search is
conjugating `ρ_1` by unitaries in the commutant of `ρ_0(b)`, conjugating `ρ_2` by unitaries in the
commutant of `ρ_0(a)`, and adding `o(d_n)` flexible padding. The actual (HA) statement also allows
perturbing `ρ_0` and changing vertex representation multiplicities; equivalence to the restricted
search with fixed vertex equivalence classes has not been proved. The mismatch on `c` has to be removed with
corrections tending to `0` in normalized HS norm. The vertex group data that constrain this are in
`ghb7-triangle-vertex-groups-split-abelianizations`: `a` and `b` have centralizers of order 49 in
every vertex group containing them, while `c` has centralizers of order 343 in `X_1` and `X_2`.

**Stakes.** Through `ghb7-flexibly-hs-stable`, Cairn cascades (HA) to `non-hyperlinear-group`,
`nonsofic-hyperbolic-group` and `non-residually-finite-hyperbolic-group`.

## Attempts

- **Where non-regular edge data sit (2026-09-13, lane `hl-ghb7-edge-matching`).** By
  `ghb7-vertex-irreducibles-edge-restriction-table`, every irreducible of every vertex group
  restricts to `⟨a⟩` and `⟨b⟩` as a linear character or as the regular representation. The only
  non-regular restrictions of nonlinear irreducibles are on `c`, in 42 degree-7 irreducibles of `X_1`
  and 42 of `X_2`, with multiplicities `(2,2,2,1,0,0,0)`. No gluing consequence is proved: the data
  record where the relative position of `ρ_1(c)` and `ρ_2(c)` can differ from a multiplicity count.
- **Plancherel-moment counts cannot refute (HA) (standard facts not re-read at source: Delorme–Guichardet,
  Lück additivity).**
  - For `k, l >= 0` and a vertex or edge group `X`, put
    `f_X^(k,l)(ρ) = (1/|X|) Σ_(x∈X) (tr ρ(x))^k · conj(tr ρ(x))^l`, with `tr` normalized. This is the
    normalized dimension of the `X`-invariants of `ρ^(⊗k) ⊗ ρ̄^(⊗l)`.
  - For a genuine `G`-representation, the count `1 − Σ_e f_e^(k,l) + Σ_i f_i^(k,l) >= 0` follows from
    property (T) and the cochain complex of `Y` with coefficients in `ρ^(⊗k) ⊗ ρ̄^(⊗l)`, exactly as in
    the fence on `ghb7-flexibly-hs-stable` (the case `k = 1, l = 0`).
  - Every asymptotic representation satisfies the same count in the limit. Replace `L^2(M)` by
    `L^2(N)`, `N = M^(⊗̄k) ⊗̄ (M^op)^(⊗̄l)`, with `G` acting on the left through
    `σ^ω(g)^(⊗k) ⊗ (σ^ω(g)*)^op⊗l`. The cochain complex consists of Hilbert right `N`-modules, (T)
    gives `H^1 = 0`, and additivity gives the count with `f^(k,l)` as `τ_N` of the averaging
    projections.
  - So no count of invariant fractions of any tensor power separates (HA) from its failure. A
    witness must be seen by the relative position of the vertex operators, not by characters.
- **Refutation side.** See `ghb7-finite-index-z-extension-center-survives` and route
  `ghb7-instability-via-visible-central-extension`.
- **Exact gap.** After `b` and `a` agree exactly, remove the `c`-mismatch with corrections tending to
  `0` in normalized HS norm plus `o(d)` flexible padding, uniformly in the dimension. Or exhibit a
  finite-index subgroup whose Kazhdan central `Z`-extension keeps its centre at unbounded orders in
  finite quotients.

ROUTES
ghb7-stability-via-one-edge-holonomy


**2026-09-20 campaign.** The preprocessing estimates are now quadratic in padding
and linear in error (`hrf-cyclic-edge-quadratic-padding`). Liu's fixed-tolerance
block theorem gives the equivalent open scalar-expander rounding frontier
`hrf-ghb7-scalar-expander-rounding`, with doubled generators. Neither the
preprocessing nor that localization proves (HA). Expanding projective examples
for other Kazhdan groups rule out deriving rounding from expansion alone
(`hrf-audit-projective-internality-does-not-round`).


The same campaign proves same-dimension rounding for exact scalar relators,
and more generally exactly central relator matrices, via
`hrf-ghb7-scalar-relator-models-round-strictly` and
`hrf-ghb7-central-relator-models-round-strictly`. Neither hypothesis is
known for general (HA) data; approximate centrality does not satisfy the
proved exact-central hypothesis.


**Wave 2 (2026-09-20).** The phase-normalized defect bound in
`wave2-ghb7-phase-normalized-defect-is-controlled-by-centrality` and the
camouflage theorem `wave2-ghb7-raw-supercentrality-does-not-reduce-stability`
show why a small centrality-to-raw-defect ratio does not prove this claim:
scalar phases can manufacture that ratio while leaving rounding difficulty
unchanged. The rank-six cover
`wave2-audit-ghb7-cyclotomic-kazhdan-cover` specifies a possible noncentral
obstruction with exact order-seven generator lifts, conditional on the
still-unproved unbounded finite visibility of a central subgroup.
