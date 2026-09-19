---
rg: 2
id: lambda-gamma-repetition-rates-capped-at-sqrt-gap
kind: claim
title: Domain-wall XOR games are lambda-gapped with value <= 1-gamma and SDP deficit <= 37 sqrt(lambda) gamma, so every parallel-repetition rate certified from (lambda, gamma) alone is at most 3300 sqrt(lambda) gamma and every such amplifier outputs sqrt-scale constant C'^2 < 1184 sqrt(lambda) gamma/eta; Raz--Rosen (poly(lambda) = lambda^4/log) lies in the killed linear class
distinct_from:
  expansion-certified-repetition-caps-deficit-ratio: that kills rates psi <= K gamma^2 + kappa lambda gamma, a lower-bound-free statement about linear rates, and leaves (P2) superlinear rates open; this proves an upper bound on every (lambda, gamma)-certified rate by an explicit family, capping (P2) at the sqrt(lambda) gamma example that claim names, and places Raz--Rosen, left unchecked there, inside its linear class.
  black-box-repetition-needs-sqrt-scale-soundness-gap: that caps universal (lambda-free) rates by the odd cycle, at lambda ~ gamma^2; this caps lambda-dependent rates by gapped domain-wall games at every lambda >= 128 gamma^2.
  raz-odd-cycle-repetition-lower-bound: that is one non-expanding family; the domain-wall family adds a complete-graph layer of weight 2 lambda, which keeps the frustration and forces the SDP to rotate over only 1/sqrt(lambda) of the cycle.
  bhhrrs-xor-repetition-sdp-lower-bound: that is the general SDP-to-repetition lower bound imported here; this supplies the gapped family on which it is applied.
  akkstv-expansion-parallel-repetition-bound: that is a (lambda, gamma) upper bound on repeated values with rate lambda gamma/log; this is the matching-shape ceiling sqrt(lambda) gamma, which no (lambda, gamma) bound can exceed.
  raz-rosen-expander-parallel-repetition-bound: that imports the Raz--Rosen bound; this classifies it.
  sqrt-scale-unique-games-hardness: that is the open hole; this narrows its expansion-repetition survivor.
artifacts:
  - experiments/ugc-domain-wall-repetition-2026-09-17/check_domain_wall_family.py
  - experiments/ugc-domain-wall-repetition-2026-09-17/output.txt
---

**ESTABLISHED (class ceiling, no complexity assumption; item 4 uses P ≠ NP
through `expansion-certified-repetition-caps-deficit-ratio`).** The proof is
`lambda-gamma-repetition-rates-capped-at-sqrt-gap-proof`.

**Setting.** λ-gapped, η, γ, ε', δ', the Rate class and the source gate are as
in `expansion-certified-repetition-caps-deficit-ratio`. `sdpval` is the
Figure 1 SDP of `bhhrrs-xor-repetition-sdp-lower-bound`. Write `Γ(λ, γ)` for
the class of λ-gapped two-prover XOR games of value `<= 1 − γ`.

**Domain-wall game `D(w, L)`**, for `w in (0, 1/2]` and an integer `L >= 3`.
Both provers get questions in `Z_L`. With probability 1/2 the referee asks
`(i, i)` and checks equal answers. With probability 1/2 it samples:

* with weight `1 − w`, a uniform cycle edge `{i, i+1}` in random orientation,
  checking equal answers, except on `{L−1, 0}`, where it checks unequal answers;
* with weight `w`, a uniform ordered pair `(i, j) in Z_L^2`, checking equal
  answers.

**Theorem.**

1. *(Family.)* `D(w, L)` is (w/2)-gapped and has `val <= 1 − (1−w)/(2L)`
   (tight on all checked cases). If `L >= ceil(1/sqrt(w)) + 1`, then
   `sdpval(D(w, L)) >= 1 − 3.24 sqrt(w)/L`.
2. *(Parametric form.)* For all `λ in (0, 1/4]` and `γ in (0, sqrt(λ/128)]`,
   the class `Γ(λ, γ)` contains a game with `sdpval > 1 − 37 sqrt(λ) γ`.
   This is `D(2λ, floor((1−2λ)/(2γ)))`.
3. *(Rate and output ceilings.)* Let `λ, γ` be as in item 2.
   - (a) For every `n >= 1`, `sup_(G in Γ(λ,γ)) val(G^(⊗n)) > 1 − 25 sqrt(n sqrt(λ) γ)`.
   - (b) If `ψ` satisfies `val(G^(⊗n)) <= (1 − ψ)^n` on all of `Γ(λ, γ)` for
     every `n`, then `ψ <= 3300 sqrt(λ) γ`. It is enough that this holds for
     the single `n = floor(1/(2368 sqrt(λ) γ))`.
   - (c) This holds for unique games of every even alphabet `k`, since an XOR
     game embeds into alphabet `[2] × [k/2]` with the same question graph and
     the same values of all repetitions.
4. *(Route condition.)* Take a repetition amplifier (`n` rounds, `ε' <= 1/2`)
   whose certified soundness holds on every game in `Γ(λ, γ)` and is used on a
   source `(η, γ, λ)`, with `λ, γ` as in item 2. Its output sqrt-scale
   constant `C' = (1 − δ')/sqrt(ε')` satisfies `C'^2 < 1184 sqrt(λ) γ/η`. If
   the source is hard and `P ≠ NP`, the gate `λγ <= 1592 η` gives
   `C'^2 < 1.9·10^6/sqrt(λ)`.
5. *(Raz–Rosen.)* On sources whose NO instances have biregular question graphs
   and value `> 1/2`, both Raz–Rosen certificates lie in the killed classes.
   - Theorem 2 as proved has rate `<= c_P γ λ^4/log(2/λ) <= κ λ γ` with
     `κ = c_P/log 2`. It is in `Rate(0, κ)`, so `R <= 3184 κ`.
   - Theorem 1 has rate `<= γ^2 c(λ) <= K γ^2`, with `K = 10^−12/(32 log^2 2)`.
     It is in `Rate(K, 0)`, so it is circular by item 4 of the kill.
   - Take any bound of the statement's shape `(1 − ϵ)^{p(λ)·n}` that is valid
     on all of `Γ(λ, γ)`. Item 3(b) forces `min(p(λ), 1) <= 3300 sqrt(λ)` on
     `(0, 1/4]`, via Bernoulli: `1 − (1−γ)^p >= pγ` for `p <= 1`.
     `D(w, L)` has rational weights, so it is a biregular multigraph. It is not
     claimed that Raz–Rosen's hypotheses cover multigraphs.

**Invariant and where it dies.** The invariant is the **SDP deficit of the
worst game in the certificate's class**. Repetition cannot push any game's
value below `1 − O(sqrt(n δ_sdp))` (BHHRRS). A certificate that sees only
`(λ, γ)` must therefore hold on the domain-wall game. That game spreads its
frustration over a wall `1/sqrt(λ)` links wide. The complete layer pays `λ`
per wall link and the cycle pays `1/W^2` per link, so the balance makes
`δ_sdp = Θ(sqrt(λ) γ)`. Every `(λ, γ)`-rate dies at the **rate-certification
step**, at `ψ = O(sqrt(λ) γ)`.

**Consequence for the decomposition.** The survivor pair (P1)/(P2) of the kill
sharpens as follows.

* **(P2)** can hold at most at the candidate rate: `ψ = Θ(sqrt(λ) γ)` and no
  faster. On XOR games it is equivalent, up to constants, to an SDP inequality
  `δ_sdp >= c sqrt(λ) γ` on λ-gapped games. The equivalence uses Feige–Lovász
  and BHHRRS Theorem 1.3, which are not imported here.
* **(P1)** must supply hard λ-gapped sources with `sqrt(λ) γ/η → ∞`. With the
  gate this forces `λ → 0` and `γ` in `[ω(η/sqrt(λ)), 1592 η/λ]`.
* The pair can still fail independently. Routes escape the ceiling if their
  certificates use structure beyond `(λ, γ)` that excludes domain walls, such as
  alphabet-dependent or small-set-expansion profiles, or NO classes with no XOR
  subgames. The complementary regime `γ^2 > λ/128` is not covered.
