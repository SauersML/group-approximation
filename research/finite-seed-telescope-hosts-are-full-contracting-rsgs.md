---
rg: 2
id: finite-seed-telescope-hosts-are-full-contracting-rsgs
kind: claim
title: The one-chain self-simulating host ⟨V, θ_S⟩ lies in a finitely presented full contracting RSG exactly when the seed group ⟨S⟩ is finite; for infinite seeds it lies in no contracting RSG at all
requires:
  - telescope-fixed-points-are-singular-on-a-parse-shift
  - contracting-rsgs-embed-in-fp-simple-groups
  - hyperbolic-groups-lie-in-the-permutational-class
distinct_from:
  telescope-fixed-points-are-singular-on-a-parse-shift: that constructs θ_s and identifies its singular set, the golden-mean parse shift Y; this decides the finiteness test T1 of Conjecture SS, by computing the nucleus of ⟨V, θ_S⟩.
  contracting-rsgs-have-fp-full-closures: that shows full closures of contracting RSGs stay contracting; this exhibits a new family of contracting RSGs whose elements are singular (relative to V) on an uncountable SFT, and shows the family stops exactly at finite seeds.
  self-simulating-hosts-over-one-ended-parse-shifts: that is the open multidimensional Conjecture SS; this settles its one-chain calibration T1.
---

**ESTABLISHED** by `finite-seed-telescope-hosts-contracting-rsg-proof` (lane proof, elementary
given the Belk–Bleak–Matucci–Zaremsky imports already on main; not reviewed; no priority claimed).

**Setting.** `C = {0,1}^ω` is the full binary shift (one node, two loops, so an irreducible
core). `U = (0^+1)^* 1` is the parse code and `Y` the golden-mean parse shift, as in
`telescope-fixed-points-are-singular-on-a-parse-shift`. For a homeomorphism `s` of `C`,
`θ_s(uw) = u s(w)` (`u ∈ U`), with `θ_s = id` on `Y`. Write `φ_s` for its companion, the same map
started inside a block: `φ_s(0w) = 0 φ_s(w)` and `φ_s(1w) = 1 θ_s(w)`. Let `S ⊂ V` be finite, and put
`H = ⟨S⟩ ≤ V`.

**Theorem.**
1. **(Finite seed.)** If `H` is finite, then
   `N_H = {id} ∪ {θ_h, φ_h : h ∈ H} ∪ {h|_β : h ∈ H, β a finite word}`
   is a finite nucleus of injections, in BBMZ's sense (arXiv:2309.06224, Definition before
   `prop:NucleusHasProperties`). So
   `𝕋_H = {f ∈ R_2 : Nuc_f ⊆ N_H}`
   is a full contracting RSG (`thrm:RSGCharacterization`) containing `V` and every `θ_h` and `φ_h`.
   Hence:
   - `𝕋_H` is finitely presented (`thrm:fin_pres`);
   - `𝕋_H` embeds in a finitely presented simple group (`prop:contr_to_simple`);
   - `𝕋_H` is a type (A) actor, so it lies in `B_A` (`hyperbolic-groups-lie-in-the-permutational-class`).
   The full closure `[[⟨V, θ_S⟩]]` is a full contracting RSG inside `𝕋_H`, so it is finitely
   presented too (`contracting-rsgs-have-fp-full-closures`).
2. **(Infinite seed.)** If `H` is infinite, then every RSG containing `⟨V, θ_S⟩` has an infinite
   nucleus: it contains the pairwise distinct maps `θ_h` (`h ∈ H`). So `⟨V, θ_S⟩` lies in no
   contracting RSG, and BBMZ's finiteness theorem says nothing about it.
3. **(Uncountable singular set.)** For `h ≠ 1` the element `θ_h ∈ 𝕋_H` agrees with no element of `V`
   near any point of `Y`, a perfect uncountable SFT. So full contracting RSGs already contain
   elements that are singular, relative to `V`, along an entire subshift of finite type. This is
   unlike Belk–Hyde–Matucci finite germ extensions, which allow only finitely many singular points.

**Calibration.** Take `H = {1, σ}` with `σ` the swap of the cones `0C` and `1C`. Then
`N_H = {id, σ, θ_σ, φ_σ}`, since the local actions of `σ` are `σ` at the root and the identity
elsewhere. `𝕋_H` is a finitely presented full RSG containing `V` and the element `θ_σ`. `θ_σ` flips
the first letter after the first terminating block `1` of the parse. It is an exponential-activity
transducer: its nontrivial sections at level `n` are counted by Fibonacci numbers.

**Lesson for general BH.** Self-simulation along one chain costs nothing, provided the seed is
finite.
- **Finite seed.** The telescope fixed points are exactly the contracting regime of
  rational similarity groups. The golden-mean parse shift, an uncountable SFT singular set, is
  absorbed by BBMZ's finite-nucleus finiteness theorem. So "locally unique parse with finitely many
  parse states" is the one-chain form of "finite nucleus".
- **Infinite seed.** An infinite seed group forces an infinite nucleus, and with it leaves every
  contracting host.
- **Design rule.** Seeds must be finite, and the input must enter through the acting group,
  never through the seeds. This is what Conjecture SS prescribes. It is also consistent with
  `telescopic-germ-bases-in-v-germ-extensions-are-v-separated` item 5: seeds only propagate.

For the multidimensional conjecture this gives a decomposition, recorded as Attempt 1 on
`self-simulating-hosts-over-one-ended-parse-shifts`:
- the seed part is always a contracting-RSG problem, already solved;
- the whole difficulty is the V-stabilized full group of `Λ⋉X` over the two-sided SFT, i.e. P2′,
  which the parse cannot reach.
