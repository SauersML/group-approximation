# Bespoke route to `BareDefectSourceData` (2026-08-22)

Coordinator's design. Closes the W6 scope gap found in the 2026-08-22
survey: `ChiodoBelegradek.Statement` alone reaches only
`UniversalTorsionFreeHost`; the missing half toward the source base is
`KazhdanEnvelope`, and this note pins how BOTH halves feed the endpoint
with no literature input.

## 1. Source base from KC.21 (in-repo permanence only)

Claim: `Nonempty UniversalKazhdanGroup` (KC.21,
`Sofic/FournierFacioUniversalGroup.lean:271`) implies
`BareDefectSourceData P E` inhabitation, with only in-repo lemmas.

Construction. Let P be the KC.21 group. P × P is f.p. (Mathlib product
closure) and power-torsion-free (`isPowerTorsionFree` closes under
products componentwise); universality gives an injective
j : P × P →* P. Set

* alpha : P →* P, alpha := j ∘ (·, 1) — a proper self-embedding
  (proper because j(1, x) centralizes the image, next bullet, while P
  has trivial-centralizer elements);
* s := j(1, x) for an x chosen below — s centralizes alpha(P), since
  (1, x) centralizes P × {1} in P × P and j is a homomorphism;
* E := HNN(P, alpha, u), so u · iota(p) · u⁻¹ = iota(alpha p).

Fields of `BareDefectSourceData P E`:
* kazhdan: KC.21's `kazhdan` field.
* compresses: the HNN relation, delta := alpha p.
* commutesAfterCompression: s commutes with iota(alpha p) — the
  centralizing bullet, pushed through iota.
* witness / witness_commutator_ne_one: choose x with j(1, x) not
  central in P. Such x exists: otherwise j({1} × P) ⊆ Z(P); but
  universality embeds F₂ into P, so {1} × F₂ maps injectively into an
  abelian (central) subgroup — contradiction with F₂ nonabelian. Then
  some p₀ has ⁅j(1,x), p₀⁆ ≠ 1 in P, hence ≠ 1 in E (iota injective).
* E torsion-free: `Algebra/HNNTorsionFree.isPowerTorsionFree_hnn`
  (in-repo) from P torsion-free.
* E f.p.: HNN finite-presentation permanence (in-repo, S8 lane —
  alpha(P) is f.g. as the image of a f.g. group).

So the whole source-base question reduces to KC.21, which the repo
already composes as `UniversalKazhdanGroup.ofInputs`:
Host (`UniversalTorsionFreeHost`) + Envelope (`KazhdanEnvelope U`).

## 2. Host half — under attack

Host ⇐ `ChiodoBelegradek.Statement` ⇐ four inputs
(`Higman/FinalReduction.lean:49`), currently reduced to the nine leaves
of the 2026-08-22 survey; the running W6 fleet owns them
(OmegaInput, SwapWitness, base S, three row facts via one lemma,
TheoremThree, TransportSectionFive, BridgeRecursive effectivity).

## 3. Envelope half — bespoke relative router, NOT Osin 2.4.5

`KazhdanEnvelope U` needs: f.p., torsion-free, (T), U ↪ carrier.
The literature route (Osin small-cancellation over relatively
hyperbolic groups + a torsion-free hyperbolic Kazhdan partner) is out
of scope: the in-repo `HyperbolicKazhdanPartner` is a typed literature
input and the hyperbolic apparatus is absent.

Bespoke replacement: run the repo's OWN router pattern relatively.
Take the free product U * B with B := Γ(3) (`gamma3Partner` — f.p.,
torsion-free, (T), certified). Impose a C'(1/7) family of relators in
which every generator of B is tied to a long U*B-word and vice versa,
symmetrized, no proper powers, every relator ≥ 42 syllables
(FragmentSlack: whole-syllable C'(lam) is WEAKER than classical; the
slack condition lam·wlen r + 1 ≤ (1/6)·wlen r forces lam < 1/6 —
lam = 1/7 at ≥ 42 syllables is the recorded concrete pair). Then:

* (T): the tie relators make B ↠ quotient surjective — (T) descends
  (same mechanism as `RoutingLemmaData`'s derived kazhdan).
* U ↪ quotient: the free-product Greendlinger FACTOR EMBEDDING — the
  conditional layer already in-repo
  (`OsinRelativeSmallCancellation`, `FreeProductConjugacy`,
  conditional on `GreendlingerLengthBound` + `TorsionIntoFactors`).
* torsion-free: `TorsionIntoFactors` + both factors torsion-free.
* f.p.: finitely many relators over a f.p. free product.

The two conditioning predicates are exactly what the relative-transfer
draft (`notes/lean_drafts/Sofic_GreendlingerRelativeTransfer.lean.txt`,
two open leaves: `greendlingerConclusion_of_slack`,
`cyclicTorsionIntoFactors_of_slack`, Lyndon–Schupp V.9–11 over
syllables) exists to supply. CONSEQUENCE FOR SEQUENCING: the relative
transfer is NOT needed for the torsion-free router (free lane) but IS
on the critical path for the ENVELOPE, i.e. for the fully bespoke
source base. It becomes a dispatch target the moment the free-lane
gate closes, since the syllable-level argument is the same
combinatorial core re-run over `wlen`.

## 4. What this buys

The full torsion-free program becomes: nine Higman leaves + two
relative-transfer leaves + the free-lane gate (already decomposed to
DeepArcSource / LandingProductionBeta / sharp twins) + the router
family (transcription in flight) — every remaining atom is either
combinatorics over explicit words or already-scaffolded assembly.
No typed literature input survives anywhere on the chain.
