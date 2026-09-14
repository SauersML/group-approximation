# gk3-post-surjective-decoders — where a decoder's free rule matters (2026-09-14)

Lane `gk3-post-surjective-decoders` executes the exact gap of `gk3-dual-surjunctivity` (2b23c4fc8):
`strict-pairs-admit-post-surjective-decoders`.

**Question.** Given a strict pair (injective, non-surjective `τ` with decoder `σ`, `σ∘τ = id`) over
`G`, can some strict pair over `G` have a post-surjective decoder? With
`post-surjective-decoders-convert-strict-pairs-to-dual-failures` this gives
`dual-surjunctive-groups-are-surjunctive`. With the dual conjecture of Capobianco–Kari–Taati it gives
Gottschalk.

**Verdict: partial, unreviewed.** The target stays OPEN. The lane landed one theorem that shrinks the
place where any decoder can fail post-surjectivity, and killed two natural routes.

## 1. Pins

- **Doucha–Gismatullin** (arXiv:2008.10565, TeX source on MSI, `dualsurjunctive.tex` l.146–154):
  - "A CA `T: X → Y` is strongly post-surjective if there exists a finite set `M ⊆ G` such that for
    every `x ∈ X` and `T(x) ∼ z ∈ Y` there exists `y ∈ X` such that `y ∼ x`, `T(y) = z` and
    `Δ(x,y) ⊆ Δ(T(x),z)·M`."
  - "A CA `T: A^G → A^G` is post-surjective if and only if it is strongly post-surjective."
  - (l.176) "Let `X, Y ⊆ A^G` be subshifts and `Y` be strongly irreducible. Let `T: X → Y` be a
    strongly post-surjective CA. Then `T` is surjective."
- **Capobianco–Kari–Taati** (DMTCS 2017): the definitions and theorems are already quoted in
  `capobianco-kari-taati-dual-surjunctivity-toolkit`. The PDF on MSI has no text-extraction tool, so
  the balancedness results of that paper were not re-read.

## 2. The theorem landed

`decoders-lift-changes-away-from-infinite-defect-chains`, proof route
`decoder-defect-chain-repair-proof`.

1. **Decoders ↔ retractions.** For a fixed encoder `τ` with image `Y`, `σ ↦ τσ` bijects decoders onto
   automaton retractions onto `Y`, with inverse `r ↦ σ₀ r`. The free part of a decoder's rule is
   exactly the free part of a retraction's rule off the image language `L`.
2. **Transfer.** `σ` is post-surjective iff `E = τσ` lifts finite changes inside `Y`.
3. **Repair lemma.** Let `D(x)` be the sites whose `W`-window is not an image pattern, with
   `U = W⁻¹W`. If the adjacency components of `D(x) ∪ F` meeting the change set `F` are finite, then
   overwriting `x` by the target image configuration on those components gives the lift. Every
   window straddling the overwritten set sees target symbols inside and, on the defect-free collar,
   symbols where `x`, `E(x)` and the target agree.
4. **Corollary.** A decoder can fail post-surjectivity only at a change adjacent to an infinite
   component of `D(x)`.
   - (b) of the conversion claim is the case where `D(x)` is finite.
   - The configurations in (e) there, with sparse Garden-of-Eden occurrences, are lifted by repair.

**Calibrations.**
- **Cross-alphabet toy** (`A ⊂ B`, `τ` the inclusion, `σ` the sitewise retraction): `W = U = {1}`,
  so all components are single sites. The theorem predicts post-surjectivity everywhere, which holds.
- **Amenable groups:** no strict pairs, so nothing to test.
- **Periodic configurations:** for finite-index `H`, `τ` injects `Fix(H)` into itself, a finite set,
  so every configuration with finite orbit lies in `Y` and has no defects.

## 3. Routes killed

### 3.1 Conjugacy of unequal full shifts (dead on arrival)

Plan: a conjugacy `φ: A^G → B^G` with `|B| < |A|` gives `τ = ι∘φ` and `σ = φ⁻¹∘r` (`r` sitewise
retraction). `σ` is post-surjective because sitewise retractions and conjugacies lift changes.
Dead: `full-shifts-with-different-alphabets-are-not-conjugate` (ESTABLISHED on main): a conjugacy
bijects the constant configurations, so `|A| = |B|`. Recorded so nobody retries it.

### 3.2 Affine free rules

Plan: choose the decoder affine, so (c) of the conversion claim makes it post-surjective for any
encoder. Dead as a new route: `disjoint-footprint-decoders-force-kaplansky-failure` (ESTABLISHED,
Special cases) shows that a strict pair with an affine decoder over `F_q^n` is a matrix Kaplansky
pair. Conversely a one-sided inverse in `M_n(F_p[G])` gives a linear strict pair with a linear
decoder. So strict pairs with affine decoders exist over `G` iff some `M_n(F_p[G])` is not directly
finite. The affine route to post-surjective decoders is exactly the Kaplansky route.
- Independent check (not landed; it duplicates that node). Take the reduced polynomial representative
  of an automaton section `τ` of a linear `L`. Homogeneous components are preserved by the linear
  composite, so the degree-one part of `τ` is a linear section of `L`.

### 3.3 Shift rule on defect windows (a design, not a theorem)

Design: `σ(x)(g) = τ⁻¹`-rule when `x|_{gS} ∈ L_S(Y)`, and `σ(x)(g) = x(gs₀)` otherwise, for a fixed
`s₀ ∈ S`.
- **Robust interiors.** Suppose every window in a neighbourhood of `g` stays non-image under every
  change of `x(gs₀)` (e.g. windows containing two disjoint Garden-of-Eden occurrences). There a
  change of `σ(x)(g)` lifts by changing the single symbol `x(gs₀)`. No other defect window reads that
  symbol through the shift rule.
- **Where it breaks.** At *gates*: sites where the window is a non-image pattern that a single change
  turns into an image pattern, or the reverse. There the rule switches between `τ⁻¹` and the shift,
  and the output at a neighbouring site can move. An infinite defect component meeting `F` always has
  gates on the boundary of any finite repair set, which is exactly the failure locus of the repair
  lemma.
- **Exact constraint.** A decoder of this shape is post-surjective iff, at every gate configuration
  reachable along an infinite defect chain, some bounded modification keeps every gate output
  unchanged while realizing the target symbol. No choice of `S`, `s₀` or robustness threshold was
  found that satisfies it in general.

### 3.4 Obstruction certificates

A certificate "every extension of the forced rule fails" needs a concrete strict pair, and none is
known over any group. Planted settings where strict objects exist do not supply one:
- **Cross-alphabet toy:** its decoder is post-surjective (§2), so there is no obstruction there.
- **Arrow shifts** (`nonamenable-groups-carry-arrow-shift-strict-automata`): copying along arrows
  with decoder `σ(y)(h) = y(ι(h))`, for an injective arrow section `ι`, lifts changes sitewise. It is
  post-surjective on the arrow subshift. The arrow data is not a free full-shift coordinate, so this
  is not a Gottschalk object.

Both planted positives are projections along an injective choice of site. A full-shift decoder has
no such choice available on periodic configurations, where every configuration is in `Y` anyway.

## 4. Exact gap

`strict-pairs-admit-post-surjective-decoders` is equivalent, for a fixed encoder, to choosing a
retraction onto `Y` that lifts changes *adjacent to infinite adjacency components of the defect
set*. Everything else is automatic by repair. A proof must control gate outputs along infinite
defect chains. A refutation must exhibit a strict pair, which does not exist on any known group,
together with an infinite defect chain where no gate-preserving bounded modification exists for any
retraction.

## 5. Status of files

- Landed: this artifact, `decoders-lift-changes-away-from-infinite-defect-chains`,
  `decoder-defect-chain-repair-proof`, and a reduction paragraph in
  `strict-pairs-admit-post-surjective-decoders`.
- No compute was run. The MSI work was source reading only, under
  `/scratch.global/sauer354/gk3-post-surjective-decoders/`.
