# Swarm lane: kt-canonical-hs-normalization-fails (2026-09-16)

- **Target:** `kt-canonical-hs-normalization-fails`, i.e. some Connes-embeddable model of the Kun--Thom
  Theorem E actor, with any trace, has a non-normalized `Γ`-commutant.
- **Hole worked:** the target itself, locked with a 180m TTL under lane
  `swarm-kt-canonical-hs-normalization-`.
- **Outcome:** an obstruction. A whole class of candidate witnesses is excluded, including the lever
  recorded under "Popa's second independence case". The target stays open.

## 1. Setup

- `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, with `r, d >= 3`. `SL_d(Z)` acts by
  monomial substitution, and `N = <<Γ>>_G`.
- For `σ : G -> U(M)` put `R_σ = σ(Γ)' ∩ M` and `K_σ = {g : [σ(g), R_σ] = 0}`. Then `σ(G)`
  normalizes `R_σ` iff `N <= K_σ`.
- The target asks for a Connes-embeddable `M` and a homomorphism `σ`, with no trace condition, such
  that `N` is not contained in `K_σ`.
- The target's attempt list ended with an unchecked conditional. The established matrix-coordinate
  rounding chain gives normalization under (H1). Does it transfer to II_1-coordinate ultraproducts
  `prod_ω M_n`, e.g. `M_n = R`, with genuine vertex coordinates? If so, Popa's second independence
  case produces no witness.

## 2. Literature gate (checked 2026-09-16)

As far as these checks show, the target is still open. No hyperlinear non-sofic group is claimed in
the literature returned.

- **arXiv API, query on sofic and hyperlinear**, fetched 2026-09-16. No entry claims a hyperlinear
  non-sofic group. The newest entry returned is arXiv:2601.18742 (Alekseev--Bradford, submitted
  2026-01-26). Nothing here relies on its content.
- **Popa, arXiv:1308.3982**, abstract page fetched 2026-09-16. It confirms the two independence
  cases in the shape quoted in the target. Only the hypothesis shape is used.
- **Kun--Thom** (the Theorem E pair and the wreath). Used through the repository node
  `kun-thom-nonsofic-wreath`. The arXiv API returned HTTP 429, so the primary source was not
  re-fetched.
- **Dogon, arXiv:2211.10492, and Becker--Lubotzky, arXiv:1809.00632.** Used only through repository
  nodes on flexible HS-(in)stability. Not re-fetched in this lane.
- **Ershov--Jaikin-Zapirain** (property (T) of `EL_r` over finitely generated rings, `r >= 3`). Cited
  from memory for the Kazhdan vertex, not re-fetched and marked unverified in the artifact.
- The WebSearch budget was exhausted, so only WebFetch on arXiv pages and the API was available.

## 3. What was proven

Artifact: `research/artifacts/kt-ii1-coordinate-model-transfer-2026-09-16.md`. Claim:
`kt-genuine-atomic-vertex-coordinate-models-normalize`. Route:
`kt-genuine-atomic-vertex-coordinate-models-normalize-proof`.

1. **Theorem T (transfer).** Let `G` be countable and residually finite, `Γ <= G`, `ω` an ultrafilter
   on `N`, `M_i` Connes-embeddable, and `σ : G -> U(prod_ω M_i)` any homomorphism. Suppose
   `σ(γ) = [(ρ_i(γ))]_ω` with genuine `ρ_i : Γ -> U(M_i)` and `ρ_i(Γ)''` atomic. Then there is a
   trace-preserving `σ♭ : G -> U(prod_U M_n)`, with genuine `π_n : Γ -> U(n)` representing
   `σ♭|Γ` at every `n`, and `K_(σ♭) <= K_σ`. Ingredients, all proved in the artifact:
   - unitary and projection lifts;
   - iterated ultraproducts;
   - Connes-embeddable separable algebras sit in matrix ultraproducts, through `R^ω` and conditional
     expectations of `R`;
   - genuine realization of an atomic representation, absorbing real multiplicities by
     `floor(w_l d)` and padding with the trivial representation;
   - unitary conjugacy of atomic embeddings into a matrix ultraproduct;
   - trace correction by tensoring with regular representations of finite quotients;
   - re-indexing by dimension.

   Witnesses of non-commutation are transported at each step, so stabilizers only shrink.
2. **Theorem N.** At the Theorem E pair, every such `σ` normalizes `R_σ`.
   - `G` is residually finite, by reduction of exponents mod `m`.
   - `σ♭` satisfies (H1) with zero error and no padding.
   - The four established per-model claims then give normalization for `σ♭`:
     `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`,
     `nonunit-projection-bounded-by-root-spectral-mass`, item 5 of
     `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`, and
     `vertex-rounding-deep-nonunit-root-mass-vanishes`.
   - `N <= K_(σ♭) <= K_σ`.
3. **Corollary H.** Atomic can be replaced by Haagerup, through
   `kazhdan-images-in-haagerup-algebras-are-atomic`. For Kazhdan images, atomic, amenable and Haagerup
   coincide. So every model with amenable coordinates `M_i`, e.g. `R`, and genuine vertex coordinates
   normalizes. The conditional in the target is settled in the positive, and the Popa lever as
   recorded is dead.
4. **Sharpness.** Constant coordinates `M_i = M_0`, `ρ_i = σ_0|Γ`, with `σ` diagonal, show that
   removing atomicity turns Theorem N into the negation of the target. The converse uses that
   ultraproducts of Connes-embeddable algebras are Connes-embeddable, which the artifact sketches.
   So no strengthening in this direction is possible without deciding the target.

## 4. Approaches tried and where each dies

- **Transfer the per-model claims to II_1 coordinates directly.** Abandoned. The spectral measures
  `μ_n` and the finite Steinberg factorization use integer dimensions and genuine finite-dimensional
  representations. Rewriting four long arguments with continuous multiplicities would be error-prone.
  Transferring the **model** into their setting (Theorem T) avoids this completely.
- **Type I or bounded-dimension coordinate algebras.** Dead as a source of witnesses, already before
  this lane.
  - A type I finite algebra is amenable.
  - A single-algebra model is excluded by `haagerup-targets-carry-no-relative-wall`.
  - An ultraproduct of such coordinates with genuine vertex coordinates is excluded by Corollary H.
- **Crossed-product reformulation.** Only a restatement. Writing a witness as a lamp or crossed-product
  model over `G/K` reproduces the recorded equivalence with hyperlinearity of some coset wreath `W_K`.
  No new leverage came out of it.
- **Index or trace obstruction to the one-sided shift shape.** None exists. The target's attempt
  "Atomic commutants" requires `Ad σ(t)^*` to act as a proper trace-preserving endomorphism on a
  diffuse summand of `R`. One-sided Bernoulli shifts on diffuse algebras are such endomorphisms. No
  invariant of trace or index type rules the shape out, so this does not refute the target.
- **Reduce an arbitrary witness to one with genuine atomic vertex coordinates.** Dies at the first
  step.
  - For approximate vertex coordinates, Theorem T's conjugation still applies. But the realized
    coordinates are only asymptotically multiplicative, and (H1) for them is the open
    `hs-stable-vertex-rounding-for-every-model`.
  - For genuine vertex coordinates with non-amenable images, e.g. `M_i = L(Γ) (tensor) R`, the images
    are diffuse. No finite-dimensional realization exists, and by the sharpness item this case is the
    general problem.
- **Principal ultrafilter.** For principal `ω`, Theorem N reduces to a special case of
  `haagerup-targets-carry-no-relative-wall`. This is a consistency check, not new content.

## 5. What remains open

- The target itself.
- A witness with genuine vertex coordinates must have non-amenable `ρ_i(Γ)''` along `ω`, inside
  non-Haagerup Connes-embeddable coordinates.
- A witness without genuine vertex coordinates yields a trace-preserving matrix-ultraproduct witness
  whose vertex fails (H1). That is the recorded flexible-instability requirement.
- The weakest link a referee should attack is the black-box use of the four chain claims at `σ♭`.
  Their stated hypotheses match: the explicit pair, trace-preserving `σ : G -> U(prod_U M_n)` over a
  free ultrafilter on `N`, and (H1). Theorem T delivers exactly that input.

## 6. Correction to the target's attempt text

The target cites
`kt-regular-congruence-mask-removes-trace-faithfulness-from-the-commutant-wall` for the reduction to
trace-preserving witnesses. The node present in `research/` is
`kt-regular-mask-removes-trace-faithfulness-from-commutant-wall`, whose computed status in the local
graph cache is OPEN. Lemma 1.5 of the artifact gives a self-contained trace reduction for ultraproduct
models with genuine vertex coordinates, so nothing here depends on that node. The target node was not
edited.
