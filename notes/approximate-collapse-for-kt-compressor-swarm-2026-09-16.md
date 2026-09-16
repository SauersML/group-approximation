# approximate-collapse-for-kt-compressor -- swarm attack 2026-09-16

Agent: swarm-approximate-collapse-for-kt-co. Hole worked:
`approximate-collapse-for-kt-compressor` (the (AC)/(CCR) wall for the
Kun--Thom Theorem E pair). Outcome: an exact **reduction** (a rigidity
equivalence). (AC) itself remains OPEN.

## Setup

- `Gamma = EL_r(F_q[x_1..x_d])` inside `G = EL_r(F_q[x^(+-1)]) semidirect SL_d(Z)`,
  with `r, d >= 3`.
- Compressors `L in SL_d(N)` act by `beta_L(x^n) = x^(Ln)`.
- For a homomorphism `sigma : G -> U(M)` put `C_0 = sigma(Gamma)' cap M`.
- (CCR)_t: `sigma(t Gamma t^(-1))' cap M = C_0`. The containment `>=` is
  automatic.

## What was proved (new claim + direct proof)

Claim `kt-compressor-commutant-collapse-is-all-or-nothing`, route
`kt-compressor-commutant-collapse-all-or-nothing-proof` (`requires: []`),
artifact `research/artifacts/kt-commutant-all-or-nothing-2026-09-16.md`.

The theorem holds for every homomorphism `pi` into every group `U`. Eight
conditions are equivalent:

1. (CCR)_t for ONE `t in SL_d(N) \ A_d`;
2. (CCR)_g for all `g in P_Gamma`;
3. `pi(G)` normalizes `C_0`;
4. `C_0 = C_U(pi(E))`;
5. `pi(e_12(f))` commutes with `C_0` for ONE `f in R \ R_+`, for example
   `x_1^(-1)`; equivalently `C_U(pi(EL_r(F_q[x_1^(+-1),x_2..x_d]))) = C_0`;
6. some `L in SL_d(Z) \ A_d` normalizes `C_0`;
7. the `SL_d(Z)`-stabilizer of `C_0` has finite index;
8. one monomial torus element `diag(x^m, x^(-m), 1, ...)` with `m != 0`
   normalizes `C_0`.

If they fail (a wall), then:

- every strict monomial compressor grows the commutant;
- the `SL_d(Z)`-stabilizer of `C_0` is exactly `A_d`;
- no `pi(e_kl(f))` with `f` non-polynomial commutes with `C_0`.

Engine:

- Take the saturation `Gamma^sat = {g : pi(g) commutes with C_0}`. It has the
  same commutant, its normalizer is the stabilizer of `C_0`, and compressors
  preserve it.
- Its root set `S = {f : e_12(f) in Gamma^sat}` is a compressor-stable subring
  `R_+ <= S <= R`.
- Subring dichotomy lemma: such an `S` is `R_+` or `R`. The proof uses a
  `K`-adic lexicographic functional placed as the first row of a nonnegative
  unimodular matrix, then a unitriangular clean-up to reach `x_1^(-1)`.
- The combinatorics were sanity-checked on 9000 random supports
  (`experiments/kt-commutant-all-or-nothing-2026-09-16/`).

Consequences for this hole:

- (AC) does not depend on which strict monomial compressor is used.
- Model by model, one-compressor (CCR) and full normalization coincide at the
  Theorem E pair. This corrects, for this pair, the "strictly weaker" remark in
  `kt-centralizer-normalization-hs` (Attempts, 2026-08-18 item 1).
- An enemy is exactly one element of `sigma(Gamma)' cap M` that fails to
  commute with the SINGLE unitary `sigma(e_12(x_1^(-1)))`.

## Approaches tried and exactly where each dies

1. **Leverage the `A_d`-rigidity with property (T) of `SL_d(Z)`.** In a wall
   model the orbit `L -> Ad sigma(L)(C_0)` has stabilizer `A_d`, so it is
   infinite. A fixed-point argument needs an affine isometric action on a
   Hilbert space with a bounded orbit. The natural candidate is the orbit of
   the projection `e_(C_0)` on `L^2(M)`. But `e_(L C_0) - e_(C_0)` has infinite
   rank in any wall: strict inclusion `C_0 < L C_0` needs infinite
   dimension, by vanguard item 2 of the target. So there is no
   Hilbert--Schmidt cocycle, and in operator norm (T) gives nothing.
   *Dies at: no Hilbertian distance between commutants.*
2. **Pure relative (T) on the one-root form.** The pair
   `Gamma <= Gamma_1 = EL_r(F_q[x_1^(+-1),x_2..])` is a Kazhdan-in-Kazhdan
   pair with no compressor inside `Gamma_1`. In the quasi-regular
   representation on `l^2(Gamma_1/Gamma)`, `delta_Gamma` is
   `Gamma`-invariant but not `Gamma_1`-invariant. So no representation-only
   argument can give `C_U(pi(Gamma_1)) = C_0`. This is the same fence as the
   target's "opening lemma" item (ii). *Dies at: the matricial ambient must
   be consumed.*
3. **Entropy or size of the shift endomorphism.**
   `Psi_t = Ad sigma(t)^* |C_0` is an injective trace-preserving endomorphism.
   The dichotomy says it is non-surjective for all strict `t` or for none.
   A one-sided Bernoulli shift has exactly this shape (the lamp model in
   `kt-canonical-hs-normalization-fails`), and no size invariant of `Psi`
   alone forbids it. *Dies at: the endomorphism picture is realized
   abstractly.*
4. **Index multiplicativity across compressors.** `A = C B` with `C in A_3`
   gives growth indices `infinity = 1 * infinity`. The dichotomy explains why:
   non-normalization is all-or-nothing, so products carry no extra inequality.
   *Dies at: infinite index is absorbing.*
5. **`L^2`-reformulation.** A wall means `L^2(M)^(Ad sigma(Lambda))` is not
   equal to `L^2(M)^(Ad sigma(Gamma))`, with fixed vectors equal to
   `L^2` of the relative commutants. By the theorem this is the same as a
   `Gamma`-invariant vector not invariant under the single unitary
   `Ad sigma(e_12(x_1^(-1)))`. This is an honest reformulation, and it gave no
   new mechanism.

## Literature consulted (external gate, 2026-09-16)

WebSearch budget was exhausted: both queries returned the budget error. The
sources below were fetched through `arxiv.org/abs` and the export API, and
only abstracts or listings were read.

- Kun--Thom, *Nonsofic wreath products of residually finite groups*,
  arXiv:2608.06222 (v1 2026-08-06, v2 2026-08-19, v3 2026-08-20). The abstract
  covers nonsoficity of the wreath product and the double, and says nothing
  about hyperlinearity.
- Alekseev--Thom, *Centralizers of sofic approximations of Kazhdan groups*,
  arXiv:2608.05362 (2026-08-05). It treats permutation centralizers only, and
  the abstract states no unitary or tracial analogue.
- Export-API listings, sorted by date:
  - `nonsofic`: 2608.06222; Bowen--Burton 1906.02172 (2019).
  - `non-sofic` / `non-hyperlinear`: 2608.29599 (Liu, 2026-08-30),
    2608.21817 (Moravec, 2026-08-22), 2608.05362, 2608.02025
    (Fournier-Facio, torsion-free non-sofic group).
  - `hyperlinear AND property (T)`: 2307.13155 (Fournier-Facio--Gerasimova--Spaas,
    2023), 2211.10492 (Dogon, 2022), 1909.07800 (Brude--Sasyk).
  - `relative commutant AND ultraproduct`: 2404.17114
    (Jekel--Kunnawalkam Elayavalli, 2024), 2309.15029 (Houdayer--Ioana,
    2023), 1212.5457 (Ando--Haagerup).
- None of these abstracts treats commutant collapse for elementary groups over
  Laurent rings, or decides (AC) or (CCR). No specific search was run for the
  subring dichotomy lemma. It is elementary and may be folklore, and no
  novelty is claimed for the lemma alone.

## What remains open

- (AC)/(CCR) for trace-faithful matrix-ultraproduct models, now in single-root
  form.
- The analogue of the theorem for compressors `u L` with `u in E \ Gamma`.
- Any use of the `A_d`-stabilizer rigidity that consumes the matricial
  ambient.

## Referee (2026-09-16)

**What was checked.**

- Every step of the route `kt-compressor-commutant-collapse-all-or-nothing-proof`,
  recomputed by hand:
  - the saturation facts (G1)-(G5);
  - the Weyl-element transport (R1) and the Steinberg commutator
    `[e_13(f),e_32(g)]=e_12(fg)` (multiplied out, with `[a,b]=aba^(-1)b^(-1)`);
  - (R3)-(R5).
- The subring dichotomy lemma:
  - the lexicographic estimate `|sum_(k>k_0) K^(d-k) delta_k| <= K^(d-k_0)-1`;
  - `psi(m^(j_0)) <= -K^(d-1)+(K^(d-1)-1)/2`;
  - `det L=(-1)^(d+1)` by cofactor expansion along the last column, and the row swap for even `d`;
  - the shift `n=(n_1,M,...,M)` and the strict inequality `n_1 < -psi(m^(j_0))`;
  - the unitriangular clean-up `L' v=-e_1`.
- The worked `d=3` instance in the artifact, recomputed: `psi=(25,5,1)`, `det L=1`, the images and the shift.
- The eight equivalences. In particular:
  - the cone argument in (6)=>(5) (`L N^d=N^d` forces a permutation matrix);
  - the Whitehead membership `diag(u,u^(-1)) in EL_2(R)` in (3)=>(8);
  - `h e_13(1) h^(-1)=e_13(x^m)`, `h e_31(1) h^(-1)=e_31(x^(-m))`;
  - the generation `<Gamma,e_12(x_1^(-1))>=EL_r(F_q[x_1^(+-1),x_2,...])`.
- Hypotheses: only `r>=3` (index 3, Steinberg) and `d>=3` (transitivity of `A_d`) are used. No characteristic, finite-generation, trace or separability assumption enters. The statement fixes the convention `beta_L(x^n)=x^(Ln)`, so the claim is self-contained.
- Strict monomial compressors are exactly `SL_d(N) \ A_d`: `beta_L(R_+)=R_+` iff `L in A_d`, as in (6)=>(5), and `EL_r` of a proper subring has entries in that subring.
- Ran the experiment script, which reproduces `output.txt`. Also ran an independent stress run (6000 supports, `d in {3,4,5,6}`, sizes up to 10, entries up to 9); all assertions pass.
- Duplicates: ran `bin/cairn search --similar` and grepped for saturation/stabilizer/root-subring language. The nearest nodes are:
  - `relative-wall-commutant-growth` (invariance form, all compressors);
  - `hs-rounding-and-actor-gap-force-ccr` (a conditional (CCR) for a generating set of compressors);
  - `kt-ab-compressors-have-one-backward-commutant-edge` (consistent: its `C` lies in `A_3` and acts as an automorphism);
  - `kt-one-compressor-normalizer-cocycle-splits`.

  None states that one strict compressor, one root or one torus element forces normalization, or that the wall stabilizer is `A_d`. No duplicate was found.
- Citations: fetched the arXiv abstract pages of 2608.05362 (Alekseev--Thom, 2026-08-05, permutation centralizers, no unitary analogue in the abstract) and 2608.29599 (Liu, 2026-08-30, Poisson actions, unrelated). They match the notes. The other identifiers are already recorded elsewhere in the graph.

**What was changed.**

- Claim:
  - defined `P_Gamma` in the Setting;
  - corrected the `U=U(M)` sentence: `C_0` is the *unitary group* of the relative commutant, with the transfer argument;
  - said that the torus element in (8) is `r x r` and lies in `E`.
- Claim, overclaim removed: "the question `approximate-collapse-for-kt-compressor` does not depend on `t`" became "the exact (CCR)_t does not depend on `t`". The approximate (AC) formulation still mentions `t`, and nothing here shows that it is `t`-independent.
- Claim: the closing "both alternatives occur" paragraph is now labelled a cited remark that is not part of the proved theorem. The Clifford-cover wall is attributed to `kun-thom-clifford-cover-weakly-sofic`.
- Route: added a short paragraph proving the transfer from unitary centralizers to relative commutants.
- Removed the stray `__pycache__` directory from the experiment folder.

**Verdict.** Sound. The direct proof (`requires: []`) is complete and elementary. Landed with the small fixes above. (AC)/(CCR) for trace-faithful matrix-ultraproduct models remains OPEN. This is an exact, trace-free reduction to the single-root form, not a resolution. No novelty is claimed for the subring lemma alone.
