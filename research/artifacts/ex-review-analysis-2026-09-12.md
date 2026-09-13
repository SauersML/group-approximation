# EX review: operator algebras, quantum information and complexity lanes (2026-09-12)

Lane `ex-verify-analysis`, adversarial verifier of the EX swarm. One section per checked claim or
route. Long sections move to part files `research/artifacts/ex-review-analysis-2026-09-12-part<N>.md`,
indexed at the end of this file.

## 0. Scope and method

Lanes under review: ex-rank-problem-villadsen, ex-rank-problem-lix, ex-k1-properly-infinite,
ex-toms-winter, ex-uct, ex-mf-kazhdan-cstar, ex-blackadar-kirchberg, ex-rr0-dichotomy,
ex-unitary-class-three, ex-baum-connes, ex-kadison-kaplansky, ex-nh-mipstar, ex-ugc, ex-quantum-pcp.

For every node those lanes land as ESTABLISHED, and for every reduction or equivalence route others
will build on, I re-derive the argument from the statement and check the statement against its
sources. Verdicts:

- **PASS**: re-derived; the statement, every hypothesis and every citation match.
- **GAP**: the statement may be true, but the written argument does not prove it: a missing step, a
  hidden hypothesis, a citation not matched to the source, or a conditional stated as unconditional.
  The owning lane is told what would close it.
- **FAIL**: the statement is false as written, or the argument has an error that no local fix
  repairs. The route is retired or the node corrected forward, and the owning lane is told.

Priority: (1) anything that would decide a famous problem; (2) reductions others build on; (3) the
rest. The sweep runs on every landed EX node and looks for:
- a `requires: []` route whose invalidator is not itself established;
- prose saying "established" with no route into the claim;
- an id over 64 characters;
- a conditional result stated as unconditional.

## 0.1 Baseline: the famous roots of this domain before any in-scope landing

Main tip `61a14d9b6` (21:35 CDT). Statuses are from `research/FRONTIER.md` at `ecea91ac0`, which
was regenerated from `cairn check` at `3a4b43636` (20:49 CDT). Those statuses were not re-derived
here. If an EX landing flips any of these roots, that is a priority-(1) check.

| root id | statement | status | lanes |
|---|---|---|---|
| `stw23-rank-problem-counterexample-exists` | not all ranks occur (negates STW XXIII) | OPEN | rank-problem-villadsen, rank-problem-lix |
| `stw99-problem-xxiii-rank-problem` | all ranks occur | OPEN, no route | rank-problem-* |
| `stw18-strict-comparison-non-z-stable-algebra-exists` | strict comparison without Z-stability (negates XVIII) | OPEN | toms-winter |
| `stw99-problem-xviii-toms-winter-conjecture` | Toms--Winter | OPEN | toms-winter |
| `stw99-problem-lxi-properly-infinite-k1-injective` | properly infinite implies K1-injective | OPEN | k1-properly-infinite |
| `stw99-problem-ii-nuclear-uct` | nuclear UCT | OPEN | uct |
| `infinite-kazhdan-group-with-mf-reduced-cstar` | an infinite (T) group with MF reduced C*-algebra | OPEN | mf-kazhdan-cstar |
| `blackadar-kirchberg-counterexample-exists` | nuclear stably finite, not quasidiagonal | OPEN | blackadar-kirchberg |
| `stw99-problem-xxix-rr0-dichotomy` | Rordam's RR0 dichotomy | OPEN | rr0-dichotomy |
| `simple-cstar-unitary-components-class-three` | class-three unitary component group, simple | OPEN | unitary-class-three |
| `baum-connes-counterexample-group-exists` | a Baum--Connes counterexample group | OPEN | baum-connes |
| `kadison-kaplansky-counterexample-exists` | torsion-free group with a nontrivial projection in `C*_r` | no route, not a root | kadison-kaplansky |
| `non-hyperlinear-group` | an explicit non-hyperlinear group | OPEN | nh-mipstar |
| `unique-games-conjecture` | UGC | OPEN | ugc |
| `quantum-pcp-constant-gap-local-hamiltonian` | quantum PCP, constant locality | OPEN | quantum-pcp |

## 0.2 Baseline guard check: direct routes into those roots

Question: does any `requires: []` route into one of these roots fire? It fires unless an
**established** obstruction claim names it under `invalidates:`. I checked this structurally, one
invalidator chain at a time. I followed each chain until every leaf was a `requires: []` proof or
citation route. The leaves were not re-derived.

1. `stw18-k1-witness-via-ah-lix-upgrade` into `stw18-k1-witness-strict-comparison-not-k1-injective`.
   This claim is the shared prerequisite of the XVIII and XXIII counterexample routes.
   - Invalidator: `simple-ah-strict-comparison-is-k1-injective`.
   - Its proof route requires `simple-ah-strict-comparison-is-z-stable` (citation route,
     `requires: []`) and `z-stable-unital-algebras-are-k1-bijective` (citation route, `requires: []`).
   - Depth 2. Guarded.
2. `bc-counterexample-via-kazhdan-projection` and `bc-counterexample-via-leavitt-compression-classes`.
   - Invalidator: `subgroup-average-projections-give-no-reduced-bc-obstruction`.
   - Its proof requires `kazhdan-projections-vanish-in-regular-group-algebra` (proof, `requires: []`).
   - Depth 2. Guarded.
3. `bc-counterexample-via-rational-trace-mismatch`.
   - Invalidator: `leavitt-unit-group-contains-every-finite-group`.
   - Its proof requires `leavitt-cylinder-swaps-generate-thompson-in-el` (proof, `requires: []`).
   - Depth 2. Guarded.
4. `ugc-via-bkm-test-on-learnable-hardness`.
   - Invalidator: `bkm-test-transparent-on-learnable-games`.
   - Its proof requires `derived-unique-game-lower-bounds-the-noise-test` (proof, `requires: []`).
   - Depth 2. Guarded.
5. `ugc-via-subexponential-pairing-enrichment`.
   - Invalidator: `separated-small-pairing-families-defeat-the-noise-test`.
   - Its proofs require `separated-pairing-families-admit-noisy-decoders` (proof, `requires: []`) and
     item 4's leaf.
   - Depth 2. Guarded.
6. The three direct routes into `rich-2to1-games-conjecture`, which feeds UGC.
   - Invalidators: `dummy-padding-cannot-beat-the-random-guessing-floor`,
     `edge-conjugation-of-2to1-constraints-is-pure-gauge` and
     `unique-constraints-orient-at-most-half-of-a-fiber`.
   - Each has a proof route with `requires: []`.
   - Depth 1. Guarded.
7. `class-three-via-equal-dimension-towers`.
   - Invalidator: `equal-dimension-ah-component-groups-class-two`.
   - Its proof requires `stw59-monotracial-matrix-stable-counterexamples` and
     `gauge-components-over-circle-sphere-towers`.
   - Their proofs require `stw59-exact-finite-abelian-unitary-component-groups`,
     `stw59-exact-factorial-unitary-component-groups` and `samelson-circle-sphere-product-has-order-n`.
   - Depth 3. I stopped at the `stw59-*` theorems, which were reviewed on 2026-09-05 per their
     artifacts and not rechecked here.
8. `qpcp-gap-from-abn-energy-semantics` and `qpcp-gap-from-ordinary-energy-amplification`.
   - Invalidators: `abn-energy-to-fault-loss-is-exponential-in-depth` and
     `ordinary-gap-amplification-grows-locality`.
   - Each has a citation route with `requires: []`.
   - Depth 1. Guarded.
9. `non-hyperlinear-group` has 198 routes, 4 of them `requires: []`. All 4 are on the coordinator's
   invalidated-id list of 21:32. Their invalidators were not rechecked here; they belong to the NH
   verifier.

No route targets `kadison-kaplansky-counterexample-exists`, `kadison-kaplansky-torsion-free`,
`stw99-problem-vii-blackadar-kirchberg` or `stw99-problem-xxiii-rank-problem`.

**Verdict: PASS.** At `61a14d9b6` no direct route fires into a famous root of this domain.

**Tool note for peers.** In POSIX ERE, `[ ,\]]` is the class {space, comma, backslash} followed by
a literal `]`. It does not match the last id of a flow list `invalidates: [a, b]`, so a scan written
that way reports no invalidator for `b`. My first pass hit this on item 1. Use fixed-string
`git grep -F <id>` and read the matching lines.

## 1. In-scope landings

### 1.1 `fractional-matrix-trace-gives-projection-in-g-star-z` (ex-kadison-kaplansky): PASS

Priority (2). This reduction is what the Kadison--Kaplansky routes build on. It claims that
Kadison--Kaplansky for all torsion-free groups is equivalent to the trace-integrality conjecture
for all torsion-free groups. Reviewed from the lane's draft, including the proof route
`fractional-matrix-trace-gives-projection-in-g-star-z-proof`.

**Item 1 (scalarization): PASS, re-derived.** Let `A = C*_r(G * Z)` with `G ≠ 1`.
- `Z` has at least three elements, so the Avitzour data exist. Then
  `non-dihedral-free-products-are-completely-selfless` makes `(A, τ)` completely selfless.
- `robert-tracial-selfless-regularity` then gives strict comparison by `τ` on `A ⊗ K`, stable rank
  one, and `τ` as the unique 2-quasitrace.
- Robert's definition compares only by the single state `ρ`. So strict comparison is usable even
  when `G` is not exact, where 2-quasitraces other than traces could exist.
- Given a projection `p` with `τ_*(p) = k + s`, `0 < s < 1`:
  - `d_τ(1_k) = k < k + s = d_τ(p)`, so `1_k ≾ p`.
  - For projections, Cuntz subequivalence gives Murray--von Neumann subequivalence. Take `y = p r q`,
    `||y y^* - p|| < 1/2`, `z = (y y^*)^(-1/2) y`; then `p ~ z^* z ≤ q`. I checked this step.
  - So `1_k ~ f ≤ p`. Put `q = p - f`, of trace `s < 1 = d_τ(1_A)`. Then `q ~ e ≤ 1_A`, and `e`
    lies in the `(1,1)` corner, which is `A`.
  - Since `f ⊥ q`, `p ~ 1_k ⊕ e`.
- Cancellation, and so stable rank one, is not needed. Only strict comparison of projections by
  the unique trace is used.

Trust surfaces, not re-read by me:
- FKOP arXiv:2510.24675v3, Theorem A (Theorem 2.7), sourced in
  `stw91-graph-component-selflessness-audit-2026-08-30`.
- Robert arXiv:2309.14188v3, Theorem 3.1(ii). The lane quotes it verbatim from the PDF, together
  with the §3 definition.

**Item 2 (torsion): PASS.** A free product is an amalgam over the trivial group, and
`amalgam-torsion-permanence-needs-no-cyclic-reduction` has a Lean-backed `requires: []` route. The
classical Magnus--Karrass--Solitar citation is supplementary.

**Item 3 (selfless hosts): PASS as an import.** Every torsion-free acylindrically hyperbolic group
has trivial finite radical. So `ozawa-php-groups-completely-selfless` (Ozawa arXiv:2508.07938,
Theorem 14 and Proposition 15) applies, and the Item 1 argument runs verbatim.

**Corollary A: PASS.**
- (TR) ⇒ (KK): the trace is faithful, so `τ(e) ∈ (0,1)` for `e ≠ 0, 1`.
- (KK) ⇒ (TR): Items 1 and 2 applied to `Γ * Z`.
- The quantifier is "for every countable torsion-free group" on both sides. That is the only sense
  in which the title's "equivalent" holds. Per group, only the direction in Corollary B is proved.
- The idempotent remark is correct: an idempotent is similar to a projection, and similarity keeps
  the trace.

**Corollary B: PASS.** It is Items 1 and 3, read contrapositively.

**Corollary C: PASS, conditional as stated.**
- `χ_(-∞,c)(a)` and `χ_{0}(A^*A)` are continuous functions on the spectrum once `c`, respectively
  `0`, is spectrally isolated. Their traces are `τ_*(P)` and `dim_vN ker A`.
- The lattice instance consumes the OPEN `complex-with-irrational-and-torsion-free-lattices` together
  with a Laplacian gap. The node says neither instance is known.

**Wiring: PASS.**
- `kk-counterexample-via-g-star-z-scalarization` and `matrix-trace-defect-from-kk-counterexample` form
  an equivalence cycle between the two OPEN claims `torsion-free-matrix-trace-defect-exists` and
  `kadison-kaplansky-counterexample-exists`.
- Neither route is `requires: []`, so nothing fires.
- All ids are at most 58 characters, and every named id exists on main.

**Notes, no verdict change.**
- The credit paragraph states the hypotheses of Dykema--Rørdam, GAFA 8 (1998) 1--16: Avitzour
  conditions plus nuclear factors. I did not check that statement against the source.
- Novelty is correctly marked unverified. The bounded check was two web searches.

## Index of part files

- `ex-review-analysis-2026-09-12-part1.md`, §1.2: the class-three root
  `simple-cstar-unitary-components-class-three` through Toms's trapping tower over T^2 × S^3. PASS
  on all five requested items, plus the excess bound and the class-four finite stage.
- `ex-review-analysis-2026-09-12-part2.md`:
  - §1.3, the Baum--Connes module K-inexactness reduction and its four supporting theorems: PASS.
  - §1.4, the Blackadar--Kirchberg spectral structure (separating quotients, compact-free ideals,
    the traced/traceless dichotomy, the radical criterion, the trichotomy, the simple-case cycle):
    PASS.
- `ex-review-analysis-2026-09-12-part3.md`:
  - §1.5, ex-uct cyclotomic KK structure of Z_p-actions on O_2 (five claims): PASS.
  - §1.6, ex-k1-properly-infinite LXI reformulations: three theorems PASS, with one GAP (citation) in
    the consequence list of `k1-injectivity-extends-over-properly-infinite-quotients`.
  - §1.7, ex-kadison-kaplansky selfless trace image, free products and real rank zero (five claims):
    PASS.

## 2. Sweep of in-scope landings to 23:35 CDT

Checked at tip `347722257`:
- **Famous roots.** None flipped. These still read OPEN and have no route whose required claims are
  all established: Rank Problem, Toms--Winter, LXI and its negation, nuclear UCT and its negation, MF
  Kazhdan, Blackadar--Kirchberg, RR0 dichotomy, Baum--Connes, Kadison--Kaplansky, NH, UGC and its
  algorithmic negation, quantum PCP and games-QPCP.
- **New direct routes (`requires: []`) into those roots.** Each is killed by an established
  invalidator:
  - `non-uct-witness-from-cartan-respecting-automorphism`, killed by
    `cartan-respecting-o2-automorphisms-give-uct-crossed-products`, whose proof requires the
    Barlak--Li import;
  - `bc-counterexample-via-ghost-projection`, killed by
    `reduced-group-algebras-contain-no-nonzero-ghosts`;
  - `games-qpcp-from-tensor-power-amplified-xx-zz`, killed by
    `natarajan-vidick-games-pcp-amplification-error`, a citation route.
- **Wording.** `global-walk-reducer-has-net-energy-gain` and
  `o2-multiplier-ideal-with-non-k1-injective-unitization` have no route and no "OPEN" marker in their
  first line. They are not established, but a reader has to infer the status.
