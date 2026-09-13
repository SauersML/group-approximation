# EX review, groups: part 3. Thompson F dictionaries, and Pi^0_2-completeness of residual finiteness

Lane `ex-verify-groups`, 2026-09-13, 00:05 CDT. Index: `ex-review-groups-2026-09-12.md`.

## 3.0 Recheck of statuses at tip `5e3b2f7eb`

The local two-stratum fixpoint of part 2 §2.0 was rebuilt at this tip. Pass 1 and pass 2 agree on all 8,133
established claims, so no dead route fires anywhere.
- `infinite-simple-kazhdan-hyperlinear-group` (Pestov 9.1) and `simple-kazhdan-lef-group-from-minimal-subshift`
  now compute ESTABLISHED. That is the combining route landed after the part 1 PASS. It is reviewed and
  expected.
- `residual-finiteness-of-finite-presentations-is-pi2-complete` computes ESTABLISHED (§3.2).
- These compute OPEN, as they should:
  - Thompson V/F soficity, amenability and hyperlinearity (both signs);
  - `non-weakly-sofic-group-exists`, `fg-simple-weakly-sofic-groups-are-sofic`;
  - Q3.4 either way, `non-hyperlinear-group`;
  - `left-orderable-non-sofic-group`, `infinite-left-orderable-kazhdan-group`, `unique-product-non-sofic-group`;
  - the determinant conjecture either way, Strong Atiyah torsion-free and its algebraic counterexample;
  - hyperbolic VTF, non-RF hyperbolic, `every-hyperbolic-group-is-good`;
  - `sl3z-admits-nonsofic-action`, `mixing-free-nonsofic-action-of-sofic-group`, `f2xf2-admits-nonsofic-action`;
  - Bernoulli classification either way, positive Rokhlin entropy, `kun-thom-wreath-bernoulli-rokhlin-maximal`;
  - `hyperlinear-fp-infinite-simple-group`, `nonsofic-groups-satisfy-benjamini-schramm`, Gottschalk,
    Kaplansky zero divisors and units.
- `thompson-v-sofic-via-folner-full-group-theorem` (`requires: []`) is killed by the established
  `cuntz-groupoid-admits-no-folner-sequence`. `thompson-v-is-sofic` computes open.
- `rokhlin-maximality-ascends-amenable-normal-extensions` (ex-rokhlin-lower, 16138868dd) is OPEN, with
  honest Attempts. Its route into the Kun–Thom wreath root does not fire.

## 3.1 ex-thompson-v-soficity: the Thompson F dictionaries (183c0f394e, f2d0166f7e). PASS

**`thompson-f-sofic-iff-relator-system-unstable`.** Re-derived around the cycle 1 ⇒ 4 ⇒ 3 ⇒ 2 ⇒ 1.
- **Exact solutions.**
  - `F'` is infinite simple, so finite images of `F` are abelian and solutions in `Sym(n)` are exactly
    commuting pairs.
  - The relators are commutators, so every commuting pair solves them.
- **Character.** For an almost-homomorphism along `ω`, `χ(g) = lim |Fix φ_n(g)|/k_n` is a character.
  - It is normalized.
  - It is a class function, since Hamming distance is conjugation invariant.
  - It is positive definite through the permutation identity, and the defects vanish in the limit.
  - Dudko–Medynets Corollary 3.3(2) (quoted verbatim in the citation route) together with Choquet
    decomposition gives `χ = t τ_reg + (1-t) χ_ab`. So `χ = 1 - t` on `F' \ {e}`.
- **1 ⇒ 4.** If `t > 0`, use `φ_n^(x m) x τ_N∘ab`.
  - The defect is at most `m` times larger.
  - Once `N` is large, elements outside `F'` translate the torus without fixed points.
  - Elements of `F' \ {e}` fix a proportion `(1-t)^m`.
  - This gives sofic approximations.
- **4 ⇒ 3.** Take `δ_n`-solutions with `d(AB, BA) >= ε`, and evaluate fixed words.
  - The defect of `gh` is at most (van Kampen area) x `δ_n`, since Hamming distance is bi-invariant and
    conjugation invariant.
  - `d(AB, BA) = 1 - |Fix [A,B]|/n`, so `χ([a,b]) <= 1 - ε`, and `t >= ε`.
- **3 ⇒ 2.** Arzhantseva–Păunescu's Main Theorem with `k = 2`: nearby commuting pairs are solutions.
- **2 ⇒ 1.** In a sofic approximation `φ_n([a,b])` is far from `id`, while stability makes it close.

**`thompson-f-hyperlinear-iff-relator-system-hs-unstable`.** The same cycle with the normalized trace:
- `||UW - WU||_2^2 = 2 - 2 Re tr [U,W]`, so `t >= ε^2/2`;
- tensor powers times `λ_((Z/N)^2)∘ab` have trace `→ 0` off `e`;
- `Z^2` is HS-stable (`chordal-abelian-graph-products-hs-stable`, which computes established).

PASS. Novelty and credit: not checked. The one-directional remark is Arzhantseva–Păunescu's, and the
converse is natural once Dudko–Medynets is in hand. Keep both lines unreviewed for priority until
`ex-novelty` looks. Neither result touches the open roots: the route
`hyperlinear-nonsofic-from-thompson-f` requires two open claims.

## 3.2 ex-complexity-sofic: `RF_fp` is Pi^0_2-complete (076f1bec8c, 0f7c32377c). PASS after correction

Artifacts `rf-fp-pumped-minsky-part1..3-2026-09-12.md`. Imports were checked against KMS arXiv:1204.6506v5,
pp. 22–24, read from the PDF fetched on MSI. That covers formula (13), the automorphisms `a_j`, `ã_j`, `A_j`,
the definition of `Ḡ` as `T_1 x| <automorphisms>`, Lemma 4.9, and Lemmas 4.10–4.11, the surjection
`G -> Ḡ`.

- **Lemma A (`pumped-divergent-minsky-word-lies-in-profinite-kernel`): FAIL as first stated, corrected in
  `ec53d79731`, now PASS.**
  - The first statement took `c' = (c; π=1, ρ=0)` and asserted `ι(c') = 1`. But
    `ι = e_π - e_ρ - e_τ = 1 - e_τ(c)`.
  - Counterexample: let `c` be the Add-successor of a clock-zero divergent `c_0`. Running that Add
    backward from `(c; 1, 0)` gives `(c_0; 0, 0)` at a nonzero command, the drain fires, and `w(c') = 0`.
  - The correction uses `e_π(c') = 1 + e_τ(c)`. Then `ι = 1`, and a drain needs `ι = -e_τ <= 0`.
  - Step 2 was re-derived. `f -> f * a_π` is a sum of conjugations of `f` in the abelian `T`, so it
    induces an endomorphism `P̄` of `φ(T)`, and an idempotent power gives `P̄^(tD+D) = P̄^D`. The chain is
    forward computation, then `D` pumps, collapse, `D` unpumps, drain.
  - The completeness route is unaffected, since Lemma C's divergent configuration has `e_τ = 0`.
- **Lemma B (`pumped-halting-clocked-minsky-group-is-residually-finite`): PASS.**
  - **B1.** Forward-then-backward normal forms by Lemma 2.1. The backward length is `<= 2 l_τ + 1`,
    because each forward Add adds a clock coin and each Sub or zero test is followed by `Add(τ)`. So the
    classes are finite.
  - **B2(ii).** `ι` is invariant, the unpump count is `m'(X) + p - m'(X')`, and the exponents stay `>= 1`.
  - **B3.** `ι mod D` is invariant under the periodic relations, and `D` exceeds every relevant
    `|ι| + l_τ` and `ι`-difference. So zero-ness and distinctness transfer exactly, and the Rees quotient
    is finite.
  - **B4, checked against formula (13).** Each letter acts on `z_(i,u)` through `z_(i',u)` and `z_(i,uℓ)`,
    and the case depends only on whether `u` contains `A_j` or `A_0`. So the generators of `F` map into
    `F`, by right-multiplication compatibility of the finite congruence and ideal. `φ(F) <= F` with equal
    finite index gives `φ(F) = F`.
  - `Ḡ/F = (T_1/F) x| A`, with `A` the finitely generated metabelian image of `<L_1 ∪ L_2>`, is
    finite-by-residually-finite and split, hence residually finite. The kernel of the action on `T_1/F`
    has finite index.
  - The part used without re-reading: Lemma 4.14, injectivity of `G -> Ḡ` on `T`, and Theorem 4.3(b).
- **Lemma C (`clocked-search-machine-halts-universally-exactly-on-inf`): PASS.**
  - LOOP constructs with fresh, only-decremented counters terminate from any contents.
  - `|W_(e,s)| > n` is monotone in `s`, so on INF every round sequence stops.
  - On FIN, the `L0` configuration with `N = |W_e|` and all else `0` diverges, and its `τ = 0`.
- **Membership.** `RF_fp ∈ Pi^0_2` is the Lean-backed baseline clause.
- **`lef-of-finite-presentations-is-pi2-complete`: PASS.** Finitely presented LEF equals residually finite
  (Vershik–Gordon). The `(LEF1)` normal form was re-checked in both directions.

Open-status and credit. The baseline node calls `Pi^0_2`-completeness of `RF_fp` "the residually finite
Higman problem, open in the literature". That status was not independently checked here. The Part 1 remark
and Part 2 §5, noting that KMS's intermediate displays do not separate or assume non-acceptance, are credible
readings but were not re-verified line by line. Before this is relayed as the first answer, it needs an
`ex-novelty` pass on "residual finiteness finitely presented Pi02 complete".

## 3.3 Not yet reviewed (queued)

- `binary-leavitt-unit-group-is-permutation-stable` (8080fb4738). This is plausible: the character simplex
  is trivial plus regular, and nonsoficity forces `t = 0`.
- `determinant-conjecture-gives-one-variable-atiyah-base-change` (3838d36e60). It is conditional, with its
  hypotheses named.
- The remaining priority-2 queue of part 2.
