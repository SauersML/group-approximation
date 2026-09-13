# One mechanism behind the non-MF paper and the Pestov 9.1 answer — synthesis, part 2

Lane `un-synthesis`, 2026-09-13, refresh 1 (main tip d1ca5488fc). Status tags as in part 1: [REVIEWED PASS · sha],
[unreviewed], [import], [printed], [OPEN].

## 8. The flagship: free-group actions

**Assembled statement** [OPEN as an assembly: its inputs are unreviewed except S4; proposed to un-architect as a
review-gated claim; no node yet].

Let `2 ≤ r < ∞` and let `F_r ↷ X` be a minimal, topologically free, expansive action on the Cantor set, so
`R = LC(X,F_q)⋊F_r` is finitely generated. Topologically free ⇒ effective holds for Hausdorff transformation
groupoids; that is standard and not re-derived here. Let `N ≥ 3`. Then `S_N = EL_N(R)/Z` is an infinite, finitely
generated, simple Kazhdan group (§3, REVIEWED PASS), and exactly one of the following holds.
- **Measure branch.** `X` carries an invariant probability measure. Then `R` is matricial (Theorem C of un-measure),
  so `EL_N(R)` is LEF for every `N` (§6), hence sofic, hyperlinear and MF.
- **Paradox branch.** `X` carries no invariant probability measure. Then some `n` has `2n[1] ≤ n[1]` (Theorem G), and
  every homomorphism from `EL_N(R)` to an MF group is trivial for `N ≥ 2n`; for `N ≥ 2` if `2θ ≤ θ` in `S(𝒢)`.
- **Open inside the paradox branch:** ranks `3 ≤ N < 2n` (§12).

**Theorem C, free groups** [unreviewed; un-measure 3f486a4805, `free-group-crossed-product-matricial-iff-invariant-measure`].
For a minimal topologically free `F_r ↷ X` (`r ∈ ℕ ∪ {∞}`) and a field `k`, the following are equivalent:
- an invariant probability measure exists;
- the action is residually finite;
- `LC(X,k)⋊F_r` embeds unitally in some `∏_ω M_N(k)`;
- it admits a unital homomorphism into one;
- it carries a unital Sylvester matrix rank function.

Inputs: Kerr–Nowak Thm 5.2, a secondary import through Ma arXiv:2209.00580. The primary paper is still to be checked
(`kerr-nowak-measure-free-group-actions-are-rf`).

**Why free groups.** For free groups "measure ⇒ residually finite" is a theorem, so the char-p gap of §7 closes by
dynamics rather than by Kaplansky. For `ℤ²` it fails (§9).

## 9. The families this produces

**Paradox families: finitely generated simple Kazhdan groups with no nontrivial MF quotient** [unreviewed; un-paradox
4253950d2e].
- **Headline:** `boundary-action-elementary-simple-kazhdan-not-mf`. `EL_N(LC(∂F_d,F_q)⋊F_d)/Z` (`d ≥ 2`, `N ≥ 3`) is
  infinite, finitely generated, simple and Kazhdan, with no nontrivial MF quotient. It is Pestov's construction with
  the measure-carrying ℤ-subshift replaced by the paradoxical boundary action.
- **Families:** `paradoxical-steinberg-families-kazhdan-no-mf-quotient`:
  - (F1) boundary actions;
  - (F2) Nekrashevych algebras of finitely generated self-similar actions;
  - (F3) `L_k(1,m)`, the printed case.
- **Non-IBN:** `EL_N(L_k(2,3))`, `N ≥ 3` (§5, Theorem 5).

**Measure families: finitely generated simple Kazhdan LEF groups** [unreviewed; un-measure f0cf0a1353].
- `toeplitz-free-group-elementary-groups-are-lef-kazhdan`. Take `X` a uniquely ergodic Toeplitz `F_r`-subshift over a
  free odometer (Cecchi-Bernales–Cortez–Gómez 2305.09835 [import]). Then `LC(X,F_q)⋊F_r` is finitely generated, simple
  and matricial, and `EL_n` (`n ≥ 3`) is LEF and Kazhdan over a **non-amenable** acting group.
- Simplicity mod centre follows from S4 (REVIEWED) once effectiveness is recorded for these actions.

**Boundary of the tower method** [unreviewed; un-measure 3f486a4805, `matricial-z2-sft-crossed-products-give-quantum-tilings`].
For a free minimal ℤ²-SFT, `LC(Ω,k)⋊ℤ²` is matricial iff finite-dimensional covariant quantum tilings (Q1)–(Q3) exist
at every scale. Quantum-rigid SFTs are never matricial, despite carrying invariant measures. This connects to the
reviewed Theorem Q (`zd-derived-full-group-fp-forces-quantum-rigidity`, ex-verify2-groups part 9, 00e9ab3615).

## 10. Trace and corona invariants

[All unreviewed; un-traces 102def4e00; queued with un-verify-measure.]
- **Kazhdan collapse** (`kazhdan-trace-amenable-iff-qd-iff-fd-limit`). For a countable Kazhdan group, a trace on
  `C*_max` is amenable ⟺ quasidiagonal ⟺ a limit of finite-dimensional traces. The canonical trace qualifies iff the
  group is residually finite. This is essentially Ozawa/Kirchberg (Ozawa survey Thms 6.1, 7.4 [import]).
- **The ring criterion** (`elementary-group-trace-amenable-iff-ring-residually-finite`). For finitely generated `R`
  and `n ≥ 3`, `τ_(EL_n R)` is amenable ⟺ QD ⟺ `R` is residually finite.
  - So the Leavitt and Pestov groups both have non-amenable canonical traces.
  - The candidate "QD trace ⟺ matricial rank function" is **refuted** by the Pestov ring.
- **Corona traces separate the branches** (`corona-traces-separate-paradox-from-measure-for-el-n`).
  - A trace of the form `tr_ω ∘ Φ` with `Φ` into a norm matrix corona is a *corona trace*.
  - Corona trace ⇒ operator MF; LEF ⇒ the canonical trace is a corona trace.
  - Paradox branch: only the trivial corona trace.
  - For subshift rings and `n ≥ 4`: corona trace ⟺ MF ⟺ directly finite.
- **No ucp lift** (`quotientless-lef-kazhdan-corona-trace-has-no-ucp-lift`). For an infinite LEF Kazhdan group
  without finite quotients, the realizing corona map has no ucp lift.
- **Reduced side.** For infinite Kazhdan groups the trace on `C*_r` is never amenable and `C*_r` is never QD. On the
  measure branch, `C*_r` being MF is [OPEN] (`directly-finite-subshift-el-n-reduced-cstar-is-mf`). On the paradox
  branch it is not MF [printed l.1038].

## 11. Examples and calibration refutations

[Table from un-calibration 8d27ba78e6, un-converse, un-paradox and un-measure. Entry statuses as tagged; "∅MF" means
every homomorphism to an MF group is trivial.]

| ring `R` | f.g. | simple | finiteness | branch | matricial over finite fields | `EL_N(R)` |
|---|---|---|---|---|---|---|
| `L_k(1,2)` (`𝒢_2`) | yes (`k` finite) | yes | not directly finite | paradox, `2θ≤θ` | no | ∅MF for `N≥2` [printed] |
| `LC(X,F_q)⋊ℤ`, minimal subshift | yes | yes | stably finite | measure | yes (towers) | LEF, Kazhdan for `N≥3` [REVIEWED] |
| `LC(∂F_d,F_q)⋊F_d` | yes | yes | purely infinite | paradox | no | ∅MF, simple Kazhdan [unreviewed] |
| Toeplitz `F_r`-subshift ring | yes | yes | stably finite | measure, RF | yes | LEF Kazhdan [unreviewed] |
| `L_k(2,3)` | yes | — | directly finite (Cohn, recalled) | non-IBN | no | ∅MF for `N≥3` [unreviewed] |
| `LC(ℤ_2,F_q)⋊ℤ` odometer | **no** | yes | stably finite | measure | yes | LEF, **no (T)** [unreviewed] |
| Weyl `A_1(ℚ)` | no | yes | stably finite, no f.d. modules | — | yes, in `∏M_p(F_p)` | LEF [unreviewed] |
| `F_q[Γ]`, `Γ` amenable, not LEF | yes | no | stably finite, faithful rank fn | — | no | Kazhdan, **not LEF** [unreviewed] |
| algebraic Toeplitz `J` | yes | no | not directly finite | defect not full | — | not MF (`n≥4`) but has a nontrivial MF quotient |
| Labbé `LC(Ω_U,F_q)⋊ℤ²` | yes | yes | measure | measure | ⟺ quantum tilings | unknown |

**Refutations every statement must respect** [un-calibration, unreviewed].
- **(F1)** "Embeds in `∏_ω M_N(k)` over the base field" is the wrong condition. `A_1(ℚ)` has no characteristic-0
  model but embeds in `∏_ω M_p(F_p)`. The right condition allows varying fields (Theorem C, §6).
- **(F2)** Kazhdan families need finitely generated rings, so expansive actions (subshifts), not odometers.
- **(F3)** A faithful rank function plus stable finiteness does not give LEF (`F_q[Γ]`, not simple).
- **(F4)** "No MF quotient" needs a **full** defect. The Toeplitz algebra has a non-full defect and a nontrivial MF
  quotient.
- **(F6)** [printed Prop l.1072] In positive characteristic, `EL_4(R)` MF ⇒ `R` directly finite.

## 12. The open middle

- **(M1) The low-rank band** [OPEN, `el-n-mf-quotient-below-twice-paradoxical-level-exists`]. Ranks `3 ≤ N < 2p(R)`
  on the paradox branch. First case: `EL_3(L_k(3,4))`. Here transport is silent and towers are dead. A nontrivial
  MF quotient would be a new object: a Kazhdan group with an MF quotient sitting inside `EL_4`, which has none.
  Owner: un-low-rank-band.
- **(M2) Is stable finiteness enough?** [OPEN, `stably-finite-simple-rings-have-mf-elementary-groups`] For simple
  stably finite `R`, is `EL_N(R)` MF, or does it have an MF quotient? A counterexample must be simple and non-matricial.
  Greenfeld's non-simple examples [import] show stable finiteness alone does not make a ring matricial.
- **(M3) The converse of Theorem C** [OPEN, `stably-mf-elementary-groups-force-matricial-rings`]. Does stable MF of
  `EL_N(R)` force a matricial ring, or at least a rank function? Operator-norm models give unitaries, not ring maps.
- **(M4) Measure without towers.** ℤ²-SFTs with invariant measures that are quantum-rigid, and characteristic-p
  "measure ⇒ rank function" [OPEN, `invariant-measure-gives-rank-function-any-field`, Kaplansky-hard]. Candidate new
  objects: Kazhdan simple groups that are sofic or linear-sofic but not LEF. Owners: un-sofic-not-lef, un-labbe-ring.
- **(M5) Does `ι` reflect paradox?** [OPEN, `type-semigroup-reflects-paradox-of-steinberg-algebra`], Kaplansky-hard.
- **(M6) Soficity on the paradox branch.** No MF quotient does not preclude soficity: the non-MF paper builds a
  sofic non-MF group. A simple ring that is not stably finite but has no halvable idempotent would give Kazhdan
  candidates for sofic non-MF simple groups (un-converse O4). Owner: un-hyperlinear-paradox.
- **(M7) Non-almost-unperforated type semigroups** (Boldrini–Prasad `F_∞` actions). The sharp theorem (§5, Theorem 6.4)
  does not apply there. The measure-free ones still fall under Theorem G at rank `2n`, and they are not finitely
  generated.

## 13. Status ledger (node → status)

| node | status |
|---|---|
| `steinberg-elementary-groups-are-simple-mod-centre` (+ S1, S2, S3 nodes) | REVIEWED PASS · 171f0f7525 |
| `steinberg-algebra-simple-iff-minimal-effective` | import, REVIEWED PASS · 171f0f7525 |
| `simple-ring-stably-finite-iff-unit-not-paradoxical` | REVIEWED PASS · 638d4941b5 |
| `kmp-tarski-theorem-preordered-monoids` | import, REVIEWED PASS · 638d4941b5 |
| `stably-infinite-ring-elementary-groups-have-no-mf-quotient` / `paradoxical-ring-el-n-full-mf-radical-from-twice-level` / `full-defect-in-m-by-m-kills-mf-quotients-of-el-2m` | unreviewed (one theorem, canonical pending) |
| `mf-elementary-groups-force-stably-finite-simple-rings` | unreviewed |
| `non-ibn-ring-el-n-full-mf-radical-above-module-rank` | unreviewed |
| `no-invariant-measure-steinberg-elementary-no-mf-quotient` / `measure-free-ample-groupoid-el-n-full-mf-radical` | unreviewed (canonical pending) |
| `unperforated-paradox-makes-steinberg-purely-infinite` | unreviewed |
| `algebraic-tarski-for-steinberg-algebras` | unreviewed |
| `char-zero-steinberg-stably-finite-iff-invariant-measure` / `invariant-measure-gives-rank-function-in-char-zero` | unreviewed |
| `measure-side-stable-finiteness-contains-char-p-kaplansky` | unreviewed |
| `matricial-steinberg-algebras-have-invariant-measures` | unreviewed |
| `exactly-matricial-rings-have-lef-general-linear-groups` | unreviewed |
| `residually-finite-actions-give-matricial-crossed-products` | unreviewed |
| `free-group-crossed-product-matricial-iff-invariant-measure` | unreviewed |
| `matricial-z2-sft-crossed-products-give-quantum-tilings` | unreviewed |
| `boundary-action-elementary-simple-kazhdan-not-mf` | unreviewed |
| `paradoxical-steinberg-families-kazhdan-no-mf-quotient` | unreviewed |
| `toeplitz-free-group-elementary-groups-are-lef-kazhdan` | unreviewed |
| `corona-traces-separate-paradox-from-measure-for-el-n` (+ un-traces family) | unreviewed |
| `weyl-algebra-over-q-is-lef-ring-not-matricial-over-q` / `weyl-algebra-is-exactly-matricial` | unreviewed (overlap) |
| `group-ring-lef-iff-group-lef-iff-elementary-group-lef`, `odometer-crossed-product-elementary-groups-not-kazhdan` | unreviewed |
| `el-n-mf-quotient-below-twice-paradoxical-level-exists`, `stably-finite-simple-rings-have-mf-elementary-groups`, `stably-mf-elementary-groups-force-matricial-rings`, `invariant-measure-gives-rank-function-any-field`, `type-semigroup-reflects-paradox-of-steinberg-algebra`, `directly-finite-subshift-el-n-reduced-cstar-is-mf`, `directly-finite-simple-ring-el-n-trace-is-corona-trace` | OPEN |

## 14. Credits and novelty bound

- **Prior work carried by this theory:**
  - Ershov–Jaikin-Zapirain (property (T));
  - Steinberg and BCFS (simplicity);
  - Clark–Edie-Michell (centre);
  - Rainone–Sims (Tarski for type semigroups, stable finiteness);
  - Kwaśniewski–Meyer–Prasad (Tarski for preordered monoids);
  - ABBL (states to measures);
  - Larki (pure infiniteness);
  - Ara–Goodearl–Pardo and Khanh–Thanh (units, `K_1`);
  - Grigorchuk–Medynets and Ma (LEF full groups);
  - Kerr–Nowak (free-group actions);
  - Ara–Claramunt (rank embeddings);
  - Greenfeld (non-linear-sofic stably finite algebras);
  - Cecchi-Bernales–Cortez–Gómez (Toeplitz subshifts);
  - Ozawa and Kirchberg (traces of Kazhdan groups);
  - Malcev and Elek–Szabó.
- **Bounded novelty** (un-prior-art 538afe1ed4): within the sources read, no prior Kazhdan simple group built from a
  Steinberg algebra, and no prior link from ring paradox or matricial approximation to MF or sofic properties of
  `EL_n`, beyond the non-MF paper. The three headline objects (boundary group, Toeplitz family, free-group equivalence)
  are queued for an ex-novelty check.
