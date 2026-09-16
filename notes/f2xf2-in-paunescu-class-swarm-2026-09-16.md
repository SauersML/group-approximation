# f2xf2-in-paunescu-class, swarm lane, 2026-09-16

**Target.** `f2xf2-in-paunescu-class`: every p.m.p. action of `Γ = F_2 × F_2` on a standard probability space
is sofic (Păunescu Definition 1.4). The lane was locked as `swarm-f2xf2-in-paunescu-class`.

**Outcome.** A reduction and obstruction. The target is **still open**, and so is its negation.

## Setup

The attack runs through Gohla--Thom's *stability in finite actions* (SFA; arXiv:2403.09582v2, Definition 3.7).
A group has SFA when the limit action of any sofic approximation is weakly contained in the family `F(Γ)` of
finite actions.

Two facts motivate it:

* **Remark 3.16 of Gohla--Thom** names `F_2 × F_2` as a test case. It states that some action of `F_2 × F_2`
  is not weakly contained in finite actions (via MIP* = RE), and that such an action "would be non-sofic if
  F2 × F2 was stable in finite actions". It gives no proof and no free version.
* **Kechris's property MD** (every action ≺ `F(Γ)`) implies SFA. `F_2 × F_2` lacks MD, through
  Fournier-Facio--Willett arXiv:2603.18456v2: Remark 5.23 (not RFD), Definition 5.10 (FD ⇒ RFD) and page 68
  (MD ⇒ FD).

## Results

Full proofs are in `research/artifacts/f2xf2-finite-action-stability-dichotomy-2026-09-16.md`.

1. **Proposition A** (`stable-finite-actions-sofic-actions-weakly-finite`, proved, route
   `stable-finite-actions-sofic-actions-weakly-finite-proof`). If a countably infinite `Γ` has SFA, then every
   Păunescu-sofic standard action of `Γ` is ≺ `F(Γ)`.
   * Lift a Păunescu embedding to sets and permutations.
   * The permutations form a sofic approximation, by trace preservation.
   * A diagonal subsequence gives a sofic approximation whose Loeb limit action reproduces the statistics of a
     dense sequence of sets exactly.
   * Then `a ≺` limit action `≺ F(Γ)`.
2. **Corollary B.** Under SFA, an action `a ⊀ F(Γ)` is nonsofic. For residually finite `Γ`, so is the free
   action `a × Γ̂`.
3. **Input** (`f2xf2-lacks-kechris-property-md`, citation route). `F_2 × F_2` has an action `⊀ F(Γ)`.
4. **Theorem C (dichotomy).**
   * `f2xf2-is-stable-in-finite-actions` gives a free nonsofic action of `F_2 × F_2`. This is route
     `f2xf2-nonsofic-action-from-finite-action-stability` into `f2xf2-admits-nonsofic-action`, and it refutes
     the target.
   * The target gives `f2xf2-not-stable-in-finite-actions` (route
     `f2xf2-finite-action-instability-from-paunescu-class`). That answers Gohla--Thom Question 3.12 with an
     explicit residually finite group (`rf-finite-action-instability-from-f2xf2` into
     `residually-finite-group-not-stable-in-finite-actions`).
   * Alekseev--Thom (arXiv:2512.15494v1, introduction) record Question 3.12 as open. So the target is at
     least as hard as producing a residually finite group that is not SFA.

**Novelty.** Proposition A is folklore-level. Gohla--Thom use it implicitly for Elek--Lippner soficity
(Remark 3.14 and Corollary 3.15), and what is added here is the passage from Păunescu's definition. Theorem C(1) is Gohla--Thom's informal Remark 3.16, now with a
written proof and the free upgrade. I found Theorem C(2), read as an obstruction to the target, stated
nowhere, but it is a direct contrapositive.

## Where each approach dies

* **Proving the target through MD.** MD would give SFA and every action ≺ F. `F_2 × F_2` lacks MD, and the
  known sofic actions are the ones in the weak closure. Dies.
* **Refuting the target through SFA.** Needs `f2xf2-is-stable-in-finite-actions`.
  * Gohla--Thom Theorems 3.9 and 3.11 need an amenable complement or quotient. `F_2 × F_2` gives
    `F_2 ⋊ F_2`, and every normal subgroup with amenable quotient again contains `N_1 × N_2` with
    `1 ≠ N_i ⊲ F_2`.
  * No amalgamation theorem exists for SFA, so `(F_2 × Z) *_{F_2} (F_2 × Z)` gives nothing.
  * The sufficient covering condition, Gohla--Thom Lemma 3.8(iii), fails in its `m = 1` case. That case is
    exactly Ioana's (⋆) from arXiv:1909.00282 Theorem D.
  * General `m` is undecided. Ioana's arXiv:2008.00554 Theorem 1.5 is about the reverse covering direction.
  * Ioana's `σ̃_p` limit actions are the natural test, undecided.
* **Proving `f2xf2-not-stable-in-finite-actions` directly.** It needs a sofic action outside the weak closure
  of finite actions. Every sofic action I could name lies inside it:
  * products of `F_2`-actions and their factors (recalled, not source-checked);
  * compact translation actions (recalled, not source-checked);
  * Bernoulli shifts (Abért--Weiss, as quoted in Gohla--Thom Remark 3.14, checked).

  Gaussian witnesses of non-RFD representations have unknown soficity. Ioana's obstructions are
  Hamming-level and give no statistics. The Koopman heuristic gives neither a construction nor an
  obstruction.
* **Gohla--Thom Theorem 3.13 engine.** It needs a non-residually-finite finite central extension. `F_2 × F_2`
  should be good in Serre's sense, and by Grunewald--Jaikin-Zapirain--Zalesskii its finite extensions are then
  residually finite. This is recalled only. Void.

## Weakest steps

* **Imported non-MD chain.** MIP* = RE ⇒ not RFD (Ozawa, as quoted by Fournier-Facio--Willett), and MD ⇒ FD
  (Kechris, second-hand through Fournier-Facio--Willett page 68, mechanism recalled in artifact §4).
  Gohla--Thom Remark 3.16 gives the same conclusion without proof.
* **Limit-action convention.** Proposition A reads Definition 3.7 with the Loeb limit-action convention
  (artifact §1). The proof is insensitive to the choice of free ultrafilter, because the relevant statistics
  converge as honest limits.

## Literature checked (2026-09-16)

arXiv API metadata was read for all of these. PDFs were read through `pypdf` for Gohla--Thom,
Fournier-Facio--Willett, Alekseev--Thom 2512.15494 and Ioana 2008.00554.

| arXiv id | Authors | Title | What it gave this lane |
| --- | --- | --- | --- |
| 1002.0605 | Păunescu | | Definition 1.4, via `research/artifacts/kun-thom-2608-06222-verified.md` |
| 2608.06222 | Kun--Thom | | via the same artifact |
| 2403.09582v2 | Gohla--Thom | *High-dimensional expansion and soficity of groups* | Definition 3.7, Lemma 3.8, Theorems 3.9 and 3.11, Question 3.12, Remarks 3.14 and 3.16 |
| 2603.18456v2 | Fournier-Facio--Willett | *The Local Lifting Property, Property FD, and stability of approximate representations* | Definitions 5.8, 5.10, A.1; Remarks 5.23 and A.4; page 68 |
| 2512.15494v1 | Alekseev--Thom | *Remarks on approximability and stability for groups* | Corollary C; Question 3.12 still open |
| 2008.00554v2 | Ioana | *On sofic approximations of F2 × F2* | Theorem 1.5, (⋆), proof outline |
| 1909.00282v1 | Ioana | *Stability for product groups and property (τ)* | metadata only, statement via 2008.00554 |
| 2408.00110v1 | Bowen--Chapman--Lubotzky--Vidick | *The Aldous--Lyons Conjecture I: Subgroup Tests* | nothing on sofic actions or `F_2 × F_2` |
| 2608.02025v2 | Fournier-Facio | *A torsion-free non-sofic group* | abstract only; nothing on actions |
| 2604.19174v4 | Ersoy | *On minimal non-sofic and ω-non-sofic groups* | abstract only; nothing on actions |
| 2608.21817v1 | Moravec | *Polynomial permutation stability, soficity, and universal polynomial groups* | abstract only; nothing on actions |
| 2608.05362v1 | Alekseev--Thom | *Centralizers of sofic approximations of Kazhdan groups* | abstract only; Kazhdan groups only |

T. Tao's blog, "On the existence of non-sofic groups" (2026-09-11), is a guest post by A. Thom. It has no
technical content on sofic actions or `F_2 × F_2`.

**Not fetched, so unverified:**

* Kechris, *Weak containment in the space of actions of a free group* (Israel J. Math.);
* Ozawa, *About the QWEP conjecture* (IJM 2004);
* Abért--Weiss;
* Becker--Lubotzky;
* Grunewald--Jaikin-Zapirain--Zalesskii (Duke 2008).

No 2024--2026 source was found that settles the target or states the dichotomy of Theorem C(2).

## Referee (2026-09-16)

**Verdict: landed with fixes.** Both `requires: []` routes survive. No route was downgraded and nothing was
withdrawn. The target `f2xf2-in-paunescu-class` stays open.

**Checked.**

* Proposition A in the artifact (§2), line by line:
  * Lemma 1: the pointwise bound `|1_A − a| ≤ 2(a − a²)` after truncation and thresholding at `1/2`;
  * Lemma 2: `‖P_σ − P_{σ'}‖_2² = 2 d_H(σ, σ')` and asymptotic freeness from `τ(u_g) = 0`;
  * Lemma 3: `τ(1_E u_g 1_{E'} u_g^*) = μ(E ∩ gE')`;
  * Lemma 4: `{k : n_k ≥ m} ∈ ω`, since otherwise `Γ` embeds in one `Sym(n)`;
  * the diagonal choice, the exact Loeb statistics, density, and transitivity of weak containment.
* The two conditional routes and `rf-finite-action-instability-from-f2xf2` are valid implications.
* The citation chain for `f2xf2-lacks-kechris-property-md` holds:
  * FFW Remark 5.23 / Ozawa: RFD of `C*(F_2 × F_2)` gives max = min and hence Connes, which MIP* = RE refutes;
  * FD implies RFD;
  * MD implies FD by the Gaussian mechanism.
* Verbatim quotes of Gohla--Thom Definition 3.7, Lemma 3.8, Theorems 3.9 and 3.11, Question 3.12 and Remark
  3.16 were re-extracted from the arXiv PDFs (2403.09582v2, 2603.18456v2, 2512.15494v1, 2008.00554v2) and match.
* The `m = 1` case of Lemma 3.8(iii) is the negation of Ioana's (⋆). Ioana's Theorem 1.5 is the reverse
  covering direction, as R3 says.
* Duplicates: the `distinct_from` rationales hold against the existing SFA and Păunescu-class nodes.

**Fixed in place.**

1. *False step in Corollary B(2) and claim part 3.* "Γ is countable, so it has countably many finite-index
   subgroups" is false (`⊕_N Z/2`), so `Γ̂` need not be standard. Corrected in the artifact, the claim and
   route step 7: `Γ̂` is metrizable for finitely generated `Γ`, and otherwise the chain completion
   `lim Γ/N_i` with `∩ N_i = 1` is used. Every consumer in the graph uses `F_2 × F_2`, which is unaffected.
2. *Convention mismatch.* Gohla--Thom §3.1 define sofic approximations only for finitely presented groups
   (free-group homomorphisms, metric ultraproduct of measure algebras). A paragraph was added to artifact §1,
   plus a trust-surface note on the claim, checking that the conventions agree for finitely presented `Γ`.
3. *Overclaims softened.*
   * R2 and the Gaussian attempt in `f2xf2-not-stable-in-finite-actions`: soficity of Gaussian witnesses is
     open, not "exactly as open as the target"; a sofic one would prove the claim. The status is "Stalls",
     not "Dies".
   * R6 and the Theorem 3.9/3.11 attempts in `f2xf2-is-stable-in-finite-actions`: these are reductions to a
     normal `Λ ⊇ N_1 × N_2` that is no easier, not a failure at amenability.
   * R4: the restriction to `F_{m−1} × F_k` is an honest action for `σ_p`. Whether that survives the
     augmentation `σ̃_p` and induction to `F_2 × F_2` was not checked, and a caveat now says so.

**Not verified by the referee.** The recalled items in R2 (weak containment for products of `F_2`-actions,
compact actions, Abért--Weiss) remain marked as recalled. The same holds for the unfetched references listed
above.
