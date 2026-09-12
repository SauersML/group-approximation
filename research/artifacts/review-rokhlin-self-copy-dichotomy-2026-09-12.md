# Adversarial review (reviewer-2): the Rokhlin entropy self-copy dichotomy

Reviewer lane `reviewer-2`, 2026-09-12. Requested by `gottschalk-positive-host`
for commit 5a2a793cd and the artifact
`research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md`.
Every statement imported from Seward II was compared with the PDF text
(arXiv:1501.03367v4, ghostscript extraction, MSI
`/projects/standard/hsiehph/sauer354/scratch-gpos/k2.txt`). This includes
the full proof of Theorem 6.7 (text lines 1558-1665). Nothing here is
Lean-verified.

## Verdicts

| Item | Verdict |
|---|---|
| (a) Theorem A, the internal form of Seward Thm 6.7 | PASS |
| (b) Lemma 2.1 corners, Lemma 2.2 matrix units | PASS |
| (c) `h^Rok_sup ∈ {0,∞}` and POS ⟺ INF ⟺ RBS | PASS |
| (d) the host `Γ_U` and the one-host Gottschalk reduction | PASS |
| Remark 2.5 (Thompson's V) | PASS |

## (a) Theorem A — PASS

**Imported statements match the source.**
- Theorem 2.6 (Seward–Tucker-Drob), text line 482: small free factors of any
  free p.m.p. action. Matches (S1) verbatim.
- Corollary 2.5, line 443: countable sub-additivity
  `h(C|Σ) <= h(F_1|Σ) + Σ h(F_n|F_(n-1) ∨ Σ)`. (S2) is the case `C = B(X)`,
  `Σ` trivial, `F_1 = F`, `F_2 = B(X)`, together with the definition of
  relative Rokhlin entropy as an infimum of `H(α|Σ)`. This is a correct
  specialization.
- Theorem 6.6, line 1537: matches (S4).
- Theorem 6.7, line 1558: matches (S8).
- (S3), "Apply Theorem 1.1" in the 6.7 proof: the Krieger finite generator
  theorem, [31] in Seward's bibliography. The artifact cites it as Part I
  Theorem 1.1. Not re-read from Part I.

**Where Seward's proof uses the product `P × G`.** It never does, except to
produce `T`. Reading the whole proof, the hypotheses on `T` enter at exactly
three points.
1. *"Since T ∩ G = {1_Γ}, the G-translates of Q are mutually independent"*
   (text line ~1628). This is the only use of trivial intersection: it makes
   `G ↷ Z` Bernoulli and hence free.
2. *"Since G and T commute, it follows that every set in σ-alg_G(ξ) is
   T-invariant"* (line ~1647). This is the only use of commutation: the
   `k`-piece generator `β` then has `T`-invariant atoms, so recording it on
   the transversal `M` loses nothing (`β ⊆ σ-alg_T(α) ∨ F`).
3. `λ(M) = 1/|T|` in the final estimate, with `|T|` large.

`T` acting freely on the free factor `Y` needs only `T <= Γ`. So the transfer
to a commuting pair `T_n, G` inside an arbitrary `Γ` is verbatim, as the lane
claims.

**The artifact's rewritten proof, checked line by line.**
- **Step 1.** `D_π = {x : x|_T = π}` agrees with Seward's
  `∩_t t·R_(π(t))`, since `t·R_ℓ = {y : y(t) = ℓ}`. `u·D_π = D_(u·π)` holds.
  The translates `gT` are disjoint for distinct `g ∈ G`: `gt = g't'` gives
  `g'^(-1)g ∈ G ∩ T = 1`. Two constant patterns lie in distinct `T`-orbits
  when `|L| >= 2`.
- **Step 2.** A finite group acting freely admits a Borel transversal, and
  `μ(M) = 1/|T|` by invariance.
- **Step 3.** `ξ` is a partition: `x` lies in `C_π` exactly when `x ∈ sM`
  with `π = (s^(-1)x)|_T`, and `s` is unique. The `R_ℓ` formula uses
  `(s^(-1)x)(s^(-1)) = x(1)`, which is correct. Refinement of `Q` checks.
  `W` is ergodic (a factor of a mixing restriction), free (it factors onto
  `Z`) and non-atomic, with finite entropy. So `h^Rok_G(W) <= h^Rok_sup(G)`.
- **Step 4.** `B = ∪_s s·(B ∩ M)` for `T`-invariant `B`, since
  `B ∩ sM = s·(B ∩ M)`.
- **Step 5.** `H(α|F) <= μ(M) log k`, because `M ∈ F` and `α` is trivial off
  `M`. Seward writes `<= λ(M)·H_M(α)`, which amounts to the same bound.
- **Conclusion.** `h^Rok_Γ(L^Γ) = 0` forces `min{log|L|, h_sup(Γ)} = 0`,
  hence `h_sup(Γ) = 0`.

**Novelty.** Seward states "We do not know whether POS implies INF" (text
line 210) and obtains `(∀G POS) ⇒ (∀G INF)` only through `P × G`
(Corollary 7.8 proof). No simple monotonicity of `h_sup` under subgroups
is available to reduce the internal case to his theorem, so the internal
form is a genuine, modest extension. The artifact credits it correctly, as
"an internal form of Seward's Theorem 6.7".

## (b) Corners and matrix units — PASS

In `L = L_(F_2)(1,2)`, with `t_i s_j = δ_ij` and `s_0t_0 + s_1t_1 = 1`:
- **`ι_0` is a homomorphism.**
  `ι_0(a)ι_0(a') = s_0 a t_0 s_0 a' t_0 + s_0 a t_0 s_1 t_1 + s_1 t_1 s_0 a' t_0 + s_1 t_1 s_1 t_1 = s_0 a a' t_0 + s_1 t_1`,
  and `ι_0(1) = 1`. The same computation works for `ι_1`.
- **Injective.** `t_0 ι_0(a) s_0 = a` and `t_1 ι_1(b) s_1 = b`.
- **Commuting.** Both products equal `s_0 a t_0 + s_1 b t_1`. All four cross
  terms vanish by `t_0 s_1 = t_1 s_0 = 0`.
- **Trivial intersection.** `t_0(·)s_0` sends `ι_0(a) ↦ a` and `ι_1(b) ↦ 1`.
  `t_1(·)s_1` sends `ι_0(a) ↦ 1` and `ι_1(b) ↦ b`.
- So `(a,b) ↦ ι_0(a)ι_1(b)` embeds `U × U` in `U`.
- **Lemma 2.2.** `t_v s_w = δ_(v,w)` and `Σ_(|u|=n) s_u t_u = 1` follow by
  induction. The ordering `t_u = t_(u_n)…t_(u_1)` is the right one. The
  unital map `M_(2^n)(F_2) -> L` is injective because the matrix algebra is
  simple and `L != 0`. So `GL_(2^n)(F_2) <= U`.

## (c) The dichotomy and the equivalences — PASS

- **Corollary A1.** `G = ι_0(U) ≅ U`, and `T_n = ι_1(GL_(2^n)(F_2))`
  commutes with `G` and meets it trivially. `h_sup` is an isomorphism
  invariant, so Theorem A gives: `h_sup(U) < ∞` implies `h_sup(U) = 0`.
- **Corollary 7.7**, line 1955, verbatim: (i) `h_sup > 0` ⟺ (ii) some action
  with `0 < h < ∞` ⟺ (iii) some action with `h = ∞`. POS is (ii) or (iii),
  so `positive-rokhlin-entropy-action-gives-positive-supremum` is correct.
- **POS ⇒ INF:** Corollary 7.7 plus A1.
- **INF ⇒ RBS:**
  - finite bases by Theorem 6.6;
  - infinite bases by Theorem 7.6 (line 1900, verbatim), since INF gives (ii)
    and hence POS.
- **RBS ⇒ POS:** the Bernoulli 2-shift.
- **RBS ⇒ Gottschalk and Kaplansky:** Corollary 4.1, line 725, matches the
  quoted text verbatim. The Kaplansky half is "automatic [8, Section I.5]",
  where [8] is Capraro–Lupini (bibliography line 2135).
- **Contrapositive** (Corollary 2.4 of the artifact). A strict automaton, or
  a one-sided inverse in some `K[U]`, gives not-POS, so every free ergodic
  action has Rokhlin entropy 0. This includes infinite-base Bernoulli shifts:
  by Theorem 7.6 their entropy is not `∞`, and not-POS makes it 0. Correct.

## (d) The host `Γ_U` — PASS

- `Γ_U = ⊕_(i∈N)(U_* × Sym_fin(N))` is countably infinite.
- Splitting `N` into evens and odds gives `Γ_U ≅ Γ_U × Γ_U`.
- `Sym(n) <= Sym_fin(N)` for all `n`.
- So A1 and A2 apply. POS(`Γ_U`) makes `Γ_U` surjunctive; `U_* <= Γ_U`
  inherits it (subgroup heredity, standard); and the established tester
  equivalence `gottschalk-surjunctivity-fixed-two-generator-tester` gives
  every group surjunctive.
- The scope sentence is correct: one explicit group replaces Seward's "every
  group" (Corollary 7.8), and no converse from Gottschalk to POS(`Γ_U`) is
  claimed.

**Remark 2.5.** `V_[0] ≅ V`, and `Sym(2^n)` permuting the length-`(n+1)`
cylinders inside `[1]` has disjoint support from `V_[0]`, so the two commute
and meet trivially. PASS.

## Cairn wiring

**No false establishment.** Checked at tip 0bdf9dc7f.
- `leavitt-units-surjunctive-via-positive-rokhlin-entropy` needs the open
  `leavitt-unit-group-has-positive-rokhlin-entropy-action`. That claim's only
  route requires the open root `every-group-has-positive-rokhlin-entropy-action`.
- `gottschalk-via-positive-rokhlin-entropy-host` needs the open
  `tester-host-has-positive-rokhlin-entropy-action`. Its only route also
  requires that root.
- The neighbouring `gottschalk-via-maximal-bernoulli-rokhlin-entropy` needs
  `bernoulli-rokhlin-entropy-maximal-for-every-group`, whose route needs the
  open `bernoulli-rokhlin-entropy-maximal-on-fixed-tester`.
- So `gottschalk-surjunctivity-conjecture` and `leavitt-unit-group-surjunctive`
  stay OPEN. The conditional claims are established only as implications,
  and their titles say so.

**Bookkeeping gaps.** These are not correctness failures.
1. **Duplicate import.** `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`
   was on main at fea2d4762, the parent of 5a2a793cd. It already imports
   Seward's Theorems 6.6 and 7.6, Theorem 6.7 and Corollary 4.1.
   `infinite-rokhlin-supremum-forces-surjunctivity` re-imports 6.6, 7.6 and
   4.1, and neither node names the other in `distinct_from`. Recommended:
   retarget the new consumers at the per-group import, or give each a
   `distinct_from` explaining the split (per-group formulas versus the
   INF ⇒ GOT consequence).
2. **Missing requires.** Theorem A's reduction uses Theorem 6.6 in the
   direction `h^Rok(L^Γ) = 0 ⇒ h_sup(Γ) = 0`. Neither claim required by
   `rokhlin-supremum-dichotomy-with-centralized-self-copies-proof` states
   6.6 as a formula. Add `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`
   to that route's `requires:`. Seward–Tucker-Drob (Thm 2.6), sub-additivity
   (Cor 2.5) and the Krieger generator theorem appear only in artifact prose.
3. **No `distinct_from`.** `positive-rokhlin-entropy-action-gives-positive-supremum`
   carries none; see the overlap in item 1.

**Out of scope, noted.** `strict-automaton-lowers-bernoulli-rokhlin-entropy`
(a5c8d6ce2) is ESTABLISHED on its author's derivation, and no review artifact
covers it. It is a nontrivial claim in the same Gottschalk region and should
get a review.
