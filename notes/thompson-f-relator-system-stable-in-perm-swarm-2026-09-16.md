# Thompson F relator stability: the weak reading and the flexible variants (swarm, 2026-09-16)

Target: `thompson-f-relator-system-stable-in-permutations` (root, open). Lock held for the session and
released at the end.

## Setup

- `F = <a, b | R_1, R_2>`, with `R_1 = [ab^-1, a^-1ba]` (reduced length 10) and `R_2 = [ab^-1, a^-2ba^2]`
  (length 14). `c = [a,b]` is not in `<<R>>`.
- `d` is the normalized Hamming distance.
- Finite quotients of `F` are abelian (Cannon--Floyd--Parry Theorem 4.3), so exact solutions of `R` in any
  `Sym(t)` are exactly the commuting pairs.
- The root recorded the Arzhantseva--Păunescu Open problem only in its strict form, and noted that the
  "weakly" variant (their Definition 7.1) was not read. This session read it from the TeX source.

## What was established

New claim `thompson-f-weak-and-flexible-stability-are-nonsoficity`, route
`thompson-f-weak-and-flexible-stability-are-nonsoficity-proof` (requires
`thompson-f-sofic-iff-relator-system-unstable`), artifact
`research/artifacts/thompson-f-stability-variants-2026-09-16.md`.

For `F` the following are all equivalent:
- nonsoficity;
- strict stability of `R` (AP Definition 3.2);
- weak stability of `R` (AP Definition 7.1);
- each of Bradford's stable, weakly stable, locally stable and weakly locally stable;
- each of Becker--Lubotzky's `P`-stable, `P`-flexibly stable and `P`-very-flexibly stable;
- a liminf `< 1/2` correction condition on sofic approximations.

The one new tool is the **commutator transfer inequality**. For `A, B` in `Sym(n)` and `A', B'` in
`Sym(t)`, `t >= n`, the commutators `[A,B]` and `[A',B']` differ on at most `2(|E_A| + |E_B|)` points of
`[n]`.
- **Sharpness.** The constant 2 is sharp. Exhaustive check for small `(n,t)` and random trials are in
  `experiments/thompson-f-stability-variants-2026-09-16/`. Explicit case: `n = t = 4`, `A = (2 3)`,
  `B = (0 2)(1 3)`, `A' = id`, `B' = B`, with `[A,B] = (0 1)(2 3)`.
- **Unconditional part.** Nonsoficity, weak stability, Bradford-weak, Bradford-weakly-local and the
  liminf condition are equivalent without importing the Dudko--Medynets-based claim.
- **Where the import is used.** The strict, local and flexible senses use direction `1 => 2` of
  `thompson-f-sofic-iff-relator-system-unstable`.

**Consequences.**
- Both readings of the Open problem are one question.
- If `F` is sofic, weak stability fails for every `epsilon < 1/4`, and flexible corrections of sofic
  approximations have liminf total error `>= 1/2`.
- AP Conjecture 1.2 holds for `G = F`.
- None of the variants is a weaker intermediate target.

**Novelty.** Each implication into nonsoficity is an instance of a known principle for groups that are not
residually finite: AP Theorem 7.2(ii), Bradford Lemma 2.15, and the remark in BL §4.4. The contribution is
the uniform sharp inequality, the constants, and the bookkeeping. No priority is claimed.

This does not decide the root.

## Literature gate (checked 2026-09-16)

- **Arzhantseva--Păunescu, arXiv:1410.2626v2.** TeX source read.
  - The Open problem asks "(weakly) stable".
  - Definition 7.1 defines `delta`-strong solutions (words of length `< 1/delta`) and weak stability. Its
    last sentence says "stable" where "weakly stable" is meant.
  - Theorem 7.2 (i)--(iii); Theorem 1.1; Conjecture 1.2.
  - The numbering was computed from the shared counter, consistent with Bradford's citation of
    "[ArPa] Theorem 7.2 (iii)".
- **Becker--Lubotzky, arXiv:1809.00632** (API "updated" 2019-02-22). TeX source read.
  - Definition 1.1 (challenges, solutions).
  - §4.4 (`d^flex`, `d^veryflex`, flexible solutions, and the remark that a flexibly stable group that is
    not RF is nonsofic).
- **Bradford, arXiv:2211.15249v2** (accepted version, 2024-09-04). TeX source read: Definitions 1.1--1.3,
  Remarks 1.4--1.5, Lemmas 2.14--2.15, Theorem 2.16.
- **No 2024--2026 source reports a resolution** of soficity of `F`, or of permutation stability of its
  relators, among those found:
  - Ersoy, arXiv:2604.19174 (submitted 2026-04-21). The abstract says locally graded non-sofic groups are
    omega-non-sofic; `F` is locally indicable, hence locally graded, so this applies to `F` only if `F`
    is non-sofic. No resolution. (Referee correction: the earlier wording attributed a statement about
    Thompson's groups that the abstract does not make.)
  - Fournier-Facio, arXiv:2608.02025 (submitted 2026-08-03): a torsion-free non-sofic group; `F` is not
    discussed in the abstract.
  - Kun--Thom, arXiv:2608.06222: needs property (T).
  - Prellberg, arXiv:2609.12290 (2026-09-10): a density bound > 3.50074529 for `F`.
- **Unverified.**
  - An article in Münster J. Math. 18 (2025) 27--38 reportedly shows `F` is not uniformly S-stable but is
    flexibly uniformly S-stable. Seen only as a search snippet, and not used.
  - Fournier-Facio--Rangarajan, arXiv:2301.03970 (uniform stability for submultiplicative norms), as
    already recorded on the root.
- **Search tooling.** The web-search budget ran out during this session, and arXiv API queries then
  returned empty feeds. The gate above rests on searches made earlier in the session.

## Approaches considered, and where each dies

- **Explicit `N_3` via Fox-calculus identities.** The goal was to extend the metabelian identity
  `c = (a^2R_1a^-2)(aR_1a^-1)(a^2R_2a^-2)^-1 mod F_2''` one derived level down.
  - It is bookkeeping-heavy and low-leverage. Every `N_l` is bounded by the root's constant `C` if the
    root holds, and a finite `N_3` is already known to exist
    (`thompson-f-bounded-derived-length-pairs-obey-linear-bounds`).
  - Its value decides nothing. Not pursued past setup.
- **Searches over `p`-groups, rooted-tree automorphisms and iterated skew products.** These only raise the
  lower bound on `C` (currently `21/4`). A pair of bounded derived length `l` is capped by `N_l`, so no
  finite family of bounded derived length can refute the root. Not run this session.
- **Class-2 pairs are useless for instability.**
  - Modulo `gamma_3(F_2)`, `R_1 ≡ [ab^-1, b] ≡ [a,b]`, and likewise `R_2 ≡ [a,b]`.
  - For pairs generating a group of nilpotency class at most 2, `R_1(A,B) = R_2(A,B) = [A,B]`. The relator
    defect equals the separation, and the ratio is 1.
  - Checked on 1000 random pairs in the integer Heisenberg group (scratch computation, not kept).
- **IRS criterion for amenable groups (Becker--Lubotzky--Thom).** An amenable group is `P`-stable iff every
  invariant random subgroup is a limit of finite-index ones.
  - For `F`, every finite-index subgroup contains `F'`. So the Dirac IRS at the trivial subgroup is not
    such a limit, and amenability of `F` would make `F` unstable.
  - That is already implied by amenable ⟹ sofic ⟹ (by the new claim) unstable. The criterion needs
    amenability of `F`, which is open, and gives nothing new for the root. Source not re-fetched this
    session.
- **Is weak stability a softer target?** No. Weak stability of `R` is equivalent to nonsoficity
  unconditionally (the new claim), so it is exactly as hard as the root, via the imported claim. The same
  holds for the flexible and local senses. This is the firewall recorded in the new claim.

## Weakest points for a referee

- Direction `1 => 2` of `thompson-f-sofic-iff-relator-system-unstable` is imported. It rests on the
  Dudko--Medynets character classification through `thompson-f-character-simplex` and is marked
  unreviewed. Only the strict, local and flexible items depend on it.
- The conversions in Lemma 3.1 of the artifact: almost-homomorphism to challenge, separating to
  `delta`-strong, and strong solutions for all `delta` to soficity. These are routine but written out.
- Novelty is modest, and the artifact says so.

## Referee (2026-09-16)

**Checked.**
- **Definitions against the TeX sources.** Re-downloaded `arxiv.org/e-print/1410.2626v2`, `1809.00632` and
  `2211.15249v2`.
  - [AP] Definition 3.2 (stable) and Definition 7.1 (delta-strong solutions, words of length `< 1/delta`,
    thresholds `< delta` and `> 1 - delta`, per-coordinate `d_H(p_i, p~_i) < epsilon`) match the artifact.
  - Theorem 1.1, Conjecture 1.2, Theorem 7.2(i)--(iii) and the "(weakly) stable" Open problem are as quoted.
    The numbering was recomputed from the shared per-section counters.
  - [BL] Definition 1.1 and section 4.4 (`d^flex`, `d^veryflex`, flexible solutions, the liminf remark) match.
  - [Br] Definitions 1.1--1.3, Remarks 1.4--1.5, Lemma 2.14, Lemma 2.15 and Theorem 2.16 match. The source's
    `Sym(n)` in Definition 1.3 is a typo for `Sym(k_n)`; the artifact now says so.
- **Mathematics.** Every step of artifact Sections 1--4 was re-derived.
  - Lemma 2.1: each of the four steps is controlled through a bijection of `[n]`, which gives the union bound.
  - The explicit equality case `A = (2 3)`, `B = (0 2)(1 3)` was recomputed: `[A,B] = (0 1)(2 3)`.
  - Lemma 3.1(a)--(c), Lemma 3.2, the choice of `m_k` in (D), and the constants in (C) and (H) check out.
    In (H), `1 - delta' >= 4 epsilon` and `l([a,b]) = 4 < 5 <= 1/delta'`.
  - The relator lengths 10 and 14 were recomputed by free reduction.
  - The vacuous directions in (I) are correct.
  - No hidden hypothesis was found. Finite presentation is used only through the two relators.
- **Script.** Reran `transfer_check.py` under `timeout 600`. The output is byte-identical to `transfer_check.out`.
- **Dependency.** `thompson-f-sofic-iff-relator-system-unstable` is ESTABLISHED (unreviewed) on main. It is
  used only for direction `1 => 2`, as the route's `requires:` says.
- **Duplicates.** `cairn search --similar`, plus lexical searches for "weakly stable", "strong solution" and
  "flexib", found no overlapping claim. The distinct_from ids all exist.
- **Literature spot-check.** arXiv abs pages for 2604.19174, 2608.02025, 2608.06222, 2609.12290 and
  2301.03970 exist with the stated titles and authors. None resolves soficity of `F`.
  - Corrected the Ersoy summary, which overstated the abstract, and the Fournier-Facio date.
  - The web-search budget was exhausted, so Cannon--Floyd--Parry Theorem 4.3 was not re-fetched. The fact
    is classical and is already proved in the repo as Fact 1.1 of
    `research/artifacts/thompson-f-soficity-as-relator-stability-2026-09-12.md`.

**Changed.**
- **Claim.**
  - The Conjecture 1.2 and firewall bullets now say explicitly that reaching item 2 or the root passes
    through the imported direction `1 => 2`.
  - The unconditional scope names the finite-quotient fact and its in-repo source.
- **Route.**
  - Fixed "Without 1" to "Under 1" in the vacuous directions; the old wording inverted the hypothesis.
  - Listed all four of Bradford's definitional implications.
- **Artifact.**
  - Firewall wording now separates what holds with and without (B).
  - Glebsky--Rivera is attributed through the [AP] and [Br] citations.
  - Recorded the [Br] Definition 1.3 typo.

**Verdict.** Sound. The claim is honestly labelled, and its novelty statement ("no priority claimed") is
accurate. The root stays open. Landed with minor fixes.
