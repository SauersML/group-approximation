# stw18-k1-witness-strict-comparison-not-k1-injective — swarm lane, 2026-09-16

Hole worked: `stw18-k1-witness-strict-comparison-not-k1-injective` (OPEN). The
lock was held on the target id. Outcome: an obstruction, meaning a new necessary
condition on any witness together with a firewall with STW Problem XXVIII. No
witness was constructed and none was ruled out. The target stays OPEN.

## Setup

A witness `A` is simple, separable, unital, nuclear and non-elementary. It has
strict comparison against a nonempty trace simplex, and some unitary
`u ∉ U_0(A)` has `[u] = 0` in `K_1`. `stw18-k1-witness-constraints` already
forces:

- `sr(A) ≥ 2`;
- `Γ` not surjective, and not pure;
- not Z-stable and not AH;
- a wild trace simplex.

The open question behind the lane: which divisibility properties can a witness
still have? The folklore that divisibility plus strict comparison is regular
suggests none. This lane checks that against current primary sources.

## External gate (dated sources, read 2026-09-16)

- **Status of the target.**
  - STW, *Nuclear C*-algebras: 99 problems*, arXiv:2506.10902v2 (2026-05-08).
    Problems XVIII and XXIII are still open.
  - arXiv listings to 2026-09-16 show no strict-comparison nuclear algebra that
    fails K1-injectivity or Z-stability.
  - Recent abstracts checked:
    - Toms arXiv:2609.09535v1 (2026-09-08): a simple AH algebra that is not
      K1-injective and fails strict comparison;
    - Robert arXiv:2609.15776v1 (2026-09-14), *Strict comparison and
      selflessness*;
    - Fu arXiv:2512.23911v1 (2025-12-30).

  None constructs a witness.
- **New since the constraint map (2026-09-11).** X. Fu, *Divisibility and Real
  Rank Zero*, arXiv:2605.21655v1 (2026-05-20), an unrefereed preprint. For exact
  algebraically simple algebras, Theorem 1.1 makes these equivalent:
  - tracial `m`-almost divisibility, for some `m`;
  - tracial almost divisibility;
  - Property (TM);
  - tracial approximate oscillation zero;
  - real rank zero of `l^∞(A)/J_A`;
  - hereditary density of `Γ`.

  Corollary 9.2 adds Cuntz-semigroup `m`-almost divisibility as a sufficient
  condition.
- **Other sources re-read in primary form.**
  - Fu–Lin arXiv:2112.14007v4 (2024-01-21), Theorem 1.1: under strict
    comparison, (TM) ⇔ stable rank one ⇔ TAO. No nuclearity or exactness.
  - Lin arXiv:2301.09250v2 (2024-02-20), Theorem 1.1 and Corollaries 1.2–1.3.
  - Winter arXiv:1006.2731v2 (2011-05-20; Invent. Math. 187), from the LaTeX
    source: Definition 3.5 (i)/(ii) and Proposition 3.8.
  - STW v2 LaTeX:
    - Problem XXVIII wording;
    - the folklore paragraph before Problem XXVII;
    - the Haagerup–Kirchberg theorem statement;
    - APRT Theorem D.
- **Not re-read, used only as quoted or as standard inputs.**
  - Haagerup's paper, used via STW's statement.
  - CETW Section 5 and APRT, used only in the novelty audit.
  - Rørdam's lemma, in the same form as the committed direct proof
    `cuntz-sups-with-continuous-rank-converge-uniformly-proof`.

## What was proved

Details are in `research/artifacts/stw18-k1-witness-tracial-divisibility-2026-09-16.md`.

1. **`fu-exact-simple-tracial-regularity-equivalences`** (citation route
   `fu-exact-simple-tracial-regularity-citation`). This is Fu's Theorem 1.1 in
   the exact case, plus Corollary 9.2.
2. **`strict-comparison-property-tm-forces-sr1`** (citation route
   `fu-lin-property-tm-stable-rank-one-citation`). This is Fu–Lin's Theorem 1.1.
3. **`strict-comparison-tracial-divisibility-forces-sr1`** (route
   `strict-comparison-tracial-divisibility-sr1-proof`). Let `A` be unital,
   simple, separable, exact and non-elementary, with `T(A) ≠ ∅` and strict
   comparison on `M_∞(A)` against `T(A)`. Then any of the following forces
   `sr(A) = 1`:
   - (a) Cuntz-semigroup `m`-almost divisibility;
   - (b) Winter's tracial `m`-almost divisibility;
   - (c) the XXVIII divisibility for contractions;
   - (d) any of Fu's eight properties.

   The route contains four matchings:
   - (i) algebraic simplicity, and quasitraces on each `M_n(A)` are traces;
   - (ii) (a), (b) and (c) are reduced to Fu's list;
   - (iii) Fu's (TM) with `e = 1_A` and rescaling gives Fu–Lin's (TM);
   - (iv) Lemma 3.5: strict comparison on `M_∞(A)` against `T(A)` gives
     Fu–Lin's Definition 2.11 for `A⊗K` against `QT~(A) \ {0}`.

   The proof of (iv) cuts `a` into a matrix algebra with Rørdam's lemma. It
   approximates `d_·(b)` from below by the continuous functions
   `τ ↦ τ̄(p_k f_{1/k}(b) p_k)`, then uses compactness of `T(A)`. It needs no
   exactness.

   Item (iv) closes a gap that `stw18-k1-witness-constraints-proof` item 3 left
   implicit when it applied Lin's theorem.
4. **`stw18-k1-witness-not-tracially-almost-divisible`** (route
   `stw18-k1-witness-not-tracially-almost-divisible-proof`). A witness fails
   every one of (a)–(d), uniformly in `m`, because item 2 of the constraints
   says `sr(A) ≥ 2`. In particular it fails the XXVIII hypothesis, so XXVIII and
   the K1-witness lane are decoupled.

## Approaches and where each dies

- **A direct K1 localization.** Idea: combine strict comparison with
  finite-dimensional order zero pieces to localize a null-homotopy of `u ⊕ 1_k`
  to `u` itself. It dies because the stabilization size `k` in `[u] = 0` is
  uncontrolled. Strict comparison moves Cuntz classes, not homotopies, and
  without stable rank one there is no cancellation of `1_k`. This is exactly
  the gap between `sr ≥ 2` and K1-injectivity. No partial result.
- **The density design test (not promoted).** Take `A = closure(∪ A_i)`.
  Suppose the building-block contractions divide tracially inside `A` with a
  uniform constant. Then (b) holds, and so `sr(A) = 1`. So any candidate
  presented as an inductive limit needs, for every `m`, block elements that are
  never tracially divided. The argument transports order zero maps through
  Kirchberg–Rørdam `(b − δ)_+ = dad*` and `her(xx*) ≅ her(x*x)`. That lemma was
  not re-read, so this stays a remark in the artifact, Section 6.
- **Chain T (cross-check only).** Fu's Remark 3.7 identifies his TAO with
  Fu–Lin's T-TAO, and Fu–Lin Theorem 9.4 gives strict comparison plus T-TAO ⇒
  stable rank one. This agrees with the (TM) chain. It was not promoted,
  because the matching rests on Fu's remark rather than on a side-by-side
  reading of the definitions.

## Source anomalies recorded

- **Fu, Definition 8.1 as printed.** It reuses `m` for the matrix size and
  writes `τ(1_n)` for `τ(φ(1_n))`. The nodes use Winter's form, which Fu cites.
- **Fu's attribution to Lin.** Fu's introduction attributes "(6) ⇔ (2)" to Lin
  [29] = arXiv:2301.09250. The v2 text of that paper has no occurrence of
  "order zero", so the attribution was not used.
- **Literal wording of STW Problem XXVIII.** It quantifies over all nonzero
  `a ∈ M_k(A)_+`, not only contractions. Read literally, no unital algebra with
  traces has the property (take `a = 2·1_A`). The committed root
  `stw99-problem-xxviii-tracial-divisibility-gamma` copies that wording. It is
  flagged here and not edited.

## Novelty audit

STW v2 calls it "folklore that in the presence of strict comparison, all these
(and other) divisibility conditions coincide and can be used to define pureness
(see [CETW, Section 5])". The Cuntz-semigroup half of Theorem B also follows
from:

- APRT Theorem D ((m,m')-pure ⇒ pure);
- Lin's Corollary 1.3;
- `stw58-simple-pure-k1-bijective`.

What is new to the graph:

- a dated, hypothesis-matched chain for the order zero tracial forms (b), (c)
  and (d), through a 2026 preprint;
- the proof of the `M_∞`/`T(A)` to `A⊗K`/`QT~` strict comparison matching;
- the XXVIII firewall.

This is a consolidation, not a new theorem about C*-algebras.

## What remains open

- **The target itself.** No candidate is known.
- **Unit divisibility.** Theorem B concerns all contractions of all matrix
  algebras, not the unit. Whether a witness can have a tracially divisible unit,
  that is, unital `Z_{n,n+1} → A` for all `n`, is untouched
  (`strict-comparison-forces-tracially-divisible-unit`, OPEN). A witness with a
  divisible unit but non-divisible matrix contractions would need the
  divisibility of `1_A` not to propagate to hereditary subalgebras. Strict
  comparison alone does not obviously propagate it, because the comparison moves
  Cuntz classes, not order zero maps with trace control.
- **Refereeing Fu.** Fu's preprint (2026-05-20) is unrefereed. Only its theorem
  statements were used, and its proofs were not reconstructed. The exact case of
  (7)⇒(1) is the step a referee of this lane depends on.

## Referee (2026-09-16)

**What was checked.**

- **Every listed file, read in full.** The committed nodes they use were read
  too: the target, `stw18-k1-witness-constraints` and its proof,
  `strict-comparison-rank-surjectivity-forces-sr1` and its citation,
  `stable-rank-one-unital-algebras-are-k1-bijective`, and the XXVIII root. No
  unlisted solver files were found in `git status`.
- **Primary sources, fetched again by the referee on 2026-09-16.**
  - **Fu, arXiv:2605.21655v1** (HTML). The abstract page confirms v1 was
    submitted 2026-05-20. Checked verbatim against the quotes in the nodes:
    - Theorem 1.1, all eight items and the exactness sentence;
    - Definitions 2.6, 3.1, 3.3 and 7.5;
    - Definition 8.1, with the two typographical slips exactly as reported (the
      letter `m` reused for the matrix size, and `τ(1_n)`);
    - Corollary 9.2 and the Cu-divisibility recall before it;
    - Remark 3.7;
    - the introduction sentence attributing "(6) ⇔ (2)" to Lin [29].
  - **Fu–Lin, arXiv:2112.14007v4** (HTML). The abstract page confirms v4 is
    dated 2024-01-21, with journal reference Can. J. Math. 77 (2025) 563–630.
    Checked verbatim:
    - Theorem 1.1, and "stated without assuming that A is nuclear or exact";
    - Definition 2.8, Proposition 2.9 and Definition 2.11, where the inequality
      is quantified over `QT~(A) \ {0}`;
    - Definition 8.1 (TM).

    So the "not independently checked" caveat on the Canad. J. Math. reference
    is now resolved.
  - **STW, arXiv:2506.10902v2** (LaTeX e-print). Problem XXVIII (`Q7b`) does
    quantify over "non-zero a∈M_k(A)_+" with no contraction assumption, so the
    `a = 2·1_A` observation is correct. The folklore paragraph and the
    Haagerup–Kirchberg statement were checked verbatim.
  - **Winter, arXiv:1006.2731v2** (LaTeX e-print). Definition
    `almost-divisible` (i)/(ii) and Proposition `divisible-tracially-divisible`
    were checked verbatim.
- **The mathematics, re-derived step by step.**
  - Algebraic simplicity of unital simple `A`.
  - Finiteness of `τ̄` on `Ped(A⊗K)`, from minimality of the Pedersen ideal.
  - Norm continuity of normalized quasitraces on `M_n(A)`, which lets
    Haagerup–Kirchberg apply, together with the form `σ⊗Tr_n` of tracial
    functionals on `M_n(A)`.
  - The (TM) transfer with `e = 1_A`: same `QT(A)`, same 2-norm, rescaling.
  - Lemma 3.5, step by step:
    - the inequality `f_{1/j}((t − ε/2)_+) ≤ f_{ε/2}(t)`;
    - `y ≲ a` and `c_k ≲ b`;
    - monotonicity of `F_k` and `sup_k F_k = d_τ(b)`;
    - the compactness argument;
    - `τ̄(c_K) ≤ d_τ(c_K)`.

    No gap was found.
  - The form of Rørdam's lemma with a shift `t`. Its short proof is now written
    into the route.
  - The quantifier negation in the concrete form of the witness claim.
- **Duplicates.** `bin/cairn search --similar` on all four new claims found no
  duplicates. The nearest node is Lin's `strict-comparison-rank-surjectivity-forces-sr1`,
  which has a different hypothesis and is already distinguished.

**What was changed.**

- `strict-comparison-tracial-divisibility-sr1-proof`: added the referee's proof
  of (R) with the shift `t`, from `h ≤ k ⇒ h_+ ≲ k`.
- `stw18-k1-witness-not-tracially-almost-divisible-proof`: rewrote the
  "concrete form" negation. The earlier "if the order zero maps are allowed to
  depend on …" was muddled. Also made the firewall precise.
- `stw18-k1-witness-not-tracially-almost-divisible`: softened "no answer to
  XXVIII constrains a witness" to what is proved. A witness never satisfies the
  contraction-form XXVIII hypothesis, so it is never a counterexample, and a
  positive answer says nothing about it.

**Remaining boundaries, stated honestly.**

- The chain rests on Fu's unrefereed 2026 preprint. Its exact-case proof of
  (7)⇒(8)⇒(1) was not reconstructed, and the citation route says so.
- Haagerup's theorem is used as quoted in STW.
- The reading of Fu's Definition 8.1 with the typos corrected is the only
  interpretive step, and it is disclosed.
- The Cuntz-semigroup half (a) was already derivable in the graph (APRT
  Theorem D, `stw58-simple-pure-k1-bijective`). The novelty is consolidation.
  The solver says the same.

**Verdict.** Sound, and honestly labelled. Landed with the small fixes above.
The target `stw18-k1-witness-strict-comparison-not-k1-injective` remains OPEN.
