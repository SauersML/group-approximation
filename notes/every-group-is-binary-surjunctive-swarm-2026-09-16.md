# every-group-is-binary-surjunctive: swarm attack, 2026-09-16

Agent: swarm-every-group-is-binary-surjunct. Hole locked: `every-group-is-binary-surjunctive` (the target).

## Setup

For a group `G`, a cellular automaton `tau : {0,1}^G -> {0,1}^G` has finite memory `M` and local rule
`mu : {0,1}^M -> {0,1}`. Target: injective implies surjective, for every group. OPEN in the graph.

Orientation (graph state read on 2026-09-16):

- Linear binary rules: Kaplansky direct finiteness of `F_2[G]` (open in general; DHJ arXiv:1112.1790
  imported for small supports).
- Filters already established: balance for `|M| <= 3`; Sidon memory plus unbalanced rule gives
  non-pre-injective; amenable decoder memory forces surjectivity; passive-fixing injective automata are
  surjective; binary strict pairs need `|M| >= 4` or `|S| >= 4` (census).
- Formalizability lane: one-track binary pairs over bi-orderable groups are affine (the marker involution
  on Z is not formalizable); stable formalizability with ancilla is OPEN.

## What was proven

**Theorem** (new claim `binary-three-address-strict-automata-are-linear`, route
`binary-three-address-strict-automata-linear-proof`, artifact
`research/artifacts/binary-three-address-strict-automata-linear-2026-09-16.md`).

Over every group, let `tau` be an injective, non-surjective binary automaton with at most three memory
elements. Then its minimal memory has three elements, its rule is `x_0 + x_1 + x_2 + epsilon`, and
`<M m_0^-1>` is not sofic. Equivalently `1 + a + b in F_2[G]` has a left inverse but is not a unit.

The route requires only `three-address-binary-injective-rules-are-balanced` (established) and
`sofic-groups-are-surjunctive`.

**Proof ingredients.**
1. **Translation and localization.** Right translation `R_g` is a bijective automaton, and
   `tau = tau' o R_g` with memory `M g^-1`. A memory inside `H` makes `tau` a product of copies of
   `tau_H`. Hence a sofic `<M m^-1>` forces surjectivity.
2. **Seventeen rules.** Balance, the constant test and output complement leave seventeen normalized
   rules on three effective addresses. The hand table uses `S_1 = {i : mu(e_i) = 1}` and
   `S_2 = {j : mu(1 - e_j) = 1}`:
   - majority;
   - parity;
   - six multiplexers;
   - six rules `x_a + x_b (1 + x_c)`;
   - three selector rules `x_s ? AND : OR`.
   `three_address_classify.py` confirms the count.
3. **Lemma T.** Majority: `tau(delta_k) = tau(0)`.
4. **Lemma C.** The twelve rules with `mu(e_r) = mu(1 - e_r)`. Take `U = <m_q m_p^-1>`.
   - If `m_r m_p^-1 in U`, the memory group is cyclic.
   - Otherwise `1_{U m_p}`, or its complement, has constant image.
5. **Lemma F.** Selector rules, with the selector translated to `1`.
   - The flip of `x(1)` is invisible iff `y(a) = y(b)`, `y(a^-1) != y(a^-1 b)` and
     `y(b^-1) != y(b^-1 a)`.
   - As a three-edge system over `F_2`, it is inconsistent only when the equality edge coincides with
     an inequality edge. That forces `a^3 = 1` and `b = a^-1`, a finite memory group.
6. **Duality (Proposition 6.2).** `L` is the algebraic transpose of right multiplication by
   `gamma = m_0 + m_1 + m_2` on `F_2[G]`. So `L` is strict iff `gamma` has a left inverse and is not
   a unit.

**New open hole** `f2-support-three-one-sided-units-are-units`. By the theorem, it is exactly the
three-address case of the target.

**Decomposition route** `binary-surjunctivity-split-by-memory-size` into the target. It requires:
- the established theorem;
- the new hole `f2-support-three-one-sided-units-are-units`;
- a second new hole, `binary-four-plus-memory-automata-are-surjunctive`: injective automata with no
  memory of at most three elements are surjective.

The route exists so the support-three hole is reachable from the root. Before it, check.sh reported
that hole as a disconnected lane top. The four-plus hole holds essentially all the remaining
difficulty. Its Attempts record that it contains Kaplansky's direct finiteness over `F_2` for
supports of at least four elements, since every memory of a linear rule contains its support.

**Outcome for the target.** This is a reduction of the `|M| <= 3` case of
`every-group-is-binary-surjunctive` to support-three direct finiteness over `F_2`. The target itself
stays open: nothing here handles memories with four or more elements.

## Approaches tried and where they die

- **Counterexample search at three addresses.** I first hunted for a non-linear three-address
  candidate over a non-amenable group, since the survivors of balance looked plentiful. The kill
  lemmas above leave none. Any counterexample at `|M| <= 3` is linear. No brute force over infinite
  groups was attempted.
- **Linear remainder.** Parity rules are invisible to every configuration test used here.
  - Constant backgrounds: `L(1) = 1`.
  - Coset backgrounds: `L'(1_H) = 1_H`.
  - Single flips: the image of a flip has weight three.
  - A collision is a nonzero kernel element, possibly of infinite support. That is Kaplansky direct
    finiteness at support three, open in general. DHJ (arXiv:1112.1790, imported node) forces partner
    support at least 12.
  - Where it dies: local blind-flip arguments cannot see a global kernel.
- **Four or more addresses.** I did not extend the lemmas.
  - At size four the graph has `binary-four-address-injective-automata-have-balanced-rules`. I did not
    check its status or use it.
  - The coset test at size four leaves two outside addresses whose coset membership varies with the
    reader, so failure no longer forces a cyclic memory group.
  - The selector flip system becomes non-linear.
  - Where it dies: the case analysis does not close without new ideas, for example flips at two
    sites glued along an involution, as in the balance proof.
- **Finite-group cross-checks.** `finite_group_checks.py` brute-forces injectivity on groups of order
  at most 12 and checks Lemma C and the flip criterion directly on larger groups. It is evidence
  only, since finite groups are surjunctive. Results are in the artifact, Section 7. The first run
  exceeded the 600 s cap under machine load, so the script was split into per-batch runs.
  - Zero failures on all 23 groups of order at most 12 in the script, with full injectivity checks.
    `Z2` is vacuous, since it has no triple of distinct elements.
  - Zero failures on `S4`, `D8` and `Z3 x S3`, where only the Lemma C backgrounds and the flip
    criterion were checked.
  - `A5` did not finish within the cap.

## Literature consulted

All fetched on 2026-09-16. WebSearch was unavailable (budget exhausted), and the arXiv API returned
HTTP 429, so I used arxiv.org pages directly.

- **arXiv search listing** (`query=surjunctivity`, newest first, 25 results).
  - Nothing targets the binary alphabet or three-element memories.
  - The only claimed full proof is arXiv:1912.00541 (Cannizzo, Dec 2019). Its own comment says Lemma
    5.3 has a gap that "likely counts as a fatal flaw".
  - Recent entries seen by title only: arXiv:2606.17757 (Ceccherini-Silberstein, Coornaert, Salo, June
    2026, SFTs); arXiv:2511.06586 (Bowen, Chapman, Nov 2025); arXiv:2507.06987 (Paturi, Kari, July
    2025); arXiv:2503.23435 (Phung, Mar 2025); arXiv:2410.17688 (Ceccherini-Silberstein, Coornaert,
    Phung, Oct 2024); arXiv:2403.05998 (Phung, Mar 2024). Their contents are unverified beyond the
    titles.
- **arXiv:2603.18183v1** (Phung, submitted 18 Mar 2026), "Around Gromov's injectivity lemma and
  applications to post-injunctive groups". Abstract read. It concerns post-injunctive groups and does
  not resolve Gottschalk's conjecture.
- **arXiv:2405.18287v1** (Ceccherini-Silberstein, Coornaert, Phung, 28 May 2024), "Stable finiteness of
  monoid algebras and surjunctivity". Abstract read: surjunctive monoids have stably finite monoid
  algebras.
  - This is the global direction "surjunctivity implies stable finiteness".
  - Proposition 6.2 of the artifact is a support-three, `F_2`, single-automaton version of the
    converse link, proved by plain linear duality.
- **arXiv:1112.1790v4** (Dykema, Heister, Juschenko; v1 8 Dec 2011, v4 28 Aug 2012), "Finitely
  presented groups related to Kaplansky's Direct Finiteness Conjecture". Abstract read. It confirms
  the ranks `(3,n)`, `n <= 11`, and `(5,5)` over `F_2` used in Corollary 6.4 and in the hole's
  Attempts.
  - The equivalence of `(m,n)` and `(n,m)` (their Remark 2.13) is taken from the graph node, not
    re-read.

No reference was used for Lemmas T, C and F. They are proved in full in the artifact.
