---
rg: 2
id: stw99-problem-lxv-jiang-su-embeddings
kind: claim
title: Characterise the unital algebras admitting a Jiang-Su embedding (STW Problem LXV)
root: true
artifacts:
  - research/artifacts/stw99-structural-cu-cluster-2026-08-30.md
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-part2-2026-09-12.md
---

**Problem LXV of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
Characterise the unital (simple) C\*-algebras `B` admitting a unital
embedding `Z ↪ B`.  Verbatim (MSI copy, line 3384): "Characterise those
unital (simple) C∗-algebras B for which there exists an embedding Z ֒→ B."
The surrounding text notes that the Villadsen-type counterexamples of Toms
all contain unital copies of `Z`.

**Statement fidelity (corrected 2026-09-12, lane `ex-toms-winter`).**
- An earlier version of this node gave as "the expected answer (the
  Dadarlat--Toms question)" that `Z` embeds iff `B` has no nonzero
  finite-dimensional representations.
- That guess, Rørdam's question, is false even for simple nuclear `B`.
  Dadarlat--Hirshberg--Toms--Winter (arXiv:0712.2020, read in full on MSI):
  "There is a unital simple nuclear infinite dimensional C∗-algebra (in fact,
  an AH algebra) into which the Jiang-Su algebra does not embed unitally."
  Their limit admits no unital `*`-homomorphism from `Z_{3,4}`.
- The Dadarlat--Toms question, as recorded in STW footnote 137, is narrower:
  whether "Z embeds unitally into the minimal tensor product D^{⊗∞} whenever D
  is unital, separable, and has no characters".
- Necessity of the absence of finite-dimensional representations is clear.
  Dadarlat--Toms's positive results concern infinite tensor powers and unital
  subhomogeneous subalgebras without characters (not re-read here).

## Attempts

* `Z = lim Z_{n,n+1}` with semiprojective dimension-drop blocks, so
  the problem reduces to coherent systems of `(n, n+1)`-divisibility;
  by Thiel--Vilalta the no-finite-dimensional-representation
  hypothesis is (2,ω)-divisibility territory and the Global Glimm
  problem (`stw99-problem-lxxiii-global-glimm`) is exactly the
  nilpotent-element engine that would produce the required
  order-zero divisibility at every scale: a positive Global Glimm
  answer supplies, in any unital `B` without finite-dimensional
  representations, full square-zero elements at all scales — the
  standard route from there to `Z_{n,n+1}`-embeddings is
  Robert--Rordam-style division with the obstruction being only
  COHERENCE across `n` (a `lim¹`-type mismatch that semiprojectivity
  reduces to eventually-constant data).  Recorded: LXXIII is the
  load-bearing half of LXV; the residual coherence step is where any
  counterexample must live (a `B` with all finite divisibilities but
  incompatible ones).
  - **Correction (2026-09-12).** The last sentence is contradicted by DHTW:
    their simple nuclear AH algebra already fails at the finite level
    `Z_{3,4}`, through line-bundle topology over `(S²)^{m(j)}`. So
    counterexamples do not need to live in the coherence step.
* **Toms--Winter link (2026-09-12, lane `ex-toms-winter`).** Let `B` be
  unital, simple, separable and nuclear, with Bauer trace simplex, tracially
  locally finite nuclear dimension and strict comparison. Then a unital `Z`, or
  unital `Z_{n,n+1}` for arbitrarily large `n`, already forces `B ≅ B ⊗ Z`
  (`toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`). The tracial shadow
  of an embedding, tracial divisibility of the unit, is the crux
  `strict-comparison-forces-tracially-divisible-unit`.
