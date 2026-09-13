# Assessment of the single-paper memorandum

2026-09-13. Editorial judgment and bounded source review. The user supplied
the memorandum in the conversation; its ZIP audit and reported computational
runs are not represented as checks performed in this review.

## Adopt the organizing idea

The canonical MF quotient is the right structural center. Lead with the
simple Kazhdan--LEF existence theorem, prove the ring and group quotient
theorems with their distinct target categories, and then use the fixed
quotient to explain the computational information lost by MF maps.

Promote the fixed-quotient/arbitrary-degree theorem and Proposition E
ahead of grouped NP-completeness. The new ordinary-consequence calculation
sharpens that comparison: the same family has one polynomial MF consequence
language and ordinary consequence languages of every Turing degree.
Even imposing a single genuinely nontrivial relation removes the gap
between these two semantics; recognizing that the relation is nontrivial
can carry the original difficulty.

The kernel is intrinsically LEF but invisible under every MF-target map
of the ambient group. This extension-of-maps distinction should accompany
the exact sequence. No splitting of that sequence is being asserted.
The symmetry between local root extraction for simplicity and propagation
of an invisible root for the radical is a useful proof-level connection.

Keep the finite graph formulas and effective algorithms in the paper;
move long compiler expansions and optimization details to appendices.
Do not add unrelated constructions merely to enlarge the list of results.
The proposed 50--65 pages is an editorial estimate, not a target that
should determine the mathematics or require a wholesale rewrite now.

## Deductions added to Cairn

The [proof note](pestov91-fixed-mf-consequences-and-hidden-degrees-2026-09-13.md)
contains the full deductions, with explicit input theorems and scope:

| Memorandum | Current treatment |
| --- | --- |
| E | Fixed marked quotient, exact endpoint-support formula, and one polynomial algorithm independent of the intercept. The correct interleaved coding is used explicitly. |
| F | Recursive presentability iff computable intercept iff decidable word problem; semideciding either identity or nonidentity suffices. |
| G | Every degree is dense in the marked family; strengthened from continuity to a topological embedding. |
| H | MF, amenable and locally finite radicals coincide for the single-seam examples. |
| Further deduction | Ordinary normal consequence has the full intercept degree; its exact discrepancy from MF consequence is calculated. |

These are deductions from the repository's written input theorems, not
independent verification of the full existence or analytic developments.
The memorandum is credited for E--H. No global novelty or new Lean
verification is claimed. The polynomial procedure is described explicitly;
this change does not claim that the existing differently coded graph CLI
already implements this particular fixed-slope family.

## Corrections to the memorandum's snapshot

1. **Brown's 2001 question is now verified in the original.**
   [arXiv:math/0111286v1](https://arxiv.org/pdf/math/0111286v1), dated
   November 27, 2001, Section 11, Question 7, printed page 33, explicitly
   asks about infinite simple Kazhdan groups in the unitary group of an
   R^omega-embeddable McDuff factor. The original PDF was checked in this
   turn, including the version/date and the question. The memorandum's
   demand for evidence from the early version is appropriate; that evidence
   is now available. Current main already cites it, so do not roll that
   attribution back to the 2003 version. This is the earliest formulation
   checked here, not a claim that all earlier literature was exhausted.
2. **Keep the new rank distinctions.** The
   [three-coordinate result](pestov91-three-coordinate-compression-and-involution-localization-2026-09-13.md)
   gives unrestricted GL rank three and a general-linear return budget
   nk>=3. Unrestricted EL still needs rank four in the established argument.
   No fixed points gives EL_2 and GL_2; no periods one or two gives units.
   Exact full-kernel radical formulas remain restricted to F_2.
3. **The weak-QD issue is already wired.** The existing node
   `mf-to-weak-qd-citation-has-unproved-lifting-step` distinguishes arbitrary
   approximate unitary maps from ucp approximations. The current
   [Dadarlat text](https://arxiv.org/html/2007.12655) was checked at the
   introductory implication, Definitions 3.1 and 3.10, and Proposition 3.19.
   Polar repair gives weak QD implies MF. That argument does not provide
   the converse ucp lifts. Preserve the explicit consistency review; do
   not cite the introductory arrow as a proved automatic lifting theorem.
4. **Existence alone is not the editorial headline.** The
   [Eckhardt preprint](https://arxiv.org/abs/2608.28772) is dated August 28,
   2026 and states a non-MF construction. The paper should explain its
   exact quotient and structural contributions rather than infer priority
   from mutable repository status. This review did not independently
   check the whole Eckhardt proof or the whole literature comparison.

The proposed one-paper architecture is persuasive. Its strongest sharpened
statement is that the same marked MF consequence theory coexists with
arbitrary ordinary computational degree, densely in one explicit family.
The simplicity and operator-norm mechanisms remain the independent proof
junctions requiring full mathematical review.
