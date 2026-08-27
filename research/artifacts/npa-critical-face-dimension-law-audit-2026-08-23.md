# Audit: the NPA critical-face first-order dimension law ("R2") dossier

Date: 2026-08-23.  Subject: a pasted dossier proving `dim V_k = 2k+3` for every
NPA level `k >= 2` at the critical doubly-tilted CHSH point, plus a
"finite-portfolio" corollary about finite moment dictionaries.  A follow-up
message from the same author retracted the closure claim by one lemma; this
audit covers both messages.

## Sources, verified to exist

All three arXiv identifiers resolve and the titles/authors match:

* `arXiv:2607.13762` -- Anton Pakhunov, *No finite level of the NPA hierarchy is
  exact for the doubly-tilted CHSH functional near the critical tilt*
  (15 July 2026, 23pp).
* `arXiv:2607.13774` -- Anton Pakhunov, *A phase transition in the exactness of
  the NPA hierarchy at the critical doubly-tilted CHSH functional* -- a
  companion the dossier never cites.
* `arXiv:2607.14569` -- Anubhav Chaturvedi, *No Finite NPA Level Characterizes
  the Complete Quantum Set in the Simplest Bell Scenario* (16 July 2026).
* `arXiv:2607.14755` -- Flora, Matos, Heightman, Krivachy, Garriga, Acin,
  *Moment Optimization in the Navascues-Pironio-Acin Hierarchy* (16 July 2026).

This is not a fabricated-citation dossier.  The defects are of provenance and of
closure, not of existence.

## What Pakhunov 2607.13762 actually contains

Confirmed against the paper text:

* `V_k = {(y_1, lambda) : P(y_1) = lambda u_k u_k^T, (y_1)_1 = 0}`, Section 4.1,
  exactly as the dossier states.
* Proposition 2.1 ("counting laws"): `|W_k| = 2k^2 + 2k + 1`, class count
  `(5k+2)(k+1)/2`, and linear independence of the `2k^2` columns of `N_k`.
* Theorem 3.7 (kernel law): at `delta* = (1/2, 1/4, 1/2, ..., 1/2)`,
  `ker Gamma_k(y_0(delta*)) = span N_k` exactly, dimension `2k^2`;
  `rank Gamma_k = 2k+1`.  PD verified for `k <= 8`.
* Lemma 5.3(1): the pins are homogeneous, **so `V_k` is a linear space**.
* Remark 4.10 ("the germ picture") is the source of the dossier's Section 4.  An
  exact induction-step analysis (steps 2->3, 3->4, 4->5, `explore_r1_induction.py`)
  shows the old-class rows of the level-`(k+1)` system reduce, modulo the
  level-`k` system, to **exactly two residual conditions** supported on the
  level-`k` "unseen" classes `m_k = 1(01)^(k-1)` of length `2k-1`:

  ```text
  y[(empty,m_k)] - y[((0),m_k)]                                     = -1/2
  y[(empty,m_k)] - y[((1),m_k)] - y[((0),0m')] + y[((1),0m')]       = (4k-3)/2
  ```

  and then: "Since unseen coordinates are free at level `k`, extendability is
  never obstructed -- this is the mechanical content of the *germ stabilization
  law* (each extension cuts exactly two gauge dimensions, higher levels cut
  nothing further ...)".
* Section 3's law numbering is L1 (Thm 3.1), L2 (Thm 3.7), L4 (Thm 3.9) and
  **skips L3**; the germ stabilization law is named only inside Remark 4.10 and
  is not a numbered theorem.

## The disputed quotations

The dossier, and its follow-up more sharply, attribute to Section 9.1 the
sentences "the matching upper bound is open" and that R2 is "the one remaining
structural conjecture of this framework", and attribute to the paper a
constructive lower bound `dim V_k >= 2k+3`.  **Three independent retrievals
found none of this.**

1. A retrieval of Section 9 returned it as "9.1 What remains open ... Three
   questions remain open", with the three items being (i) exact overshoot
   exponents (quoting the certified bounds `a_2 > 1/39`, `a_3 > 1/188`,
   `a_4 > 1/641`), (ii) the convergence rate of `eps_k` (quoting
   `eps_k >= (1024 t_k)^(-1/3)` and the `alpha = beta = 0.999` numerics of
   ref. [1]), (iii) structure away from the critical line `alpha + beta = 2`.
   None concerns `dim V_k`.  The specificity of that return -- three certified
   rational constants and a named numerical comparison -- is not the shape of a
   summariser's invention.
2. A dedicated search for the string `2k+3` over the same document returned
   NO OCCURRENCE.
3. Targeted exact-string probes returned NO for "the matching upper bound is
   open", NO for the token `R2` anywhere including script names, NO for
   "structural conjecture", and NO for any table of `dim V_2..dim V_5`.  The
   only `r1` in the paper is in the script names `verify_r1_induction.py` and
   `explore_r1_induction.py`; there is no `r2` companion.
4. The companion `2607.13774` has none of it either: no `V_k`, no `2k+3`, no
   R-labels, no lower bound.

**Caveat on the strength of this.**  These retrievals are model-summarised
renderings of the HTML, not a grep over the source, and the third probe reported
truncation on its section-9 item.  So this is strong convergent evidence, not a
kernel-grade negative.  Anyone holding the PDF settles it with four greps:
`R2`, `2k+3`, `matching upper bound`, `structural conjecture`.  Until then the
region treats the labelled conjecture and the published lower bound as
**unsourced**.

**Why it matters, independent of who is right.**  The dossier proves (modulo one
lemma) only the upper bound `dim V_k <= 2k+3`.  The equality needs the lower
bound, and the follow-up still discharges that half onto the paper.  If the
paper does not carry it, the honest status is **two open halves, not one** --
and the `7, 9, 11, 13` values quoted for `k = 2..5` are then the dossier's own
computation, consistent with the paper's `k <= 5` structural-check range but not
a published dimension table.

## The mathematical gap, now conceded

Step (7) of the argument needs: *every row of `Phi_(k-1)` has zero coefficient on
the three level-`(k-1)` unseen coordinates* `(empty,m)`, `((0),m)`, `((1),m)`
with `m = r_(2k-3)`.  Section 3 of the dossier proves only that these classes
carry **no triangular pivot**, which is strictly weaker: `m` has degree
`2k-3 <= 2k-2`, the top degree at level `k-1`, so a level-`(k-1)` row may have
its leading term at degree `2k-2` and a nonzero tail on `m`.  The dossier closed
the gap by citing Remark 4.10's "unseen coordinates are free at level `k`",
which the paper asserts from the same `k <= 5` computational analysis.  The
follow-up message concedes exactly this point and withdraws "that closes R2".

The proposed repair, recorded here as the leading attack and not as a proof: the
support words in the `T/D` relation lattice have an endpoint-parity property, and
no product of them can generate the four exceptional alternating classes without
either a trailing `0` or a cancellation that lowers the degree.

Independently, the Section 3 case analysis asserts two branches without
exhibiting the exhaustion -- degree `2k` with `a = 1` and `beta` starting and
ending in `1`, and degree `2k` with `a = 0` ("the only possibilities force one
factor to be residual").  The numerics make these very likely true; they are not
written.

## The supplied verifier does not test the theorem

`verify_r2_newproof.py` checks, for `k = 3..12`: `5k+1` new classes, exactly four
exceptional, a unit-triangular row for each of the rest, restricted pivot rank
`5k-3`, and projections `(2,-2,0)` and `(2,0,-2)` for `A_k, B_k`.  It never
computes `rank Phi_k`, never checks the increment
`rank Phi_k - rank Phi_(k-1) = 5k-1`, never checks `dim ker Phi_k = 2k+3`, and
never tests independence modulo `row Phi_(k-1)` -- i.e. it does not touch the one
genuinely open step.  It is also not runnable as supplied: it imports
`verify_pipeline_laws` and `npa_general` from a sandbox path that was not
included.  A decisive check exists and was not run: build `Phi_k` and compute
`dim ker Phi_k` directly for `k = 6, 7`, beyond the paper's verified range.

## What survives, and is worth keeping

* **The reduction `dim V_k = dim ker Phi_k` is sound.**  Theorem 3.7(1) gives
  `Gamma_k(y_0) N_k = 0`, so `y_0(delta)` lies in `ker Phi_k` with identity
  coordinate `1`; the identity functional is therefore nonzero on `ker Phi_k`, so
  `y_1 = 0` cuts exactly one dimension, which the free `lambda` restores.
  Lemma 5.3(1) supplies the linearity the argument needs.
* **The `A_k` closed form is correct; re-derived here by hand.**  With
  `p = ((0), r_(k-2))`, `q = ((0), r_(k-1))`, `T_p = e_p - e_((empty),r_(k-2))`
  and likewise for `q`, the four cross terms give A-side words
  `00 -> empty`, `(0)`, `(0)`, `empty`, and B-side word
  `rev(r_(k-2)) . r_(k-1) = r_(2k-3)` with no cancellation, the abutting letters
  having opposite parity.  Hence

  ```text
  A_k = 2 y_[(empty, r_(2k-3))] - 2 y_[((0), r_(2k-3))]
  ```

  which is twice Remark 4.10's first residual condition.  So the dossier's
  Section 4 recovers, in closed form for all `k`, what the paper obtained by
  stepping `2->3->4->5` in a script.  That is the ingestion's real increment.
  The `B_k` dressing reproduces the `(empty,m) - ((1),m)` signature of the
  paper's second condition; that signature was checked here, not the full
  six-term identity.
* **The arithmetic is internally consistent.**  `C_k = (5k+2)(k+1)/2` gives
  `C_2 = 18`, `C_3 = 34`, `C_k - C_(k-1) = 5k+1`, and
  `C_k - (2k+3) = (5k^2+3k-4)/2`.  So "nullity `2k+3`", "rank
  `(5k^2+3k-4)/2`" and "rank increment `5k-1`" are one statement three ways, and
  the shell decomposition `5k+1 = (5k-3) + 4` minus two consumed gauge
  dimensions is exactly the `+2` per level.
* **The finite-portfolio theorem is true, and has a shorter proof.**  The
  dossier takes `S = union S_i` and applies Chaturvedi to `S`.  The union is
  unnecessary: each finite `S_i` sits inside the level-`k` dictionary for
  `k = max` word length, so `Q_k` is contained in `Q_(S_i)`, and Chaturvedi's
  `p` in `Q_k \ Q` already lies in every `Q_(S_i)`.  Monotonicity does all the
  work, and the adaptive-decision-tree corollary is the same observation.  The
  follow-up message agrees this is minor.

## Relevance gate for this repository

Finite-level non-exactness says nothing about `Q_c` versus the closure of `Q`.
The level sets decrease to the commuting-operator set, and "no `Q_k` equals the
quantum set" is compatible with `closure(Q) = Q_c` in the `(2,2,2)` scenario.
So neither Pakhunov nor Chaturvedi supplies any separation usable by the
Connes-embedding / hyperlinearity lanes here, and no route in this graph may
consume them as if they did.  That negative is wired as
`finite-npa-nonexactness-does-not-separate-qc` and is the part of this ingestion
with actual downstream value.

The follow-up message's own landscape reading was checked: the three Cairn nodes
it names -- `fanizza-self-referential-game-never-attains-npa-limit`,
`tracial-npa-cannot-separate-canonical-trace`,
`zpc-irs-value-computable-upper-hierarchy`,
`traffic-branching-rounding-hierarchy` -- all exist with the stated content, and
its report that the graph contains no `Pakhunov` / `2607.13762` / `2k+3` material
is correct; a sweep for `Chaturvedi`, `Pakhunov`, `tilted CHSH`, `Motzkin` and
`unseen class` over `research/`, `notes/` and `docs/` returned nothing.  No peer
lane collides with this region.

## Disposition

Wired as a self-contained region.  Target `dim V_k = 2k+3` **open**; the
upper-bound half open behind the unseen-freeness lemma; the lower-bound half
open and flagged unsourced; the shell pivot count open with the case analysis
recorded.  Established: the kernel reduction, the class arithmetic, the
first residual row in closed form, the Chaturvedi import, the finite-portfolio
corollary, and the relevance gate.  Nothing in the region is attached to the
program goal.
