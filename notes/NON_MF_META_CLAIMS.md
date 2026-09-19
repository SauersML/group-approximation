# Non-MF manuscript: provenance and open-status claims

Companion to `metadata/NON_MF_PROOF_LEDGER.md`.  Created 2026-08-17 and
re-audited against the 2026-08-20 manuscript.

## What lives here, and why it does not live in the ledger

The proof ledger answers one question about each printed assertion: *is this
inferential step in Lean, and is it the same step?*  Sixteen of its rows could
never answer it, because the sentences they were about are not inferential
steps.  They are of three kinds:

* **historical** — attributions of a theorem to the literature that the
  manuscript uses for scholarship and not in a deduction ("Haagerup and
  Thorbjørnsen later proved `C*_red(F₂)` to be MF");
* **terminology** — imports of a name or a convention from a cited paper
  ("`E` is a group of *Deligne type* in the terminology of BDL");
* **open-status** — the manuscript's own record that something is not settled
  ("an effective modulus would need an effective Kazhdan constant").

Grading such a sentence `MISSING/MISSING` is not false, but it is not
informative either, and sixteen of them inflated the ledger's `MISSING` counts
with rows that no amount of Lean work could ever move.  The right question to
ask of them is different — *is the attribution correct, is the citation key
right, and is the status still current?* — and this file is where it is asked.

**The ledger keeps a one-line tombstone for each ID**, so that a reader
following a cross-reference lands somewhere and nothing vanishes silently.  The
tombstones also keep the ledger's own invariants intact: several of these rows
are the only user of their anchor, and the gate rejects an anchor no step uses.

## How to read a row

`Sentence` records the wording audited when the row was created.  The
machine-enforced current source is `metadata/NON_MF_SENTENCE_CENSUS.tsv`, joined
from the manuscript and `metadata/NON_MF_SENTENCE_MAP.tsv`; a wording change
invalidates its sentence key and must be re-triaged there.  This historical
manifest is therefore not a second manuscript pin.

`Status` is one of `historical`, `terminology`, `open-status`.

`Load-bearing` records whether any *proof* in the manuscript consumes the claim.
Every row here is `no`; a literature input that feeds a deduction stays in the
proof ledger, where the grading standard says it is `MISSING`.  The load-bearing
ones are named in the ledger's findings.  In particular, the paper-level
Shulman amalgam input and the Fournier-Facio--Hull--Osin construction now have
their own explicit `ER.*` and `TF.*` rows.

---

## historical

### INT.12 — amalgamated free products

*Sentence.* "Recent work establishes it for many amalgamated free products
\cite{Schafhauser,Shulman,GKEMP}."

*Keys.* `Schafhauser`, `Shulman`, `GKEMP`.  *Anchor.* `p:intro-history`.
*Load-bearing.* no.  *Recorded.* 2026-08-17.

### INT.13 — the Blackadar–Kirchberg candidate

*Sentence.* "Their natural candidate was $\Cred(F_2)$, which Haagerup and
Thorbj{\o}rnsen later proved to be MF \cite{HT}."

*Keys.* `HT` (with `BK`, `CDE` in the preceding sentence).
*Anchor.* `p:intro-history`.  *Load-bearing.* no.  *Recorded.* 2026-08-17.

### INT.14 — abstract stably finite non-MF algebras from CEP

*Sentence.* "The negative solution of the Connes embedding problem subsequently
implied the existence of abstract stably finite non-MF algebras
\cite{MIPRE,FGH}."

*Keys.* `MIPRE`, `FGH`.  *Anchor.* `p:intro-history`.  *Load-bearing.* no.
*Recorded.* 2026-08-17.

Note that the manuscript's own contribution is stated as the contrast in the
next sentence, "No countable group was known whose reduced or maximal group
$C^*$-algebra fails to be MF", which is a claim about the state of the art and
not about a group.

### INT.15 — the Schatten cases

*Sentence.* "The case $p=2$ was settled by
De~Chiffre--Glebsky--Lubotzky--Thom \cite{DGLT}, the cases $1<p<\infty$ by
Lubotzky--Oppenheim \cite{LuO}, and the case $p=1$ by
Bachner--Dogon--Lubotzky \cite{BDL}."

*Keys.* `DGLT`, `LuO`, `BDL`.  *Anchor.* `p:intro-thom`.  *Load-bearing.* no.
*Recorded.* 2026-08-17.

### INT.16 — the soficity problem, answered elsewhere

*Sentence.* "The first was answered negatively in 2026: a nonsofic group was
constructed in \cite{OAI}, Fournier-Facio then gave a torsion-free example
\cite{FFF}, and Kun--Thom developed further wreath-product examples \cite{KT}."

*Keys.* `OAI`, `FFF`, `KT`.  *Anchor.* `p:intro-nonsofic`.  *Load-bearing.* no.
*Recorded.* 2026-08-17.

*Status caveat.* This row is `historical` but it is the one row here whose text
can go stale on its own: it dates a result to a year and asserts the state of a
neighbouring problem.  The sentence after it — "at the time of writing the
hyperlinear problem is open" — is an open-status claim about somebody else's
problem and should be re-read at every revision.

### INT.23 — Slofstra's precedents

*Sentence.* "Slofstra's hyperlinear-profile construction uses a Clifford group,
a distinguished central involution, a shift, and an HNN doubling map
\cite[Section~2 and Remark~3.3]{SlofstraProfile}."

*Keys.* `SlofstraProfile` (and `SlofstraVidick`, `BDL` nearby).
*Anchor.* `p:intro-slofstra`.  *Load-bearing.* no.  *Recorded.* 2026-08-17.

This is the manuscript's acknowledgement that its four structural ingredients
are not new individually; what is new is the operator-norm conclusion drawn from
them.

### INT.24 — the conjugation representation

*Sentence.* "Bekka and Bekka--Valette study property~\textup{(T)} through the
conjugation representation $\pi\otimes\bar\pi$ on Hilbert--Schmidt space
\cite{BekkaAmenable,BekkaValette}, and Dadarlat uses normalized finite-rank
projections as almost invariant Hilbert--Schmidt vectors in an operator-norm
approximation argument \cite[Lemma~3.18 and Proposition~3.19]{Dadarlat}."

*Keys.* `BekkaAmenable`, `BekkaValette`, `Dadarlat`.
*Anchor.* `p:intro-bekka`.  *Load-bearing.* no.  *Recorded.* 2026-08-17.

### INT.25 — the invisible-subgroup precedent

*Sentence.* "He also considers the elements sent to the identity by every exact
finite-dimensional representation and those sent to the identity by every
approximate representation \cite[Definitions~2.5--2.7]{SlofstraCorrelations};
the two subgroups they form are the exact and the approximate analogues of the
MF residual used below."

*Keys.* `SlofstraCorrelations`, `Fritz`.
*Anchor.* `p:intro-slofstra-quotients`.  *Load-bearing.* no.
*Recorded.* 2026-08-17.

The same attribution is repeated at `def:radical` ("This is the operator-norm
analogue of the invisible subgroups of \cite[Definitions~2.5--2.7]
{SlofstraCorrelations} and of the metric-ultraproduct approximation framework of
\cite{NST}"), which is the sentence the ledger's `RA.*` rows sit beside.

### INT.26 — the rounding and corner procedures

*Sentence.* "Bachner--Dogon--Lubotzky develop the operator-norm rounding,
compression, and polar-correction procedures used in
Section~\ref{sec:conj} \cite[Lemmas~2.2--2.3, Proposition~2.4, and the proof of
Proposition~1.5]{BDL}, and handle a finite normal subgroup by a
character-isotypic corner \cite[proof of Proposition~1.6]{BDL}."

*Keys.* `DGLT`, `BDL`, `GR`, `Gl19`.  *Anchor.* `p:intro-dglt`.
*Load-bearing.* no.  *Recorded.* 2026-08-17.

*Caution.* This is the closest of the sixteen to being load-bearing, and it is
the one to re-check if the attribution list changes: the procedures it names are
re-proved in `Section~\ref{sec:conj}` rather than quoted, and the ledger grades
those proofs on their own (`FN.*`).  The sentence is an attribution of priority,
not an import.

### INT.27 — the group-MF framework

*Sentence.* "The group-MF framework is that of Carri\'on--Dadarlat--Eckhardt,
who also give, through Abels' group, an amenable MF group that is not residually
finite \cite[Section~2.14 and Corollary~2.18]{CDE}."

*Keys.* `CDE`.  *Anchor.* `p:intro-cde`.  *Load-bearing.* no.
*Recorded.* 2026-08-17.

The *definition* CDE supply is load-bearing and is graded in the ledger at
`INT.18` and `PRE.16`, where it is `EXACT`: `IsCDEOperatorMF` is that definition.
What is recorded here is only the attribution and the Abels'-group example.

### BT.25 — the classical presentation

*Sentence.* "The eight relations \eqref{eq:sl3presentation} present
$\SL_3(\mathbb Z)$ \cite[Theorem~2]{CRW}; the corresponding matrices are also
recorded in \cite{CLV}."

*Keys.* `CRW`, `CLV` (and Burger's journal article for property~(T) in the
same remark).
*Anchor.* `rem:classical-base`.  *Load-bearing.* no.  *Recorded.* 2026-08-17.

The manuscript says in the same remark that the proofs given here are
independent of the citation, and the ledger's `BT.*` rows grade that independent
development.

---

## terminology

### INT.19 — the two stronger conventions

*Sentence.* "Two stronger conventions also occur in the literature: in
\cite{GKEMP} the approximating maps must also recover the canonical trace and
the left-regular norm on every group-ring element, and the purely matricial
field (PMF) property of \cite[Definition~1.2]{MdlS} requires
finite-dimensional representations whose group-ring norms converge to the
regular norms."

*Keys.* `GKEMP`, `MdlS`.  *Anchor.* `p:intro-convention`.  *Load-bearing.* no.
*Recorded.* 2026-08-17.

This row exists to keep the convention question visible: the manuscript's
Question 3 ("Does MF imply hyperlinearity?") is explicitly about the CDE
convention, and the print says the implication is built into the definition for
the stronger trace-controlled ones.  Anyone re-reading Question 3 should read
this sentence with it.

### FD.17 — Deligne type

*Sentence.* "The central involution $w$ lies in the kernel of every
homomorphism to a finite group, so $E$ is a group of \emph{Deligne type} in the
terminology of \cite[Definition~1.2]{BDL}.  Such groups were proposed there as
the natural candidate counterexamples for all three remaining approximation
problems, and $E$ is such a counterexample for the operator norm."

*Keys.* `BDL`.  *Anchor.* `p:B-deligne`.  *Load-bearing.* no.
*Recorded.* 2026-08-17.

The mathematical content of the first clause — `w` dies in every homomorphism to
a finite group — is *not* terminology and is not recorded here: it is a theorem
and the ledger grades it (`FD.*`, from `thm:exactfd`).  What is here is the
naming and the attribution of the proposal.

---

## open-status

### TA.05 — no effective modulus

*Sentence.* "This argument is nonquantitative and gives no bound for $\delta$
or $|F_0|$.  An effective modulus would need an effective Kazhdan constant for
the base together with effective versions of the compression estimates."

*Keys.* none.  *Anchor.* `cor:uniform`.  *Load-bearing.* no.
*Recorded.* 2026-08-17.

A ledger row cannot be moved by Lean work here in the way the other rows can:
what is open is a *quantitative strengthening* of a theorem that is already
`EXACT`.  The named obstruction is concrete, though, and if either half ever
lands (an effective Kazhdan constant for the base, effective compression
estimates) this row's status changes and `cor:uniform` gains a new claim.

### LI.05 — the Alekseev–Thom problem is separate

*Sentence.* "Alekseev--Thom ask whether commutants arising in sofic
approximations of Kazhdan groups can be recovered from finite-dimensional
coordinate subalgebras \cite[Open Problem~6.2]{AlekseevThom}; that question is
independent of Theorem~\ref{thm:kazhdan-transport}."

*Keys.* `AlekseevThom`.  *Anchor.* `p:limits-alekseev`.  *Load-bearing.* no.
*Recorded.* 2026-08-17.

The second clause is a claim the manuscript makes about the relation between two
problems.  It is not provable and not disprovable in the ledger's sense, and
recording it as `MISSING` said nothing; recording it here says what it is.  The
adjacent claim that *is* mathematical — that the method needs operator-norm
control, which permutation and Hilbert–Schmidt models do not supply — stays in
the ledger, at `LI.16`.

---

## Provenance of this file

Every sentence above was quoted from the manuscript at commit `36490e17` and
matched against the citation keys in the manuscript's own `thebibliography`.
Nothing here was copied from an earlier draft of the ledger without re-reading
the current text: five of the sixteen ledger rows described sentences that had
been reworded since they were written, and the versions above are the current
ones.

Citation-key correctness is a separate audit and is not re-done here; see the
repository's citation audit for the source-verification of these keys.  Two
recurring traps recorded there apply to this file as well: `ElekSzabo` (the
amenable-extension theorem) and `ElekSzaboHyper` (the simple sofic envelope) are
different papers and are cited for different theorems, and `Gl19` is Glebsky's
weak-soficity extension result, not a soficity permanence theorem.
