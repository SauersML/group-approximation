# W1 design: the GreendlingerGate n ≥ 3 count (2026-08-21)

Coordinator's mathematical design for the critical-path residual, against
the W1 dossier (all file:line references as of today's tree).  Read with
`GroupApproximation/Sofic/GreendlingerCascade.lean` /
`GreendlingerDehnCritical.lean` open.

## 0. Ground rules learned from the three refutations

- `GreendlingerTwoPiece` is false because a face can meet the boundary
  in TWO arcs (the witness's second factor contributes 45+45 of 100,
  neither arc > ½).  Any invariant asking for two >½ single infixes is
  dead.  The true classical grading: one >(1−3λ) arc always; the
  companion arcs are only >(1−4λ) = ⅓ and may be split.
- `LeadingConfinement` is false because a block can overrun the next
  factor's kept region; the conclusion survived via a LATER factor's
  untouched rotation — the needed invariant is positional ("where does
  the block stop"), which is exactly `CascadeLanding`'s shape.
- The witnesses live in the band `|t'| − 2|E| ≤ 2|q| ≤ |t'|`; outside it
  the two-piece form holds (`twoPiece_of_long_overhang`).  Any new
  statement must be checked against BOTH witnesses before formalizing.

## 1. New result: the deepest-match orientation lemma

Setting: minimal expression `(c₁,t₁) :: e'`, reduced head palindrome
`P = c₁ ++ t₁ ++ invRev c₁`, tail word `V = K₂ ++ … ++ Kₙ` (chunk
decomposition, proved), and the head–tail reduction eats `M` from `P`
against `invRev M <+: V` with `|c₁| < |M|` (the CascadeLanding regime).
Then `M = (suffix of t₁ of length μ) ++ invRev c₁` with `μ ≥ 1`, hence

    invRev M = c₁ ++ invRev(t₁-suffix of length μ),

so IN `V`, positions `[0, |c₁|)` are matched against conjugator letters
and positions `[|c₁|, |c₁|+μ)` — the DEEPEST eaten positions — are
matched against RELATOR letters of `t₁`.  Consequently the landing
chunk `K_j` (the one containing position `|c₁|+μ−1`) always has its
deepest eaten letters matched relator-vs-relator.  Proof: immediate
from `M`'s decomposition and contiguity of the eaten prefix.  This is
elementary but load-bearing: it splits the landing intrusion into

    i = i_c + i_t,   i_t > 0 always,

where `i_t` counts `t_j`-relator letters matched against `t₁` and `i_c`
counts those matched against `c₁` (nonzero only when `c₁`'s match
overruns all intermediate chunks into `K_j`'s relator territory).

## 2. The landing dichotomy, case tree

(α) `i_c = 0` (intermediate chunks absorb the whole conjugator).  The
intrusion into `t_j` is a common subword of rotations of `t₁` and
`t_j`.  Either it is a piece — `IsPiece` via `isPiece_of_overlap`
(Overlap:180) — giving `6·i < |t_j|`, the sixth-disjunct of
`CascadeLanding`; or the words coincide (`invRev t₁ = t_j.rotate k`
with the conjugator relation), and the coincidence-collapse lemmas
(Overlap:232/:255, 3F:887) delete two factors, contradicting
minimality.  Case (α) is CLOSED by existing machinery plus the
orientation lemma; only assembly is new.

(β) `i_c > 0`: head-conjugator letters eat into `t_j`'s relator
letters.  Pieces do not bound `i_c`; the proved reroute bounds
(`hug_le_of_minimal_reroute` 3F:594 etc.) give at best a HALF-type
bound, while `CascadeLanding`'s landing disjunct demands a SIXTH.
**This gap is the concentrated refutation risk of the whole lane** —
three prior "one remaining lemma" statements died in adjacent
territory.

## 3. Mandatory first step: adversarial test of case (β)

Before anyone formalizes toward `CascadeLanding`, run a concrete
search for a counterexample IN THE (β) REGIME: three factors, the head
conjugator constructed as `c₁ = (prefix of V) = K₂-whole ++ (c_j-part
of K_j) ++ (t_j-prefix of length i_c)` with `|t_j|/6 < i_c` and all
minimality side-conditions checked mechanically (factor-count
minimality via `conjEval_block_ne_one`-style checks, weight minimality
by enumerating rivals up to the obvious moves).  Small alphabets,
relator lengths ~30–100, scripted; run it on MSI, not locally.  Two
outcomes: a counterexample (CascadeLanding dies as stated, and the fix
is to weaken its landing disjunct to a half-bound plus a
second-disjunct strengthening — re-derive the assembly, which is where
the real work moves); or a survival profile that tells us which
minimality move excludes (β)-deep configurations.

## 4. Candidate closures for (β), in attack order

4a. **Spectator-reduction (my current best candidate, not yet a
proof).**  In (β), `c₁` contains as a prefix the entire surviving
contribution `K₂…K_{j−1}` of the intermediate factors plus a prefix of
`K_j`.  Morally the intermediate factors are swallowed spectators and
the (head, factor j) pair should reduce to the PROVED two-factor
analysis (`greendlinger_of_le_two_factors`, regime dichotomy).  The
obstruction to the naive factor-reordering move: `K₂…K_{j−1}` is the
chunk string, NOT the reduced word of `∏₂^{j−1}` (later factors may
have eaten parts of earlier ones), so stripping it off `c₁` does not
directly produce a lighter rival expression.  The repair should run the
two-factor regime analysis RELATIVE to the fixed spectator string: the
proved reroute bounds (3F:433/:504/:594/:701) are exactly two-factor
moves stated with intervening material; check whether their proofs
already tolerate the spectator string in the conjugator position — if
yes, (β) inherits the two-factor dichotomy: either a >½ arc among
{head palindrome remnant, factor j's remnant} located right of
position `|c₁|` (the `GreendlingerAt` disjunct), or a
coincidence-collapse.  I judge this the most likely true closure.

4b. **Measure change on the Dehn route.**  If (β) resists, switch
target to `PieceOverlapRight` (DehnCritical:590), which never mentions
conjugators: the missing content is transporting `DehnReducible`
across a swap when two DISTINCT relators overlap in a piece.  Proof
program: induct on the given derivation of the swapped word; steps
disjoint from the `γ/invRev v₂` window commute (context-freeness,
proved); steps overlapping the window are constrained by two piece
bounds (their redex meets both `r₁`- and `r₂`-material, so at least
`½ − ⅙ − ⅙ = ⅙` of the redex lies in `A` or `B`), forcing a nested
critical-pair analysis with the SAME shape one level down — so define
the induction on (derivation length, window size) lexicographically.
This is mechanical-heavy but conjugator-free; its risk is a genuinely
new nested case, not a false statement.

4c. If both stall: the max-conjugator frame needs its junction-reading
written (labelled Dyck tree `exists_dtree_of_dyck_map` + chunk
decomposition + `conjEval_block_ne_one`), producing the `IsPiece`
premise of `MaximalJunction`, PLUS a new assembly theorem — the most
work, kept as reserve.

## 5. The torsion companion (new leaf, needed by the avatar router)

Free-group C'(1/6) torsion theorem: cyclically reduced symmetrized `R`,
no relator a proper power, metric C'(1/6) ⟹ the quotient is
`IsPowerTorsionFree`.  Classical proof to formalize (after the gate):
if `g^k = 1`, `g ≠ 1`, take `w` cyclically-reduced conjugate
representative of `g`; then `w^k ∈ N` and Greendlinger applies to
`w^k`.  **CORRECTED 2026-08-21 (the first version of this paragraph
pointed at a REFUTED sub-lemma — the fourth documentation error in this
lane's history, machine-checked this time):** "a word sharing more than
half of itself with its own nontrivial rotation is a proper power" is
FALSE — `PeriodicOverlap.not_isProperPower_of_two_mul_length_le` has
the witness `0 1 0 0 1 0 0 1`, which overlaps a rotation of itself in
three quarters of its length and is not a proper power; the sharp true
hypothesis is `|w| ≤ |p| + gcd(k, |w|)`, which a Greendlinger arc never
supplies.  Fine–Wilf is the wrong tool here, not merely unproved.  The
correct route is the TWO-OCCURRENCE DICHOTOMY: the arc exhibits a
common prefix of two rotations of one relator; either the rotations are
distinct — then the prefix is a piece and C'(1/6) bounds it — or they
are equal, and `isProperPower_of_rotate_eq_rotate` fires with no
overlap-length hypothesis at all, which is exactly where the
`NoProperPower` hypothesis is spent.  The consuming statement
(`isPowerTorsionFree_of_metricSmallCancellation`, w1b) carries this
warning in its docstring; `Sofic/PeriodicOverlap.lean` (landed on main)
supplies the dichotomy lemmas, the rotate/invRev closure of
non-proper-powers, and the refutation itself.

SECOND CORRECTION (same evening, fifth error in the lane): even the
dichotomy sketch above was incomplete — in the arc-spans-two-periods
branch with DISTINCT rotations, bounding the overhang piece bounds m,
not |u|, and the resulting length system is satisfiable (machine-
verified, 7592 solutions; window 2n ≤ |r| < 3n).  The full descent is
finewilf's L0–L3 decomposition: |u| ≤ n closes by Dehn descent; equal
rotations close by the proper-power lemma; |r| < 2n closes by the
cyclic-conjugate descent; and the residual window is ARITHMETICALLY
EMPTY when the gate is consumed in sharp form |u| > (1−3λ)|r| at
λ ≤ 1/8 (then n > (1−4λ)|r| ≥ |r|/2).  Consequence for the program:
the avatar family is designed at C'(1/8), the gate file carries a
sharp-form leaf from which the ½-form is derived, and the torsion
theorem is unconditional given the sharp gate — no second van-Kampen
atom exists on this path.

## 6. Division of labor

Coordinator: (3) test design, (4a) relativized two-factor analysis on
paper, review of every candidate statement against §0.  Opus agents:
the §3 search script on MSI; assembly formalization of case (α);
`PieceOverlapRight` induction skeleton (4b) in parallel; Fine–Wilf
sub-lemma of §5 (independent, elementary, can start now).
