# Referee memo: dropping condition (iii) from the action-form collapse criterion

Subject: Fournier-Facio's proposed simplification (email, 2026-08-15) of the
working-group criterion ("Theorem 4.1" of the circulated note): replace the
single-mover hypothesis `Gamma = <H, gamma>` by nothing, at the price of an
existential conclusion over a finite set of movers.

**Verdict: the argument is correct as sketched, with one hypothesis to make
explicit (Remark 1), one change of conclusion strength to record (Remark 2
and Section 5), and one bookkeeping simplification available for free in the
ultrafilter formulation (Remark 3).  The modification touches only the
normalization and the word-length estimate; the analytic core is untouched.**

## 0. Evidentiary basis and scope

The circulated note itself ("Caleb's PDF") is not transcribed in this
repository.  This memo verifies the *argument schema*, which is fully
determined by the fragments quoted in the email — the normalization
`k_n = d_n(x_0, gamma x_0)`, the word-length estimate
`delta_n(g) <= C_g k_n`, and the assertion that condition (iii) enters the
proof only through that estimate — cross-checked against (a) the verbatim
Kun–Thom record (`kun-thom-2608-06222-verified.md`; their Theorem 4.1 and
Theorem A are the sofic-side ancestors of this mechanism), and (b) the
kernel-checked compression-form analogues in this repository, whose estimate
layer has the same letter-wise structure.  Section 7 lists the specific
lines of the PDF that must be inspected to confirm the schema matches; every
other step of this memo is independent of that inspection.

## 1. The improved criterion, stated

Let G act on X with basepoint x_0, let Gamma <= G have property (T), let
H = Stab_Gamma(x_0) (see Remark 1), and let the remaining hypotheses (i),
(ii) of the note stand unchanged.  Since Gamma has (T) it is finitely
generated; fix any finite generating set and let gamma_1, ..., gamma_m be
its members outside H, so that Gamma = <H, gamma_1, ..., gamma_m> and
gamma_i x_0 != x_0 for every i.  Conclusion: for every morphism
theta : L -> Q_d (L the finite-order-lamp group over X, Q_d the
operator-norm matrix corona), there exists i <= m with
theta(a_{gamma_i x_0} a_{x_0}) = 1.

## 2. The upper estimate survives (the only place (iii) was used)

Write k_n := max_i d_n(x_0, gamma_i x_0).  The estimate
`delta_n(g) <= C_g k_n` is a triangle inequality over the letters of a word
for `g` in the alphabet H ∪ {gamma_1^{±1}, ..., gamma_m^{±1}}:

- an H-letter contributes only the almost-equivariance error of the model:
  for h in H the wreath relation `h a_{x_0} h^{-1} = a_{h x_0} = a_{x_0}`
  holds *exactly in the group*, so the displacement of an H-letter is not
  merely o(k_n) but is the model error alone, exactly as in the
  single-mover proof — the max-choice changes nothing here;
- a gamma_i-letter contributes `d_n(., gamma_i .) <= k_n + (invariance
  error)` — the single-mover proof used `<= k_n` by fiat (there was one
  mover and k_n was *its* displacement); the max-choice restores the same
  inequality by definition of the maximum.

So `delta_n(g) <= C_g k_n` holds with `C_g` the same word-length constant,
for every g in Gamma.  No other step of the proof reads (iii) (this is the
email's assertion; checkpoint 7.1).

## 3. The lower bound at the top scale survives

In the single-mover proof the normalized displacement mass of the mover is
exactly 1 because k_n is defined as its displacement.  With the max-choice,
the argmax mover gamma_{i*} has `d_n(x_0, gamma_{i*} x_0) = k_n` by
definition, hence normalized mass exactly 1 — the same input, with the same
constant, for the spectral-gap/circumcenter contradiction.  There is no
degradation: the maximum is attained, not approximated.

## 4. The pigeonhole

The argmax function n -> i*(n) takes values in a set of size m.

- Subsequence formulation (the email's): some value i* recurs along an
  infinite subsequence; run every limit along it.
- Ultrafilter formulation (the Q_d-native one): the sets
  {n : i*(n) = i} partition the index set, so exactly one lies in the
  ultrafilter; no subsequence extraction is needed at all (Remark 3).

The bounded-versus-unbounded dichotomy for k_n is likewise run per argmax
value and is unchanged: if k_n is bounded along the chosen
subsequence/ultrafilter set, the original proof's bounded-displacement
branch applies verbatim to gamma_{i*}.

## 5. What the conclusion buys, precisely (the sharpest point)

The dying element depends on the morphism (through the ultrafilter set on
which the argmax stabilizes).  This is harmless for the intended
application and the email's claim, but it does change what is proved, and
the working group should record the distinction:

- **Non-MF-ness: yes.**  Each product `a_{gamma_i x_0} a_{x_0}` is a
  nontrivial element of L (two distinct lamps).  The criterion gives: every
  morphism theta kills *some* element of this fixed finite nontrivial set.
  Hence no morphism is injective, hence L is not MF.  Morphism-dependence
  of the witness costs nothing, because non-injectivity is a per-morphism
  statement and the blocking set is fixed in advance.
- **Radical membership: not delivered.**  Membership of a *specific*
  element in Rad_MF(L) means that *every* morphism kills *that* element.
  The multi-mover conclusion places no single a_{gamma_i x_0} a_{x_0} in
  the radical; it only exhibits a finite blocking set.  The single-mover
  version (iii) did pin the element, hence did give radical membership.
  Two recoveries when radical membership is wanted: (a) a symmetry of the
  pair (G, Gamma, x_0) whose induced automorphisms of L permute the
  candidate elements transitively — then killing one kills all, and each
  lies in the radical; (b) the compression form (Section 6), whose
  conclusion is universal from the start.

So: for "there exists a non-MF group of this shape", Francesco's
simplification is a strict improvement.  For the radical-calculus program,
(iii) — or a compressor — is still doing real work.

## 6. Why the compression form never needed movers

The kernel-checked compression-form endpoint of this repository
(`InvolutionCollapseEndpoint.actualCoronaMFInvisible_commutator`; torsion
orders via `TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness`)
assumes a single element s with `s iota(Gamma) s^{-1} <= iota(Gamma)` and
concludes `ActualCoronaMFInvisible ⁅iota(gamma), k⁆` for EVERY gamma in
Gamma and every corona representation — universal on both counts, i.e.,
genuine radical membership, with no mover or scale bookkeeping anywhere.

The asymmetry is structural.  The compressor supplies uniform transport:
the (T)-primitive is pulled back through s and pushed forward, and one
transport step fixes it for all of Gamma simultaneously — the scale is
carried by s.  The action form has no compressor (that is its virtue: for
Kun–Thom's infranormal pairs only the compression *semigroup* generates,
and G need not contain one global compressor; and in the working-group form
G need not even have (T)), so the scale must be synthesized from the
displacement data of the movers — whence k_n, the max, and the argmax.
One slogan: *a compressor buys universality; movers buy only existence.*
The sofic-side setup already formalized here anticipates the multi-mover
shape: `CompressionSetup.compressors` is a Finset with a joint-generation
field, not a single element.

Consequently no new Lean module is written for this item: the finite-family
corona statement is vacuous on our side (the universal endpoint already
kills every witness commutator individually), and a faithful formalization
of the action form is exactly a formalization of the rank-cocycle analytic
core, which this repository deliberately holds behind the assembly gate of
`TorsionCompressionCollapse` — a separate project, not an estimate-layer
patch.

## 7. Checklist against the circulated PDF

1. Confirm by inspection that `Gamma = <H, gamma>` is read only in the
   proof of the estimate `delta_n(g) <= C_g k_n` (the email asserts this).
2. Confirm H enters conditions (i)/(ii) only through `H <= Stab(x_0)`-type
   monotone conditions, so that enlarging H to the full stabilizer
   (Remark 1) is harmless; in particular no finiteness or (T) hypothesis
   on H.
3. Confirm the normalization k_n is used only through the two properties
   verified in Sections 2–3 (upper bound for all letters, mass exactly 1
   at the normalizing mover).
4. If the note's proof extracts subsequences elsewhere, confirm those
   extractions commute with fixing the argmax value first (they do if they
   are all along the same ultrafilter; Remark 3).

## Remarks

**Remark 1 (H must absorb the fixers).**  The step "choose the generators
so that gamma_i x_0 are all distinct from x_0" discards generators fixing
x_0, which is legitimate only if they land in H.  So take
H = Stab_Gamma(x_0) — without loss by checkpoint 7.2, and the wreath
relation makes the H-displacement exactly zero regardless.

**Remark 2 (existential conclusion).**  The conclusion is existential over
a finite, a-priori-fixed set, with the witness depending on the morphism.
Sufficient for non-MF-ness (Section 5); not a radical-membership statement.

**Remark 3 (the ultrafilter is the pigeonhole).**  In the Q_d formulation
the argmax takes finitely many values, so exactly one value is
ultrafilter-large; "pass to a subsequence" can be deleted from the write-up
rather than added to it.

Provenance: verified 2026-08-15 against the email text, the verbatim
Kun–Thom record, and the kernel-checked compression-form declarations named
above.
