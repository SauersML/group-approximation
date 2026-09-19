# Unique Games / affine-orientation ingestion — audit, 2026-08-24

External dossier delivered by the user: an attack on the Unique Games
Conjecture run against the `F_lin`-rich 2-to-1 instances, together with a
linear-pairing "memorizer" obstruction, a conjectured Affine
Orientation-Glue Lemma, and three no-go results.  This file records what
was re-derived, what was corrected, and what was withheld.

## Verdict

The dossier is honest about its own boundary: it does **not** claim UGC.
Every explicit computation in it checks out.  One statement it leaves as an
observation is upgradeable to a theorem, and one framing sentence is not a
mathematical assertion at all.  Details below.

## Re-derived and CONFIRMED

1. **Memorizer identity.**  With `Omega = F_2^k`, `N = 2^k`, `b != 0`,
   `P_b` the partition of `Omega` into `b`-pairs, `C_b = {0,b}`, `r` odd,
   `M = binom(N/2-1, r)`, and

   ```text
   B(X) = X_0 * (1/M) * sum_{A subset P_b\{C_b}, |A|=r} prod_{{u,u+b} in A} X_u X_{u+b},
   ```

   the four assertions `|B| <= 1`, `deg B = 2r+1`, `B|_{D_b} = X_0`,
   `||B||_2^2 = 1/M = Theta(N^{-r})` all hold, and the monomials are the
   `2r+1`-element sets `{0} union (union A)`, pairwise distinct with
   coefficient `1/M`.  Confirmed.

2. **Cross-direction orthogonality (the mod-4 argument).**  A common
   Fourier set minus the forced coordinate `0` is a `2r`-element `S` with
   `S+b = S` and `S+c = S`, hence a union of `<b,c>`-orbits of size 4, so
   `4 | 2r` against `r` odd.  Confirmed, and the *same* argument gives the
   sharper statement the dossier actually needs: no monomial of `B_{c,r}`
   restricts on `D_b` to the singleton quotient character at `C_b` either,
   because that also forces `S + b = S`.  So equation (7) is exact, not
   merely generic.

3. **Gauge identity (10).**  With `(P_pi y)_a = y_{pi(a)}`,
   `F|_pi = F . P_pi`, `(sigma.X)_a = X_{sigma^{-1}(a)}` and
   `F^sigma = F . (sigma^{-1}.)`, one computes
   `(sigma^{-1}.(P_{pi.sigma^{-1}} y))_a = y_{pi(a)}`, hence
   `(F^sigma)|_{pi^sigma} = F|_pi` on the nose.  Confirmed.

4. **Random-assignment floor (11) vs (12).**  A 2-to-1 constraint
   `pi: [K] -> [K/2]` under independent uniform labels is satisfied with
   probability `1/(K/2) = 2/K`, so `OPT >= 2/K` unconditionally, and a
   decoder whose list is the whole `K`-element core also achieves exactly
   `2/K`.  Confirmed: alphabet-sized lists can never produce a soundness
   contradiction.

5. **Orientation half-wall.**  Compositions of permutations are
   permutations, so no network of unique constraints implements the merge
   `a_0, a_1 |-> b`.  Confirmed.  This is the classical shadow of the
   repository's own `perfect-commuting-unique-game-is-classically-satisfiable`
   (path transport of a nonzero answer vector), which the dossier did not
   know about.

## UPGRADED — the dossier understates its own result

The dossier says `P_s = sum_b s_b B_{b,r}` "is not bounded pointwise" and
that saturating it "destroys the clean finite-degree description", leaving
open whether *some* renormalization of the memorizer family refutes the
glue lemma.  That question is decidable in two lines and the answer is no.

Evaluate at the `N` **linear** points `X = chi_t`, `X_u = (-1)^{<t,u>}`.
Then `X_u X_{u+b} = (-1)^{<t,b>}`, every one of the `M` products in `B_{b,r}`
equals `(-1)^{r<t,b>} = (-1)^{<t,b>}` since `r` is odd, and `X_0 = 1`, so

```text
B_{b,r}(chi_t) = (-1)^{<t,b>}.
```

The memorizers are literally the F_2-characters at these `N` points.  Hence
for any `B subset Omega\{0}` and any real coefficients `c_b`, Parseval on
`F_2^k` gives

```text
average_t |sum_{b in B} c_b (-1)^{<t,b>}|^2 = sum_{b in B} c_b^2,
```

so `||sum_{b in B} c_b B_{b,r}||_infty >= (sum_{b in B} c_b^2)^{1/2}`.  With
every `|c_b| >= delta` this is `>= delta*sqrt(|B|)`.  Normalizing to sup
norm 1 therefore drives every quotient dictator coefficient to at most
`|B|^{-1/2}`.

**Consequence:** the entire *linear* span of the pair memorizers is closed
as a source of counterexamples, for every sign pattern and every positive
density of directions — not just for the all-ones pattern.  The dossier's
`tanh` remark is thus not a loose end but the only remaining freedom: any
counterexample must be genuinely nonlinear in the memorizers.  Recorded as
`memorizer-superposition-has-large-sup-norm`.

## Sharpened elsewhere

* `B_{b,r}` is **homogeneous** of degree `2r+1`, so `T_rho B = rho^{2r+1} B`
  exactly.  Noise therefore does not damp the obstruction at all: the
  restricted dictator survives with coefficient `rho^{2r+1}`, a constant
  independent of `k`.  The dossier presents boundedness+noise as jointly
  necessary; in fact **boundedness and noise and low degree together still
  fail** for a single direction.  Only *simultaneity across directions* is
  where boundedness bites.  This is why the kill lands on the naive
  influence-transfer route and not on the glue lemma.
* Coordinate `0` has ambient influence `1/M -> 0` in `B_{b,r}`, so the
  memorizer has **no** large ambient low-degree influence while carrying a
  full restricted dictator.  That is the precise failure of "arrow 1".

## Scope limits recorded, not asserted

* The gauge identity (10) is a statement about a **single** edge's folded
  restriction.  It does not by itself show that randomizing constraints
  across a whole instance is useless — the joint law of which vertices
  share which `sigma` is untouched by the computation.  The node states the
  per-edge scope explicitly.
* The dossier's boxed endpoint asserts that "Cairn supplies plausible
  machinery for the subsequent globalization".  **Cairn is a build system
  for unknown facts — a bookkeeping graph, not a mathematical method.**
  There is no Cairn theorem that converts small local defect into global
  structure.  The globalization step is therefore recorded as an ordinary
  OPEN claim (`triangle-defect-globalizes-to-a-bounded-label-list`), with
  no machinery credited to the tool.

## Routes deliberately WITHHELD

rg:2 semantics are that a route's existence asserts its validity.  The
dossier's central implication — glue lemma ==> the missing endgame — is
explicitly *not proved* there ("if established, would give").  Writing it
as a route would be a restatement dressed as a reduction.  It is recorded
instead as the OPEN claim `glue-lemma-implies-rich-2to1-hardness`, and the
route `rich-2to1-from-glue-lemma-modus-ponens` consumes both the analytic
lemma and that implication.  The missing step stays visible and attackable
rather than hidden inside an asserted arrow.

## Citations checked

* Braverman, Khot, Minzer, *On Rich 2-to-1 Games*, ITCS 2021, LIPIcs 185,
  Art. 27, pp. 27:1--27:20, doi 10.4230/LIPIcs.ITCS.2021.27.  Abstract
  verified: "We propose a variant of the 2-to-1 Games Conjecture that we
  call the Rich 2-to-1 Games Conjecture and show that it is equivalent to
  the Unique Games Conjecture."  This is the only literature import the
  region takes.
* Braverman, Khot, Lifshitz, Minzer, *An invariance principle for the
  multi-slice, with applications*, Advances in Mathematics 480 (2025),
  Art. 110460; arXiv:2110.10725.  Verified.  Its perfect-completeness
  hardness applications are stated **assuming** the Rich 2-to-1 Games
  Conjecture, which is the dossier's point about the richness gap.
* `theoremdb.org` status packet: the page resolves, but it is a
  self-described public workspace whose evidence grade on this record is
  "source only".  **Not cited by any node.**  The facts it was used for
  (UGC open as of 2026-08; 2-to-2 theorem at completeness ~1/2; 2025-2026
  work still conditional on Rich 2-to-1) are carried by the two
  peer-reviewed references above instead.
* A LICS 2026 accepted-papers link was offered for "still uses Rich 2-to-1
  conditionally".  Not independently verified here and not cited.

## Nodes written

Claims: `unique-games-conjecture` (root),
`rich-2to1-games-conjecture`, `rich-2to1-conjecture-is-equivalent-to-ugc`,
`affine-orientation-glue-lemma`, `glue-lemma-implies-rich-2to1-hardness`,
`affine-orientation-triangle-defect-is-small`,
`triangle-defect-globalizes-to-a-bounded-label-list`,
`linear-pairing-memorizer-restricts-to-a-dictator`,
`affine-memorizers-are-cross-direction-orthogonal`,
`memorizer-superposition-has-large-sup-norm`,
`edge-conjugation-of-2to1-constraints-is-pure-gauge`,
`unique-constraints-orient-at-most-half-of-a-fiber`,
`dummy-padding-cannot-beat-the-random-guessing-floor`.

Four recorded-dead routes carry the kills:
`glue-lemma-via-ambient-influence-transfer`,
`glue-lemma-via-parseval-budget-across-directions`,
`rich-2to1-via-edge-conjugation-randomization`,
`rich-2to1-via-local-unique-orientation-gadgets`,
`rich-2to1-via-dummy-label-padding`.
