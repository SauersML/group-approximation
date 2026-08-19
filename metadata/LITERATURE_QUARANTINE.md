# The literature quarantine

What this repository *advertises* rests on nothing but `propext`,
`Classical.choice` and `Quot.sound`.  What it *contains* is larger: several
modules formalize a printed route by taking the external theorem it cites as a
typed package and proving everything downstream of it.  That is honest
formalization — it is strictly more informative than an opaque citation,
because it says which steps are theorems and which are not — but it creates a
standing hazard: a later lemma can consume such a package, and a later endpoint
can consume that lemma, and the result is a conditional theorem wearing a clean
axiom report.

`literaturePackages` in `scripts/Audit.lean` is the roster of those packages.
Beside it, the audit walks the **statement** of every advertised result —
`headlineTheorems ++ zeroInputEndpoints` — unfolding through the type and value
of everything the statement names, and fails if the walk reaches any entry.

## Why the walk is over the statement and not the proof

Because reaching a package *from a proof term is not a defect*.  A closed
theorem whose proof mentions one must have built one, and the kernel has
already checked the conclusion; if that ever happens the roster entry is stale,
not the theorem.  Reaching one **from a statement** is the defect: that is a
conditional result wearing a clean axiom report.  The implication is genuinely
proved and it assumes the citation anyway, which is precisely the shape the
kernel cannot see.

## Why this is not `literatureInputNames`

`literatureInputNames` is a roster of *tagged* propositions; the declaration
scan refuses one as a premise **anywhere** in the corpus.  It is empty, and it
must stay empty.  It cannot express what this gate expresses:

* the packages here are not tagged and must not be — tagging them would make
  the modules that take them apart illegal, and those modules are the reason
  the citation surface is as small as it is;
* `zeroInputEndpoints` refuses a leading binder, so it sees
  `DefectRoutingData D → P` and does not see a statement that mentions a
  *named* `Prop` which itself quantifies over one.  The quarantine walk unfolds
  through definitions, so the name buys no cover.

## The roster, and what would retire each entry

An entry is retired **only by proving it**, in the same commit that deletes the
line.  An entry naming a constant that no longer exists fails the run rather
than being skipped, so the roster cannot outlive the problem it records.

| package | the theorem it transcribes | what discharging it needs |
|---|---|---|
| `QuasidiagonalMF.TikuisisWhiteWinterInput` | Tikuisis–White–Winter, *Quasidiagonality of nuclear C\*-algebras*, Ann. of Math. (2) **185** (2017) 229–284 | the theorem itself |
| `QuasidiagonalMF.AmenableNuclearInput` | Lance: `C*_r(G)` is nuclear for amenable `G` | **not the theorem** — `nuclearReducedCPAP_iff_isAmenable` proves amenable ⟺ CPAP already. What is left is CPAP ⟹ `IsNuclearMap`: a positivity check (`k > 0`) and one theorem (complete positivity corestricts to a C\*-subalgebra, by `cfc_mem`) |
| `QuasidiagonalMF.AmenableUCTInput` | Tu: the UCT for `C*_r(G)`, `G` amenable | the theorem itself |
| `QuasidiagonalMF.AmenableMFInput` | the group-level corollary `amenable ⟹ operator-MF` | the three rows above; `Analysis/TikuisisWhiteWinter` proves every step between them and this |
| `CyclicBaseCalibration.AmenableImpliesMF` | the same corollary, at the calibration site | as above |
| `ContainsSquareWitness.UniversalFPTorsionFree` | Fournier-Facio, arXiv:2608.02025 §2: a finitely presented torsion-free property-(T) group universal for finitely presented torsion-free groups | the two rows below; `Sofic/FournierFacioUniversalGroup` proves the step that joins them |
| `FournierFacioUniversal.UniversalKazhdanGroup` | the same theorem, as the conclusion structure the construction consumes | the two rows below |
| `FournierFacioUniversal.UniversalTorsionFreeHost` | Chiodo, arXiv:1107.1489v4, Thm 3.10 (= Belegradek's Thm A.1) | the theorem itself |
| `FournierFacioUniversal.KazhdanEnvelope` | Osin, small cancellation over relatively hyperbolic groups, Thm 2.4.5 | the theorem itself |
| `SmallCancellationEnvelope.HyperbolicKazhdanPartner` | a torsion-free hyperbolic Kazhdan group to run that small cancellation over | an explicit construction |
| `SmallCancellationRouter.GreendlingerGate` | Greendlinger's lemma for `C'(1/6)` | **a self-contained combinatorial theorem; see below** |
| `SmallCancellationRouter.RoutingLemmaData` | the small-cancellation routing datum the gate feeds | the row above |
| `DefectRoutingData`, `OrderPreservingRoutingData`, `FiveConditionRoutingData`, `RelativeCommonQuotientData`, `FournierFacioDefectData` | Hull, Groups Geom. Dyn. **10** (2016) 1077–1119, Thm 1.5, over Osin, Trans. AMS **368** (2016) 851–888 | a suitable subgroup inside the compression defect; see `notes/HULL_ROUTING_AUDIT_2026-08-16.md` |
| `KunThomShulmanDoubleData` | the Kun–Thom/Shulman double construction | the construction |
| `CStarRecognitionConsequences.GroupCStarAdianRabinReductions` | Adian–Rabin | the theorem itself |

## Twenty entries, ten citations, two proofs

The roster is longer than the debt.  Six entries are **derived** — the corpus
already proves them from other entries — and stay listed only because a
statement that names one is conditional all the same:

* `AmenableMFInput` is the universal quantification of
  `isOperatorMF_of_isAmenable_of_tww` over TWW, Lance, Tu and the ucp facts;
  `CliffordAsideInert` proves `AmenableImpliesMF` equivalent to it;
* `UniversalKazhdanGroup` is `ofInputs` of the host and the envelope, and
  `UniversalFPTorsionFree` is read off it;
* in the routing family, `RelativeCommonQuotientData.toDefectRoutingData` and
  `OrderPreservingRoutingData.toFiveConditionRoutingData` are proved, so the
  five names are one obligation.

What is left is **nine** independent inputs.  Eight are other people's
theorems: TWW, Lance, Tu, Chiodo/Belegradek, Osin, a torsion-free hyperbolic
Kazhdan group, Hull, Kun–Thom/Shulman, Adian–Rabin.  The ninth is
`GreendlingerGate`.

There were ten.  **`Quasidiagonal.UCPContractive` was retired on 2026-08-19 by
proof**: `Quasidiagonal.ucpContractive` inhabits it, both clauses are theorems,
and the roster line is gone.  Its story and Greendlinger's share a shape —
each was aimed at a statement that is wrong as written, and neither was an
unproved case waiting on effort.  The difference is that the ucp statement
could be repaired and was; the Greendlinger one is refuted, and a successor has
to restate it cyclically before spending an induction on it.

## `UCPContractive`, discharged — and what it cost to see why it was stuck

`Analysis/QuasidiagonalTrace` recorded this input as dischargeable, missing only
(i) transport of its form-sense complete positivity into
`CStarExactness.IsCompletelyPositive` and (ii) the identification of
`Matrix Y Y ℂ` with `B(ℂᵏ)`.  Step (ii) is bookkeeping.  **Step (i) was
impossible**, which is why the input sat there labelled closable and was not.

`IsCompletelyPositiveOnMatrices` asked only that the *real part* of the form be
nonnegative.  Writing a matrix as `H + iK` with `H, K` Hermitian,
`Re ⟪W, T W⟫ = ⟪W, H W⟫`, so the predicate constrained `H` and said nothing at
all about `K`.  It was strictly weaker than complete positivity, and both
clauses of the input failed over it.  With `N = !![0, 1; -1, 0]` (so `Nᴴ = −N`
and `⟪W, N W⟫` purely imaginary), take `A = ℂ × ℂ`, `Y = Fin 2`, and

```text
    φ (z, w)  =  z • (½ • 1 + N)  +  w • (½ • 1 − N).
```

Linear, unital, and completely positive *in the old sense* — the double sum
collapses to `Re ⟪U, (½ + N) U⟫ + Re ⟪V, (½ − N) V⟫`, each term `½‖·‖²`.  But
`φ (star (z, w)) ≠ (φ (z, w))ᴴ` whenever `z ≠ w`, and `‖φ (1, 0)‖ = √5 / 2 > 1`.

**The fix, applied.**  The predicate now also asks that the form's imaginary
part vanish — which is what complete positivity means and what
Tikuisis–White–Winter supplies, so the input did not outgrow the theorem it
transcribes; the old definition was an accidental weakening.
`IsCompletelyPositiveOnMatrices.form_im` reads the clause off at one element.

**The `⋆` half is now a theorem** (`Quasidiagonal.ucp_map_star`), and it needs
no dilation and no C⋆-theory — not even that `A` is a C⋆-algebra rather than a
`⋆`-algebra over `ℂ`.  Fix entries `r, s` and feed the tuple at the two
`δ`-vectors; the form collapses to four matrix entries, and reality of that
scalar is the whole hypothesis.  Run it at `(0, b)`, `(1, b)` and `(1, i • b)`,
writing `α = φ b r s`, `β = φ (star b) s r`, `γ = φ (b⋆ b) s s`:

```text
    γ.im = 0,     (1 + α + β + γ).im = 0,     (1 + iα − iβ + γ).im = 0,
```

whose second gives `β.im = −α.im` and whose third `β.re = α.re`.  That is
`β = conj α`, entry by entry `φ (star b) = (φ b)ᴴ`.  Putting the `i` on `b`
rather than on `1` keeps `a₁⋆ a₁ = b⋆ b`, so one `γ` serves all three readings.

The structure that carried both facts has lost the proved one and been renamed
`UCPContractive`.  What remains is one inequality — **and that inequality is
proved too, at a different target**:
`CStarExactness.IsCompletelyPositive.norm_apply_le_of_unital`
(`Analysis/CStarUnitalCPContractive`) gets it for a unital completely positive
`φ : A →ₗ[ℂ] (H →L[ℂ] H)` off this repository's own Stinespring dilation.  What
separates the two is the bridge the original note called steps (i) and (ii),
and only that: the form-sense predicate into `IsCompletelyPositive` at the
target `EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y`, and the isometric
`⋆`-algebra identification of `Matrix Y Y ℂ` with that operator algebra — which
is what the scoped `Matrix.Norms.L2Operator` instance *is*, so the norms agree
by definition.  Neither is a citation, and step (i) is now possible where
before it was not.  **This entry is one bridge from leaving the roster
entirely**, and the bridge is short enough to write out.

### The bridge, step by step

Everything it needs is already in the tree.

1. **Self-adjointness of the transported block matrix.**  For
   `M : CStarMatrix (Fin n) (Fin n) A` with `M = star N * N`, self-adjointness
   of `M` gives `M i j = star (M j i)`, and then
   `star ((M.map ψ) j i) = ψ (star (M j i)) = ψ (M i j)` — the middle step is
   **`ucp_map_star`**, which is why that half had to be proved first.  So
   `star (M.map ψ) = M.map ψ`.
2. **Nonnegativity of its form.**  `M i j = ∑ k, star (N k i) * N k j`, so the
   form of `M.map ψ` at `v` is `∑ k` of the form at the tuple `a = N k ·`, and
   each summand is the hypothesis `IsCompletelyPositiveOnMatrices` supplies —
   *including* the reality clause, which is what `blockOp` positivity wants and
   what the old predicate could not give.
3. **Factor it.**  `LanceBlockOperator.exists_factor_of_blockOp_form_nonneg`
   takes exactly (1) and (2) and returns `P` with `M.map ψ = star P * P`.  That
   is `CStarExactness.IsCompletelyPositive ψ`, by definition.

   **Steps 1–3 are now `CStarExactness.isCompletelyPositive_of_form`**
   (`Analysis/CStarFormCompletelyPositive`), proved and compiling: a
   `⋆`-preserving linear map into `B(ℂᵏ)` whose sesquilinear sums are
   nonnegative and real is completely positive.  Note the order the corrected
   predicate forced: reality gives `⋆`-preservation (`ucp_map_star`),
   `⋆`-preservation gives self-adjointness of the block matrix, and
   nonnegativity gives the rest.  Nothing is assumed twice.
4. **Read off the bound.**  `IsCompletelyPositive.norm_apply_le_of_unital`
   then gives `‖ψ c‖ ≤ ‖c‖`, and `UCPContractive` follows.

**What is left is step 4 and the transport into it.**  Two frictions, both
mechanical, and neither a theorem about C⋆-algebras:
`isCompletelyPositive_of_form` and `exists_factor_of_blockOp_form_nonneg` are
stated at `EuclideanSpace ℂ (Fin k)`, so an arbitrary `Y : FiniteModel` has to
be moved along `Fintype.equivFin`; and `ψ` is `φ` followed by the identification
of `Matrix Y Y ℂ` with those operators, which is the scoped
`Matrix.Norms.L2Operator` structure and so is isometric by definition rather
than by a lemma.  The entrywise form and the inner-product form agree on the
nose under that identification, since `⟪u, M *ᵥ v⟫ = ∑ₓ ∑_y conj (u x) M x y v y`.

**Step 4 and the transport are done**, in `Analysis/UCPContractiveMatrix`:
`euclideanize` is the composite of `matrixReindexStarAlgEquiv (enum Y)` and
`Matrix.toEuclideanCLM`, `norm_euclideanize` is that it changes no norms
(`norm_matrixReindexStarAlgEquiv` and `Matrix.l2_opNorm_toEuclideanCLM`),
`ucp_norm_le` runs the four steps, and `ucpContractive` inhabits the structure.
**Compiled 2026-08-19; the roster line is gone.**

Two things nearly cost several rounds each, both found by reading rather than
by the compiler, and both worth remembering.  The module's first compile failed
at the *statement*: the operator norm on `Matrix Y Y ℂ` is a **scoped** instance
(`Matrix.Norms.L2Operator`), so `‖M‖` did not synthesize in a module that had
not opened it, and every declaration after the failure reported `sorry` with no
`sorry` in the source — the poisoning pattern in a new disguise.  And a
`set e := Fintype.equivFin Y` abstracts only the occurrences present when it
runs, while every occurrence in that proof arrives later from the rewrites
themselves; the lemma instances would have said `e` and the goal
`Fintype.equivFin Y`, equal definitionally and not syntactically, which is the
only kind `rw` cares about.

## The one citation that is not a research programme

`GreendlingerGate` is Greendlinger's lemma: a nonempty reduced word in the
normal closure of a `C'(1/6)` symmetrized set contains more than half of one of
its relators.  Nothing in Mathlib proves it, and the classical proof runs on
reduced van Kampen diagrams, which the corpus has no vocabulary for.  The
`Sofic/Greendlinger*` modules attack it diagram-free, and the state is sharp:

* `n = 0` — impossible for a nonempty reduced word;
* `n = 1` — `GreendlingerOneRelator`, proved;
* `n = 2` — `GreendlingerRegime.greendlinger_of_isMinimalConjExpr_two`, proved,
  from the two minimalities (fewest factors, then least total conjugator
  length) and `C'(1/6)`;
* `n ≥ 3` — **open**, and `GreendlingerInduction` states exactly what is
  missing: the one-piece conclusion does not survive multiplication by another
  factor, because the surviving relator can be the one the next factor
  destroys.  What does survive is `TwoPieceConclusion` — *two disjoint*
  subwords, each more than half a relator — since a prefix cancellation can
  only reach the first.  `greendlingerConclusion_of_greendlingerTwoPiece`
  proves the strengthened statement suffices, and
  `IsMinimalConjExpr.tail` / `.leadingPair` prove that minimality is hereditary
  in the two ways the induction needs.

### `GreendlingerTwoPiece` is false as stated — do not try to prove it

`GreendlingerInduction` proposes `TwoPieceConclusion` as the strengthening the
three-factor induction runs on, on the grounds that it is "what Greendlinger's
lemma actually proves for a reduced diagram with at least two regions".  It is
not, and the difference is not cosmetic.  The classical conclusion is that each
of two regions meets `∂D` in a part that is **consecutive along `∂Dᵢ`**.
`TwoPieceConclusion` asks for two subwords consecutive along **`w`**.  When the
second region's arc wraps past the basepoint those are different statements,
and the second one fails.

The witness, in the shape `GreendlingerRegime` already produces.  Take
`|t| = |t'| = 100`, an overlap `|E| = 10`, and the regime `|c'| ≤ |c|` with
`c' = []` and `c = q` where `q = t'.take 45`; let `E` be the suffix of `t` with
`invRev E = t'.drop 45 |>.take 10`.  Then

```text
    w  =  q(45)  ++  t.take 90  ++  t'.drop 55 (45)
```

is reduced, spells `q t q⁻¹ · t'`, and its minimal expression has two factors.
Every subword of `w` that is more than half of a relator lies inside
`t.take 90` — `q` and `t'.drop 55` are 45 letters each, both short of the 51
needed, and they are **not adjacent in `w`**.  Two *disjoint* such subwords
would need at least 102 letters inside a block of 90.  So `TwoPieceConclusion`
fails, while the Greendlinger conclusion itself holds through `t.take 90`.

What the second region does satisfy is the cyclic form: on `∂D₂ = t'`, the part
off `∂D` is exactly `invRev E`, so the part on `∂D` is `t'.drop 55 ++ q`,
consecutive as a rotation of `t'` and `90 > 50` letters long.  Any strengthening
that survives the induction has to be stated that way — pieces located as
*cyclic* subwords, or as a pair (suffix-part, prefix-part) — not as
`w = A ++ u₁ ++ B ++ u₂ ++ C`.  Note also that the stem `c'` sits between the
two parts in general, so even the cyclic reading needs the basepoint handled.

### What is proved, and what the two-factor case still owes

`Sofic/GreendlingerTwoPieceRegime.twoPiece_of_long_overhang` closes the branch
where the linear form *is* available: if `|t'| < 2|q|` then `q` is itself more
than half of `t'`, and `q` and `t.take (|t| − |E|)` are two disjoint consecutive
subwords **of `P'`** — both pieces in the first palindrome, which is why looking
for the second one in `B'` makes the case look harder than it is.  The mirror
branch `2(|q| + |E|) < |t'|` puts the second piece in `B'`.  Between them lies
the band `|t'| − 2|E| ≤ 2|q| ≤ |t'|`, and the witness above lives in it — so the
band is not an unproved case, it is where the statement is wrong.
