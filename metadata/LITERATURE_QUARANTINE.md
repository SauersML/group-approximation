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
| `QuasidiagonalMF.AmenableNuclearInput` | Lance: `C*_r(G)` is nuclear for amenable `G` | the theorem itself |
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

## The one entry that is not a research programme

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

### The band that is open, exactly

Even the **base case** of that induction — two disjoint pieces for a two-factor
minimal expression — is not yet closed, and it is worth recording how narrow the
gap is, because the shape of the remaining obligation is not the one the
`GreendlingerInduction` docstring guesses at.

Take the regime `|c'| ≤ |c|` of `regime_cases`, where `c = c' ++ q` with
`q <+: t'` and the destroyed block eats `q ++ invRev E` out of the second
rotation (`exists_overlap_of_cancellation`).  `E` is a piece, so `6|E| < |t'|`;
`q` is only a suffix of the first conjugator, and `C'(1/6)` says nothing about
it.  Two disjoint pieces are available at either end of the range:

* if `|t'| < 2|q|`, then `q` itself is more than half of `t'`, and `q` and
  `t.take (|t| − |E|)` are **two disjoint consecutive subwords of `P'`** — the
  second piece lives in the *conjugator* part of the first palindrome, not in
  `B'`, which is why looking only at `B'` misses it;
* if `2(|q| + |E|) < |t'|`, then `t' .drop (|q| + |E|)` survives whole in `B'`,
  is a suffix of `t'` and so a prefix of a rotation of it
  (`prefix_rotate_of_suffix`), and is more than half.

What is left is the band `|t'| − 2|E| ≤ 2|q| ≤ |t'|`, of width `2|E| < |t'|/3`,
in which `q` is a prefix of `t'` longer than `|t'|/3` that is simultaneously a
suffix of the first conjugator.  Neither minimality reaches it: the factor count
is spent on `hcoin`, and the weight is stable there — sliding `q` into the second
conjugator (`mk_palindrome_slide`) *lengthens* the total by `|q|`, and sliding it
out of the first would need `invRev q` to be a suffix of `t`, which nothing
supplies.  Closing that band, or finding the move that empties it, is the
genuine research step; it is what planarity does for the classical proof.
