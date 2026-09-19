# STW 99-problems: the commutative & noncommutative dynamics cluster (XXXII--XXXIX)

*2026-08-30 goal session.  Source: arXiv:2506.10902 v2, sections on
classifiability of C\*-algebras from commutative and noncommutative
dynamics (labels q:ZCrossedProd, q:DynComparison,
q:dynamicalcharacteriseZstable, q:TCiso, q:PhillipsToms,
q:ComputeKTheory, q:z-stable-product, q:z-stable-action; extraction
#34, #36--42 with commented #35).*

## Wiring

* **XXXIII ⟹ XXXII, both halves** (`stw99-xxxiii-implies-xxxii`).
  Amenable half: finite-dimensional base gives SBP; comparison + SBP =
  almost finiteness (Kerr--Szabo); Kerr's theorem finishes.
  Non-amenable half: amenable action + invariant measure would force
  amenability of the group, so comparison degenerates to dynamical
  pure infiniteness; Ma + nuclearity + Kirchberg absorption finish.
  So the entire Problem XXXII is equivalent in difficulty to dynamical
  comparison restricted to those two classes.
* **XXXIX ⟹ XXXVIII** (`stw99-xxxix-implies-xxxviii`): cocycle
  conjugacy preserves crossed products and
  `(A⊗Z)⋊_{α⊗1}G ≅ (A⋊G)⊗Z`.
* **XXXV + XX ⟹ Giol--Kerr uniform Γ**
  (`giol-kerr-uniform-gamma-via-tracial-completion`): with Problem XX
  now ESTABLISHED (Vaccaro 2026), a positive tracial-completion
  identification transports uniform Γ from Villadsen algebras to the
  Giol--Kerr crossed products, since uniform Γ is a property of the
  uniform tracial completion (CCEGSTW).  This answers a side question
  STW list as open and would separate absolute uniform Γ from relative
  uniform Γ (= SBP, which FAILS for GK by Lindenstrauss--Weiss).  It
  also gives Problem XXXV a refutation channel: proving GK lacks
  uniform Γ refutes XXXV outright.

## Post-Toms recalibration of STW's duality table

STW tabulate: strict comparison fails in C*-examples / dynamical
comparison conjecturally always holds; uniform Γ conjecturally always
holds / relative Γ (SBP) fails dynamically.  Toms's 2026 counterexample
(imported at `toms-ah-counterexample-to-uniform-gamma`) breaks the
"uniform Γ always" cell, so THREE of the four cells now have failure
examples and dynamical comparison (XXXIII) is the last surviving
"always?" — with the recorded structural reason for optimism that the
C*-side failure mechanisms are characteristic-class obstructions with
no dynamical carrier on open subsets of `X`.

## Recurring frontier: equivariant CPoU

XXXVIII/XXXIX isolate the same missing technology as the session's
XXI/XXVIII/XXX analysis, now equivariantly: the von Neumann side is
DONE without outerness (Szabo--Wouters automatic equivariant
McDuffness), uniform Γ of the base is FREE (`Z`-stability), CPoU
exists non-equivariantly, and what is missing is `G`-invariant
complemented partitions of unity over wild trace boundaries.
Matui--Sato's (SI)+weak-Rokhlin machinery is exactly the
finitely-many-extremal-traces case of it.  Any progress on equivariant
CPoU simultaneously advances XXXVIII, XXXIX, and the classification of
actions.

## Individual notes

* **XXXIV** encoded as the optimistic characterisation (Z-stable ⟺
  almost finite ⟺ SBP for free minimal amenable actions); via KLTV /
  Elliott--Niu the converse direction is a Cartan-rigidity question
  for Γ: can central sequences exist that no Cartan expectation sees?
* **XXXVI (Phillips--Toms)**: `≤` is Niu-technology; `≥` needs
  characteristic classes from mean dimension, where the XXVII lane's
  mod-`ell` divider thresholds are a ready lower-bound tool awaiting a
  dynamical (first-return-tower) translation — flagged as the concrete
  crossover between this cluster and the ranks cluster.
* **XXXVII** recorded through its bottleneck: a Ruelle--Sullivan
  cap-product formula for the trace pairing compatible with
  Baum--Connes assembly; Scarparo-type HK counterexamples do not touch
  it (they break integral homology vs K-theory, not the measure
  pairing).

## Status

Eight roots (XXXII--XXXIX) + the GK-uniform-Γ target claim; three
routes; no establishments claimed.  With this wave, STW problems
XVIII--XXXIX all carry Cairn regions.
