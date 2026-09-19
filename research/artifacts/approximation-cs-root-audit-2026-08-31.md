# Approximation and complexity root audit — 2026-08-31

## Verdict ledger

The six requested high-impact targets remain open after a primary-literature
check and a proof audit:

| Cairn target | Verdict | Exact remaining gate |
|---|---|---|
| `non-hyperlinear-group` | **OPEN** | No discrete nonhyperlinear witness; current nonsofic examples have no proved failure of hyperlinearity. |
| `q3-4-resolved` | **OPEN** | Both admissible answers, `hyperlinear-nonsofic-group` and `hyperlinear-implies-sofic`, remain open. |
| `one-relator-groups-sofic` | **OPEN** | The nonabelian derived Linton radical / free-edge Magnus-chain approximation remains. |
| `nonsofic-one-relator-group` | **OPEN** | No locally indicable, primitivity-rank-two witness with an action-sensitive nonsofic obstruction is known. |
| `quantum-pcp-constant-gap-local-hamiltonian` | **OPEN** | The proposed Cairn lane still needs state-weighted local syndrome-port domination at bounded horizon. |
| `unique-games-conjecture` | **OPEN** | The Rich 2-to-1 equivalent formulation still lacks the analytic affine-star density estimate and the written hardness endgame. |

No root was promoted.  One intermediate lemma in the UGC lane is newly
established: `triangle-defect-globalizes-to-a-bounded-label-list`, with the
sharp constants `L=2` and `gamma=1-eta`.

## Cairn reduction inventory

* `q3-4-resolved` has exactly the two logically admissible answer claims:
  `hyperlinear-nonsofic-group` and `hyperlinear-implies-sofic`.  A proof that
  one current nonsofic candidate is nonhyperlinear would close
  `non-hyperlinear-group` but would not decide this disjunction.
* `one-relator-groups-sofic` is reduced on its positive side to the Linton
  shell (`linton-shell-sofic`) or, independently, to soficity of the generic
  staggered Magnus chain (`magnus-staggered-chain-sofic`).  The Fox/Magnus
  quotient modulo the derived Linton radical is already closed.  The
  negative root `nonsofic-one-relator-group` attacks the same remaining core
  but has no candidate rigidity inequality compatible with local
  indicability.
* `quantum-pcp-constant-gap-local-hamiltonian` has a proposed conditional
  conversion from combinatorial gap to energy gap.  Its noncircular supply
  problem is `local-syndrome-port-domination-at-each-gadget`; the checkpoint
  route further decomposes this into a bounded-horizon anchor and a backward
  syndrome recursion for the actual amplifier.
* `unique-games-conjecture` passes through the cited equivalence with
  `rich-2to1-games-conjecture`.  The proposed affine-orientation lane needs
  both `affine-orientation-glue-lemma` and the separately recorded soundness
  implication `glue-lemma-implies-rich-2to1-hardness`.  Inside the glue lemma,
  the combinatorial globalization premise is now closed, leaving the
  analytic product-uniform star-density estimate.
* `non-hyperlinear-group` has multiple large compilation lanes.  The most
  compressed arithmetic route currently ends at weak dimension-free
  ucp-stability for `SL_3(Z)` on the relevant regular-type approximations;
  the game/microstate routes still need a semantic compiler preserving a
  positive-density authenticated corner.  None of these premises is
  established by the literature checked below.

## Primary-literature boundary

### Hyperlinear versus sofic

Fournier-Facio, *A torsion-free non-sofic group* (arXiv:2608.02025,
3 August 2026), constructs torsion-free **nonsofic** examples while stating
that they use the same technical criterion as the binary-Leavitt example.
The paper does not claim that these groups are nonhyperlinear or hyperlinear,
so it selects neither answer to Pestov Question 3.4.  Its Remark 1.4 instead
describes non-examples for the other approximation properties as still to be
found:

<https://arxiv.org/abs/2608.02025>

The strongest direct conversion result located remains restricted to
amenable groups: Arzhantseva--Paunescu, *Hyperlinear approximations to
amenable groups come from sofic approximations* (arXiv:2311.09202).  It does
not supply a conversion for arbitrary hyperlinear groups:

<https://arxiv.org/abs/2311.09202>

Accordingly, neither the existence of a nonhyperlinear discrete group nor
hyperlinear-versus-sofic is closed by the 2026 nonsofic breakthrough.

### One-relator soficity

Berlai, *A new family of sofic one-relator groups* (arXiv:2502.05064), proves
soficity for explicit infinite families that need not be residually finite
or residually solvable.  Its abstract and Theorems A/C are subclass results,
not the universal theorem and not a counterexample:

<https://arxiv.org/abs/2502.05064>

The Cairn reductions remain correctly localized: the affirmative side is
stuck on the nonabelian derived Linton core (or equivalently the generic
free-edge Magnus chain), while every negative witness must be torsion-free
and locally indicable and must evade the established first-order Fox/Magnus
quotients.

### Quantum PCP

Bafna--Vyas, *Private PCPs from Product Expansion*, ECCC TR26-150,
19 August 2026, explicitly opens by saying that the quantum PCP analogue for
QMA remains wide open:

<https://eccc.weizmann.ac.il/report/2026/150/>

Nothing in that paper supplies the tensor-site, state-weighted operator
domination required by `local-syndrome-port-domination-at-each-gadget`.
The repository's checkpoint recursion removes a depth loss only conditional
on bounded-horizon syndrome anchors; it does not construct those anchors.

### Unique Games

Braverman--Khot--Minzer, *On Rich 2-to-1 Games*, ITCS 2021, prove that their
Rich 2-to-1 Games Conjecture is equivalent to UGC:

<https://doi.org/10.4230/LIPIcs.ITCS.2021.27>

A current 2026 primary proceedings source explicitly calls UGC unresolved:
Culf--Mastel--Paddock--Spirig, *The Quantum Smooth Label Cover Problem Is
Undecidable*, ICALP 2026:

<https://doi.org/10.4230/LIPIcs.ICALP.2026.71>

A 2025 primary proceedings source also records the best unconditional Unique
Games hardness as completeness `1/2-epsilon` with arbitrarily small
soundness, rather than the UGC completeness `1-epsilon`: Bodirsky et al.,
*Undefinability of Approximation of 2-To-2 Games*, CSL 2025:

<https://doi.org/10.4230/LIPIcs.CSL.2025.16>

Thus the BKM equivalence is a valid reformulation, not a resolution.

## New closure: star-degree averaging

The globalization claim had been made to look like a substantial
local-to-global theorem.  Its exact conditional content is much simpler.
Let `C_b` be the selected affine pair for `b in B`, and suppose a set
`S subset B x B` of product-uniform density at least `1-eta` consists of
certified star pairs, so `(b,c) in S` implies `C_b intersect C_c != empty`.
Then

```text
E_(b in B) Pr_(c in B)[(b,c) in S] >= 1-eta.
```

Some `b_0` has star degree at least `1-eta`; taking `Q=C_(b_0)` gives
`|Q|=2` and hits at least the same fraction of all `C_c`.  The same conclusion
holds for uniform distinct-pair sampling after adjoining the diagonal.

This proof also exposes two defects in the earlier analytic formulation:

1. `C_(b+c)` is not defined merely from choices `C_b` for `b in B` unless
   `b+c in B` or a completion is supplied.
2. In ambient dimension at least three, arbitrary affine lines need not lie
   in one affine plane; they may be skew.  Hence “exactly star or triangle”
   is not a valid dichotomy.  Skew and unavailable-sum cases must count as
   defect, or the proof must separately rule them out.

The sampling measure is essential.  High star density only after conditioning
on an additive-triple set with a biased marginal need not hit a constant
fraction under the uniform measure on `B`.  The remaining analytic claim has
therefore been restated with the exact product-uniform output consumed by the
averaging lemma.

## Why UGC is still open

The new lemma removes only the combinatorial half of
`glue-lemma-from-small-triangle-defect`.  Two independent commitments remain:

1. prove that boundedness, noise, and heavy restricted influences produce
   product-uniform star certificates on almost every pair in `B x B`;
2. write and verify the soundness reduction
   `glue-lemma-implies-rich-2to1-hardness`.

Neither is supplied here.  Promoting `affine-orientation-glue-lemma`, Rich
2-to-1, or UGC would therefore be unsupported.
