---
rg: 2
id: amenable-cd-two-annihilator-iteration-closes-up
kind: claim
title: Over a torsion-free amenable group of rational cd at most 2, one zero divisor forces zero divisors of arbitrarily small L2-rank; the annihilator iteration maps this configuration to itself and cannot close the L2-rank gap
distinct_from:
  amenable-cd-two-groups-have-an-l2-rank-gap: that is the open gap statement for finitely generated groups of integral cd 2; this proves that the gap can fail only in the extreme form (infimum 0), for all torsion-free amenable groups of rational cd at most 2, and that the annihilator iteration aimed at the gap is a closed loop
  amenable-cd-two-l2-rank-gap-forces-baumslag-solitar: that derives the {0,1} dichotomy for finitely generated groups of integral cd 2 through the second syzygy, Degrijse's finiteness step and the BS(1,m) classification; this gets it directly from one annihilator, with no finite generation, no syzygy and no classification, and only rational cd at most 2
  amenable-principal-fp-group-algebras-are-domains: that shows an annihilator of type FP is zero; this runs the other way and feeds the non-finitely-generated annihilator into the trace-ideal theorem to regenerate thin zero divisors
  l2-small-projectives-with-rank-gap-are-finitely-generated: that is the general module theorem; this applies it to annihilators of single elements and iterates it
---

**ESTABLISHED** (proposed; referee pending) through
`amenable-cd-two-annihilator-iteration-closes-up-proof`, from
`l2-small-projectives-with-rank-gap-are-finitely-generated` (item 1, over `Q[G]`) and the imports
(I1)–(I5) of `amenable-principal-fp-group-algebras-are-domains-proof` (Lück's dimension theory,
amenable dimension-flatness, Higson–Kasparov plus the Baum–Connes trace theorem).

Let `G` be a torsion-free amenable group of any cardinality with `cd_Q G <= 2`. For example, `G`
can be any amenable group with `cd_Z G <= 2`. Write `rk(a) = dim_NG(NG a)` for `a ∈ Q[G]`. This is
the `L²`-rank of the target. Put `Σ(G) = { rk(a) : 0 ≠ a ∈ Q[G] } ⊆ (0, 1]`.

1. **Rank defect is zero division.** Let `0 ≠ a ∈ Q[G]`. Then `rk(a) < 1` iff `a` is a left
   zero divisor, iff `a` is a right zero divisor. This holds for every amenable `G`, with no
   condition on `cd`.
2. **Annihilator step.** If `a ≠ 0` is a zero divisor, then `J = ann_l(a)` is a projective left
   ideal. It is not finitely generated, and `dim_NG(NG ⊗ J) = 1 − rk(a) ∈ (0, 1)`.
3. **Trace step.** For such `J` and every `ε > 0`, the trace ideal `T(J)` contains `b ≠ 0` with
   `rk(b) < ε`. Every such `b` is again a zero divisor, so step 2 applies to `b`.
4. **Dichotomy.** Either `Σ(G) = {1}`, in which case `Q[G]` is a domain, or `inf Σ(G) = 0`. So for
   these groups, an `L²`-rank gap is the same as `Q[G]` having no zero divisors. A single zero
   divisor of any rank below 1 already forces zero divisors of arbitrarily small rank. If
   `cd_Q G <= 1`, the first case always holds.
5. **The iteration closes up (obstruction).** Suppose `Q[G]` has a zero divisor `a_0 ≠ 0`. Then
   there is an infinite chain of zero divisors `a_0, a_1, a_2, …` with
   `a_{n+1} ∈ T(ann_l(a_n))` and `rk(a_{n+1}) < rk(a_n)/2`. The dimensions `1 − rk(a_n)` of the
   non-finitely-generated projectives `ann_l(a_n)` increase to 1. The four inputs of a step are
   Elek/dimension-flatness, `gl.dim Q[G] <= 2`, integrality of traces, and the trace-ideal
   theorem. Each is used in step `n+1` exactly as in step `0`, and none is violated anywhere on
   the chain. The Følner kernel densities of `a_n` equal `1 − rk(a_n)` (Elek; recalled), so they
   add nothing. **Hence the annihilator iteration proposed for the gap is a self-map of the
   hypothesis "`Q[G]` has a zero divisor".** It cannot produce a contradiction unless it is given
   an extra input that forbids the chain. By item 4, forbidding the chain is equivalent to the
   domain property it was meant to prove.
6. **Calibration: where torsion-freeness enters.** Let `L = Z/2 ≀ Z`. Then `Q[L]` satisfies every
   input except integrality: `L` is amenable, `cd_Q L <= 2` so `gl.dim Q[L] <= 2`, and Elek's
   approximation holds. The idempotents `e_n = ∏_{k<=n} (1 + g_k)/2` are zero divisors with
   `rk(e_n) = 2^{-n}`. There the iteration stops at step 2: `ann_l(e_n) = Q[L](1 − e_n)` is
   finitely generated, of non-integral dimension `1 − 2^{-n}`. So gl.dim `<= 2`, amenability and
   Følner approximation do not imply the gap. Torsion-freeness enters the iteration only through
   integrality of traces, and there only to conclude "`ann_l(a)` is not finitely generated".
   That conclusion is exactly what the trace step needs to regenerate thin elements.

**What it kills.** It kills every argument for `amenable-cd-two-groups-have-an-l2-rank-gap` that
passes from thin elements to annihilators and trace ideals, and otherwise uses only
`gl.dim Q[G] <= 2`, amenable dimension-flatness or Følner/Elek approximation, and integrality of
`dim` on finitely generated projectives. This includes any finite number of rounds of the
iteration and any choice of dual bases. The iteration takes a zero divisor to further zero
divisors, so its outputs are consequences of its input. A proof of the gap must bring in a
statement not implied by "one zero divisor exists". The known candidates are all equivalent to the
target: coherence of `Q[G]` (`amenable-cd-two-solvable-iff-coherent-rational-group-algebra`),
finiteness of one annihilator (`amenable-principal-fp-group-algebras-are-domains`), or elementary
amenability of the subgroup carrying the zero divisor (Remark R below).

**Remark R (where thin elements live).** Let `G` be as in the target: finitely generated,
amenable, `cd_Z G = 2`. If `ab = 0` with `a, b ≠ 0`, then `H = ⟨supp a ∪ supp b⟩` is again a
two-dimensional counterexample to Kropholler's question: finitely generated, amenable, `cd H = 2`,
and not elementary amenable. Every term of the chain in item 5 therefore lives in the group ring
of a finitely generated counterexample.
