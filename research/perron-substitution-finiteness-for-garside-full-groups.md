---
rg: 2
id: perron-substitution-finiteness-for-garside-full-groups
kind: claim
title: A Perron substitution condition replaces Li's diagonal multiplicity condition (t<d) and makes the topological full group of a Garside category of type F_n
requires:
  - cubulated-groups-act-by-bisections-of-a-pointed-cube-category
  - raag-cube-codings-fail-li-multiplicity-at-every-power
distinct_from:
  finitely-coded-cantor-actions-give-type-a-hosts: that quotes Li's theorem with (t<d) verbatim; this weakens (t<d) to a Perron spectral condition on the type-substitution matrix, so it covers deterministic label-injective codings (free groups, RAAGs) that (t<d) misses.
  raag-cube-codings-fail-li-multiplicity-at-every-power: that shows (t<d) fails for RAAG codings because each maximal state returns only once; this supplies the replacement finiteness theorem whose recurrence is off-diagonal.
---

**OPEN (proof refuted 2026-09-18).**
- The only proof, `perron-substitution-finiteness-proof`, is invalidated by
  `perron-weights-do-not-give-li-finiteness` (landed ba9176b48a).
- For the `F_k` reduced-word coding, (Perron) holds, yet infinitely many Witzel complexes
  `|E(x_N)|` are not simply connected. So no height function, Perron or otherwise, makes
  Witzel's criterion work for that datum.
- The correct extra hypothesis is merge packing (Pack), decided by
  `thin-cycles-decide-li-packing`.
- After Cuntz stabilization, packing is automatic
  (`cuntz-stabilized-garside-full-groups-are-f-infinity`, 16be960ff1).
- Whether (Perron) alone implies `F_n` for the unstabilized full group is open. No
  counterexample is known.

The original text follows, unchanged, as a record.

~~**ESTABLISHED** through `perron-substitution-finiteness-proof` (lane proof; it uses
X. Li, arXiv:2110.04505v2, Theorem `thm:Fn` and its proof; not independently reviewed;
no priority claimed).~~

## Motivation

`raag-cube-codings-fail-li-multiplicity-at-every-power` proved that Li's multiplicity
condition (`t<d`) fails for every label-injective deterministic coding beyond products
of trees: from a maximal state the only single-step return to that state is the state
itself, so the diagonal of the type-substitution matrix is `1`, never `≥ 2`. Yet these
codings have exponentially many reduced words, so their type graph is *primitive with
Perron eigenvalue `> 1`*: recurrence to a type happens through *other* types, not
through a doubled self-loop. This node turns that observation into a finiteness theorem.

## Setting (Li's, verbatim)

Let `𝔠` be a finitely aligned left cancellative small category with finite `𝔠⁰`, right
cancellative up to `=*`. Let `𝔖` be a Garside family in `𝔠` that is locally finite,
`=*`-transverse, with `𝔖 ∩ 𝔠* = ∅`, and with `(𝔖^{≤L})^♯` closed under left divisors for
every `L`. Let `X ⊆ Ω_∞` be a closed invariant subspace and let `𝔛, 𝐗, Γ, 𝚪, * ∈ 𝐗, ℭ, 𝒬`
be as in Li §`s:GarsCat-TFG`. Assume condition (F) and condition (St), and that `ℭ`
admits lcms (Li's standing hypotheses for `thm:Fn`, minus `(t<d)`).

**The type set and substitution matrix.** The set of *types* is the finite set
`𝔗 = 𝔛(*)` of cylinders `X(𝔳; 𝔢)` reachable from `*` (finite because `𝔠⁰` is finite and
`𝔖` is locally finite). For a full one-step expansion `γ(𝔢, 𝔖₁)` of a cylinder of type
`τ = X(𝔳; 𝔢)`, Li's Lemma `lem:gamma` writes its codomain as the disjoint family
`(X(𝔡(s); 𝔣_s))_{s}`. Define the **type-substitution matrix** `M ∈ ℕ^{𝔗×𝔗}` by

  `M[τ', τ] = #{ s : the piece X(𝔡(s); 𝔣_s) has type τ' }`  (up to `=*`).

`M` records how many pieces of each type one full expansion of a `τ`-cylinder produces.
Since `X ⊆ Ω_∞`, the leftover `X(𝔳; 𝔖₁ ∪ 𝔢)` is empty, so `M` accounts for the whole
codomain.

## The condition

**(Perron).** `M` is primitive (irreducible and aperiodic) with Perron eigenvalue
`λ > 1`. Equivalently: there is a strictly positive weight `w ∈ ℝ^𝔗_{>0}` with
`w·M[·,τ] > w_τ` for every type `τ` that admits a proper expansion.

## Theorem

Assume Li's standing hypotheses above and **(Perron)**. Then for every `n`, `𝒬(*,*)`
is of type `F_n` provided `𝔠*(𝔳,𝔳)` is of type `F_n` for every `𝔳 ∈ 𝔠⁰`; and
`𝐅((I_l ⋉ X)_Y^Y)` is of type `F_n` under the same hypothesis. In particular the
topological full group is finitely presented (`F_2`) when the unit groups are.

## Relation to (t<d)

**(Perron) strictly weakens (t<d).** If `(t<d)` holds then every type reproduces itself
at least twice, i.e. `M[τ,τ] ≥ 2`; the all-ones weight `w = 𝟙` then satisfies
`𝟙·M[·,τ] ≥ 2 + (other pieces) > 1 = 𝟙_τ`, so **(Perron)** holds with `w = 𝟙`. Li's
theorem is the case `w = 𝟙`. **(Perron)** additionally captures the off-diagonal
recurrence that label-injective codings force, where `M[τ,τ] = 1` but `λ > 1`.

## Consequences

- **Free groups, un-recoded** (`perron-recovers-free-group-boundary-full-groups`): the
  reduced-word automaton of `F_k` has `M = J − P` (`P` the letter-inversion
  permutation) with row sums `2k−1`, hence `λ = 2k−1 > 1` and `M` primitive, while its
  diagonal is `1`. So its boundary full group is `F_∞` by this theorem, without the
  power-and-phase recoding that `raag-cube-codings-fail-li-multiplicity-at-every-power`
  needed. `F_2 × F_2` follows by the product of two such matrices.
- **Cube codings** (`cubulated-groups-act-by-bisections-of-a-pointed-cube-category`):
  Bishop--Q1.15 now reduces, for special cube complexes, to **primitivity** and
  `λ > 1` of the state-substitution matrix of the pointed-cube category, in place of
  the impossible `(t<d)`. This is an explicit finite check on `𝔗 × 𝔗`.

## What remains for RAAGs (open, honest)

`(Perron)` needs the state graph to be *primitive*. For the free group it is (a
self-loop at a state gives aperiodicity; every state reaches every state). For a RAAG
`A_Γ` the state set is the signed cliques and the one-step reachability is "next
allowed layer"; whether this graph is irreducible and aperiodic must be checked per
`Γ`. `P_4` (the smallest non-join RAAG) is the first test and is recorded as OPEN on
`raag-cube-codings-fail-li-multiplicity-at-every-power`. `λ > 1` itself always holds
once `A_Γ` is not virtually cyclic (exponential trace growth).

## Lesson for general BH

Li's `(t<d)` ("each piece self-reproduces `≥ 2`") is one *sufficient* way to build the
height function that his `F_n` proof needs; the proof uses that height function only
through strict increase and finite sublevels. The right invariant is spectral: a
finite-type coding gives a finitely presented simple host as soon as its
type-substitution matrix has **Perron eigenvalue `> 1` and is primitive**. Loop-richness
is a Perron property, not a diagonal one. This dissolves the "deterministic codings have
no loops" wall for every host whose local combinatorics grows exponentially, and it is
the general finiteness certificate the synthesis calls FTR for deterministic codings.

## Attempts

1. **(bh-major-cube-b, 09-18) The proof is invalid, and the "ESTABLISHED" status above
   does not stand for `n ≥ 2`.** See `perron-weights-do-not-give-li-finiteness`, which
   invalidates `perron-substitution-finiteness-proof`.
   - For the `F_k` reduced-word coding (so `(Perron)` holds), `𝐗(*)` contains
     infinitely many objects `x_N = (a, a^{-1}, N b, N b^{-1})` whose Witzel complexes
     `|E(x_N)|` are not simply connected.
   - Li's `lem:link:n-conn_3` needs the packing number `ρ'(x) → ∞`, and here
     `ρ'(x_N) ≤ 2`. A Perron height does not control it.
   - The correct extra hypothesis is **(Pack)**: finitely many objects of bounded
     packing. Li's (`t<d`) is what makes packing a height.
   - The free-group consequence remains true, via Li's `cor:ProdGraphs` with Matui's
     recoding. The claim that no recoding is needed does not.
