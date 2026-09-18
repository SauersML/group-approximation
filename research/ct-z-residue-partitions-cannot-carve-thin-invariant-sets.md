---
rg: 2
id: ct-z-residue-partitions-cannot-carve-thin-invariant-sets
kind: claim
title: "Kourovka 21.74(a), obstruction: a residue-class partition permuted by g in CT(Z) must put each clopen-indecomposable component in one class, so an invariant set created by a computation inside a thin region (e.g. inside 7Z) can never make g permute a partition; machine-plus-single-mixer reductions cannot decide (a)"
requires:
  - ct-z-invariant-residue-partitions-are-not-conjugacy-invariant
  - ct-z-finite-cycle-problems-are-undecidable
---

**ESTABLISHED** (lane proof, not reviewed). Elementary. No priority is claimed.
Kourovka 21.74(a) itself remains **OPEN**. This node closes one natural route to
undecidability and says what any reduction must do instead.

## Setting

- **Notation.** As in `ct-z-invariant-residue-partitions-are-not-conjugacy-invariant`,
  `ĝ` is the extension of `g ∈ CT(Z)` to the profinite integers `Ẑ`, and `Ĉ` is the
  box of a class `C`. *YES* means that `g` permutes a partition of `Z` into at least two
  residue classes.
- **Indecomposable sets.** A clopen `ĝ`-invariant set `V` is *indecomposable* if, for
  every `k ≥ 1`, the only `ĝ^k`-invariant clopen subsets of `V` are `∅` and `V`.
  Examples: `ψ̂` on `Z_2`, and `ψ`-type mixers with attracting fibres (Theorem 4 there).
- **Co-classes.** A *co-class* is `Z ∖ C` for a proper class `C`, i.e. one with
  modulus `≥ 2`.

## Statement

1. **Components sit in one class.** Let `g` permute a residue-class partition `𝒫`, and
   let `V` be indecomposable. Then `V ⊆ Ĉ` for exactly one `C ∈ 𝒫`, and `g(C) = C`.
2. **Carving criterion.** Let `W ⊆ Z` be a `g`-invariant finite union of classes whose
   complement has indecomposable closure `V = Ẑ ∖ Ŵ`.
   - If `g` is YES, then `W` contains a nonempty `g`-invariant co-class `E`, and `g`
     permutes a partition of `E` into classes.
   - Conversely, any such `E ⊆ W` makes `g` YES.
3. **Thin sets.** If `W ⊆ pZ` for an odd prime `p`, then `W` contains no co-class.
   Hence, under the hypothesis of 2, `g` is NO.

## Proof

**1.**
- Let `K = |𝒫|!`. Each `Ĉ` is clopen and `ĝ^K`-invariant, so `V ∩ Ĉ` is a
  `ĝ^K`-invariant clopen subset of `V`, hence `∅` or `V`.
- The `Ĉ` partition `Ẑ`, so exactly one of them contains `V`.
- `g(C) ∈ 𝒫` contains `g(V ∩ Z) = V ∩ Z`, so `g(C) = C`. ∎

**2.**
- **Necessity.** Apply 1 to `V`, and let `C_1` be its class. Then `C_1 ⊇ Z ∖ W`, so
  `E = Z ∖ C_1 ⊆ W`.
  - `E` is nonempty, since `𝒫` has at least two parts.
  - `E` is `g`-invariant, since `g(C_1) = C_1`.
  - The other parts of `𝒫` partition `E` into classes that `g` permutes.
- **Sufficiency.** `{C_1} ∪` (that partition of `E`) is permuted. ∎

**3.**
- Let `E = Z ∖ r(m)` with `m ≥ 2`.
- The integers prime to `p` have density `(p−1)/p ≥ 2/3`, while `r(m)` has density
  `1/m ≤ 1/2`.
- So some `n` prime to `p` lies in `E`, and `E ⊄ pZ`. ∎

(For `p = 2` this fails: `0(2) = Z ∖ 1(2)`.)

## Consequence for 21.74(a)

**The natural reduction.** Take the counter-machine elements of
`ct-z-finite-cycle-problems-are-undecidable` and `ct-z-conjugacy-problem-is-undecidable`.
- They act on codes `X ∪ 2X ⊆ 7Z`, since every code has `1 ≤ v_7 ≤ N`.
- A Σ₁ event, such as halting from `x*` in the direction-switching machine, creates a
  finite invariant union `W` of code tubes. For example, `W` is the cycle of `x*`,
  exactly as in the halting case of the 21.73 node.
- The natural plan: couple everything else to one mixer, so that the rest is
  indecomposable, and hope that `g` is YES exactly when `W` exists.

**What 3 says.** Because `W ⊆ 7Z`, `g` is NO whether or not `W` exists. The Σ₁ event is
invisible to (a). The same holds for any special structure inside any `pZ`, `p` odd.

**What a reduction needs.**
- **Thickness.** The special invariant set must contain a co-class. Equivalently, its
  complement's mixing component must sit in one proper class.
- **Where thick structure comes from.** Valuation-coded (multiplicative) configurations
  are always thin, since every tube fixes a `p`-adic valuation. Thick configuration
  boxes need prefix (`V`-type, 2-adic) coding, and in one 2-adic coordinate that
  carries only one counter.
- **Which side this favors.** This points toward decidability of (a) on `CT_∅(Z) ≅ V`:
  a revealing-pair decomposition would give finitely many components and a
  finite-order remainder. It leaves open whether multi-prime interactions can
  manufacture thick Σ₁ structure.

## Lesson for general BH

**Coordinates only see thick dynamics.** A box partition must swallow each
indecomposable component whole. So invariant sets produced by computation are visible
to coordinates only if they contain a co-class; thin ones, living in a valuation
stratum, are not.

**For host design.** Undecidable dynamics (21.73, 21.74(b),(c)) lives in thin,
valuation-coded strata. Box-level structure, the kind a host needs to realize
subgroups as clopen stabilizers, is controlled by the coarse component structure. That
structure is far more rigid, and plausibly decidable.
