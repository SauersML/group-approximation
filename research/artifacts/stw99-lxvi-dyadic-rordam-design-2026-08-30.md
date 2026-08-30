---
title: STW Problem LXVI --- the dyadic Rordam tower, full design and verification ledger (2026-08-30)
---

Target: a simple unital infinite C*-algebra `B` with a unital embedding
`M_{2^∞} → B` whose image contains a nonzero finite projection
(Problem LXVI; equivalently, by the peers' corner reduction, a finite
simple unital CAR-containing algebra whose 2x2 amplification is infinite).
This dossier records a complete candidate construction, modelled line by
line on Rørdam, *A simple C*-algebra with a finite and an infinite
projection*, Acta Math. 191 (2003) (arXiv math/0204339), Sections 2–5,
with three deviations: step-dependent connecting maps, decoupled branch
data, and sparse paired steps.  Nuclearity is NOT claimed and is not
required by the problem.

## 0. Rørdam machinery reused verbatim

`Z = (S²)^∞`, `A = C(Z) ⊗ K`, `M(A)` its multiplier algebra; `p_n`, `p_I`
the line-bundle projections of `ζ_I = ⊗_{i∈I} ζ_i`; `g` a constant
rank-one projection (`= p_∅`).  Facts reused: Prop 2.1–2.3 (proper
infiniteness, corners, semiprojectivity of `E_2`), Section 3 (Euler-class
calculus; crucially Prop 3.2 is stated for LISTS `I_1, …, I_m`, i.e. for
multisets: `e(ζ_{I_1} ⊕ … ⊕ ζ_{I_m}) ≠ 0` iff the list admits a system of
distinct representatives), Lemmas 4.1–4.4 (bundles vs projections, infinite
sums, `Q ~ 1` iff properly infinite and full, finite subordination), and
Prop 4.5(i) (SDR for the multiset implies `g ⋠ Q` and `Q` not properly
infinite).

## 1. Step data

For each step `n ≥ 1` choose a countable branch list `𝔅_n`; branch
`β = (E_β, c_β, ν_β, I_β)`:

* `E_β ⊂ N` a finite eval-coordinate set, `c_β ∈ (S²)^{E_β}` eval points;
* `ν_β : N → N` injective, ranges pairwise disjoint over all branches of
  all steps and disjoint from all `I`-sets and all previously used
  integers ("fresh ranges");
* `I_β ⊂ N` a fresh finite tensor-set.

The branch map on `A`:
`ψ_β(f)(x) = τ( f(c_β on E_β, x∘ν_β elsewhere) ⊗ p_{I_β}(x) )`,
and `ψ_n = Σ_β S_β ψ_β S_β^*` for isometries `S_β` with
`Σ S_β S_β^* = 1` strictly; after Rørdam's Lemma 5.1/isometry correction
(V2 below) this extends to a unital endomorphism `ψ̄_n` of `M(A)`.
`B := lim (M(A), ψ̄_n)`, unital.

On multiset classes (Lemma 5.4-analogue, V3):
`ψ_β(p_J) ~ p_{α_β(J)}`, `α_β(J) = ν_β(J ∖ E_β) ∪ I_β`.

Constraints:

(C1) [density] for every `n`, the eval data `{(E_β, c_β)}_{β ∈ 𝔅_n}`
contains, for every finite `F ⊂ N`, branches whose eval points are dense
in `(S²)^F` (Rørdam's (5.1), per step).

(C2) [fullness hosts] every `𝔅_n` contains infinitely many PAIRS of
branches `β ≠ β'` with `I_β = I_{β'}` a singleton (the pairs' relabelings
still differ and have fresh ranges).

(C3) [size floor] `|I_β| ≥ h(n)` for all non-(C2) branches at step `n`,
with `h(n) → ∞` chosen below; (C2)-pairs are exempt.

(C4) [paired steps] along a sparse sequence `n_1 < n_2 < …`, the entire
list `𝔅_{n_k}` consists of branches occurring in identical duplicate
pairs (`E, c, ν, I` all equal within a pair).  Then for every projection
class, `[ψ_{n_k}(p_J-sum)]` is exactly `2 ·` a class.  All other steps
have all branches pairwise distinct.

(C5) [schedule] `c(n) := #{k : n_k ≤ n}` satisfies
`2^{c(n)+1} ≤ min(h(m) : m ≤ n)`-type growth: concretely
`h(n) = n + 4` and `n_k = 4^k` works, giving multiplicity
`2^{c(n)} ≤ n^{1/2}` against size floor `≥ h(first step after seed)`,
with the (C2) singleton contributions handled in §4.

## 2. The tower of projections

Seed: `P^{(0)} := ⊕_{i∈N} p_{a_i}` for distinct fresh singletons
`{a_i}`.  `Q_1 := ψ̄^∞(P^{(0)}) ∈ B`.

Halving: at stage `n_k`, the evolved multiset `M^{(n_k)}` of the seed is
exactly `2 · N_k` by (C4).  Let `X_k ⊕ X_k'` be the corresponding
orthogonal splitting of the stage-`n_k` projection into the two copy
classes (Lemma 4.2 matches them: identical multisets).  Define
`Q_{k+1} := ψ̄^∞(X_k)`.  Then `Q_k ~ Q_{k+1} ⊕ ψ̄^∞(X_k')` and
`ψ̄^∞(X_k') ~ Q_{k+1}`; orthogonality is preserved by the limit maps.

Unit halving: `1 ~ ⊕^∞ g` in `M(A)`; by (the stage-0 multiset containing
all the singleton pairs after one (C2)-host step — or directly:) for each
`i`, `θ ↪ ζ_{a_i} ⊕ ζ_{a_i}` (Rørdam Lemma 3.1 over `S²`), so
`1 ≾ Q_1 ⊕ Q_1` using infinitely many disjoint hosts; `Q_1` is full
(each `p_{a_i}` is full in `A`); Lemma 4.3 upgrades to `1 ~ Q_1 ⊕ Q_1`.
[Ledger note: run this either at stage 0 with the seed itself doubled
into `Q_1 ⊕ Q_1` inside `1`, or after the first paired step; the artifact
proof will fix stage 0: `1 ≾ 2 · P^{(0)}` holds already in `M(A)`.]

CAR: from `1 ~ Q_1 ⊕ Q_1'` and the chain `Q_k ~ Q_{k+1} ⊕ Q_{k+1}'`
choose partial isometries implementing the halvings and their transports;
the generated tower of unital `M_{2^k}`'s has closure `M_{2^∞} ⊂ B`, with
level-`k` diagonal projections equivalent to `Q_k`.

## 3. Finiteness of `Q_1` (hence of every `Q_k`)

Multiset ledger.  At stage `n` the seed's class is a multiset `M^{(n)}`
of finite subsets of `N`; by induction:

* (disjointness) two member sets share an element only if their entire
  branch histories coincide (fresh ranges; elements of a shared last-step
  `I_β` or a (C2) singleton are shared, but diverging histories relabel
  them apart one step later — the induction tracks "private elements":
  each set has at least `|history length| − 2` elements belonging to no
  other set of different history);
* (multiplicity) each set occurs `2^{c(n)}` times (paired steps double
  everything; other steps preserve multiplicity since branches are
  pairwise distinct with fresh data);
* (size) each set has at least `h(m)` elements after any non-(C2) step
  `m`, and never fewer private elements than `max(1, (#non-(C2) steps) − 2)`.

SDR: choose, for each distinct set, `2^{c(n)}` distinct private elements,
one per copy — possible once `2^{c(n)} ≤` private count, i.e. by (C5)
after finitely many stages; the finitely many early stages are handled by
Rørdam's Prop 4.5(i) hypothesis being needed only eventually (Prop 2.3:
proper infiniteness of the limit forces proper infiniteness of the
corners `Q^{(n)} M(A) Q^{(n)}` for all large `n`).  Prop 3.2 (list form)
then gives nonvanishing Euler class for every finite sub-multiset, so
Prop 4.5(i) applies: `g ⋠ Q^{(n)}` and `Q^{(n)}` is not properly
infinite for all large `n`.  As in Rørdam's Theorem 5.6(iii), if `Q_1`
were infinite in the simple `B` it would be properly infinite, and the
corner argument pushes proper infiniteness down to some stage `n`,
contradiction.  Sub-equivalent projections of finite ones are finite, so
every `Q_k` is finite; they are nonzero because the limit maps are
injective (V1(ii)).

## 4. Verification ledger (all expected to mirror Rørdam §5)

* (V1) Prop 5.2(i)-(ii) analogues, per step: (i) `ψ_n(g) ~ 1`:
  `ψ_β(g) ~ p_{I_β}`, and the (C2) pairs give
  `⊕^∞ g ≾ ⊕_{pairs} (p_a ⊕ p_a) ≾ ψ_n(g)`, then Lemma 4.3.
  (ii) for `0 ≠ f ∈ M(A)`: density (C1) supplies an infinite set of
  branches with `‖ψ_β(f)‖ ≥ δ` and `ψ_β(f)` full (Lemma 5.3 pointwise
  nonvanishing; the tensor factor `p_{I_β}` is nowhere zero), giving
  `ψ_n(f) ∉ A` and `A ψ_n(f)` full.  Simplicity of `B` then follows as in
  Theorem 5.6(i).
* (V2) Lemma 5.1 analogue: `ψ_n(e_λ) → F` strictly with `F ~ 1`: each
  branch contributes `F_β = τ(1 ⊗ p_{I_β})`, an infinite-multiplicity
  copy of `p_{I_β}`; a single (C2) pair already gives
  `⊕^∞(p_a ⊕ p_a) ≿ ⊕^∞ g ~ 1`, so `F ~ 1` by Lemma 4.3, and the
  isometry correction `T` defines the unital `ψ̄_n` on `M(A)`.
* (V3) Lemma 5.4 analogue for decoupled data: the eval coordinates of
  `p_J` contribute constant rank-one factors, the surviving coordinates
  relabel by `ν_β`, the tensor factor contributes `I_β`:
  `ψ_β(p_J) ~ p_{ν_β(J∖E_β) ∪ I_β}`.  Rørdam's computation carries over
  with `E_β` in place of `{1..j}` and arbitrary `I_β`.
* (V4) the multiset induction of §3, including the private-element count
  at paired steps (two disjoint transversal systems per doubling) and the
  (C2) shared singletons (never used as representatives).  RISK
  CONCENTRATES HERE; a fully explicit choice of `ν`-ranges and a written
  induction is required.
* (V5) `1_B` infinite (unit of `M(A)` is), `B` unital simple; Blackadar
  separabilisation keeping `{CAR generators, a non-unitary isometry,
  Q_k}` gives a separable simple example; finiteness and infiniteness
  persist in subalgebras.

## 5. Relation to recorded obstructions

Non-tensorial: the CAR arises from halvings of one evolving projection,
not from tensoring; `stw99-lxvi-car-stabilization-destroys-finite-seed`
does not apply.  The conditional expectation onto the CAR (if any) has
infinite index; `stw99-lxvi-finite-index-car-envelopes-are-stably-finite`
does not apply.  The construction is consistent with the peers'
reduction: `Q_1 B Q_1` is a finite simple unital CAR-containing algebra
with `M_2(Q_1 B Q_1) ≅ B` infinite.

## 6. What would refute the design

A failure of (V4)'s ledger — e.g. an unavoidable multiplicity blow-up on
sets of bounded private count — would leave `Q_1` possibly properly
infinite; the fallback is to slow the paired-step schedule, which only
thins the CAR levels' realisation stages, never blocks them.  The
structural risk is therefore low but nonzero; the claim node stays OPEN
until the ledger is written in full.
