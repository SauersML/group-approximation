---
rg: 2
id: e2-for-plane-lifts-is-clustered-floating-freedom
kind: claim
title: In crossing-wire plane lifts the letters and coordinates are automatically central, so gate E2 is exactly clustered, relatively rigid floating freedom; transport-coupled floating data would be rigid but can never be minimal for a non-SFT input
requires:
  - plane-local-freedom-kills-rigidity-of-plane-lifts
  - extension-rigidity-is-base-centrality-plus-pointwise-rigidity
  - crossing-wire-fixed-point-tile-sets-are-quantum-rigid
  - strongly-proximal-geometries-are-disjoint-from-measured-inputs
distinct_from:
  plane-local-freedom-kills-rigidity-of-plane-lifts: that proves far free planes kill rigidity and proposed bijective transports as the fix; this proves the letter layer is classical in every crossing-wire table lift, characterizes E2 by clustering, and WITHDRAWS the transport fix (Theorem C).
  copy-constraints-make-simulation-skeleton-and-data-commute: that gets skeleton–data commutation from exact copy rules in aligned simulations; this adds the crossing of copied table wires, which makes the letters of all planes commute and central.
  keyed-diversification-slots-give-plane-constant-minimal-lifts: that is the E1 construction; Theorem C shows its slot mechanism is incompatible with any transport of floating data, and Section 4 names the one shape of freedom E2 still allows there.
---

**Status.**
- Theorem A is ESTABLISHED, conditional on the layout hypotheses (P) below; they are design
  obligations of the construction lane.
- Theorem B is ESTABLISHED given A.
- Theorem C is ESTABLISHED: a no-go, lane proof, unreviewed.
- Section 4 is OPEN.

## Setting

A *crossing-wire table lift* is an SFT `X` over `Λ_0 x Z^2`, with `Λ_0` finitely generated and
infinite, built as in `keyed-diversification-slots-give-plane-constant-minimal-lifts`, satisfying
(P):
- **(P1) Skeleton.** It is `Λ_0`-constant. In each plane it is a Durand–Romashchenko–Shen
  variable-zoom hierarchy whose layout satisfies (L0)–(L4) of
  `crossing-wire-fixed-point-tile-sets-are-quantum-rigid` at every level.
- **(P2) Inputs.** The table fields `τ_k`, `τ_k^{(s)}`, `τ_{k+1}` and the identity data are side
  inputs of the level-`k` macrotiles. Every two side inputs of a macrotile cross.
- **(P3) Plane-constant letters.** Letters `ℓ` are plane-constant. The base, delegation, zone and
  twin rules are those of 695a89096, and the zone checks are deterministic accepting
  computations.

Quantum families and (Q1)–(Q3) are as in `fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Theorem A (the input layer is classical)

In every `D`-quantum family of a crossing-wire table lift (`D` at least the rule radius):
- (a) the letter projections `L_b(λ)` are well defined (independent of the `Z^2`-site) and
  pairwise commute, over all planes;
- (b) every table projection equals a letter projection: `P[τ^λ_k(f) = b] = L_b(λf)`;
- (c) every idempotent of the family commutes with every `L_b(λ')`. So the letters are
  central, and so are the skeleton coordinate projections.

*Proof.*
1. **Constancy.** Rules of the form "the symbol at `p` equals the symbol at `q`" with
   `d(p,q) ≤ 2D` give `E_a(p) = E_a(q)`. By (Q3), `E_a(p)E_b(q) = 0` for `a ≠ b`, and these
   commute by (Q2). So `E_a(p) = E_a(p) Σ_b E_b(q) = E_a(p)E_a(q)`, and symmetrically this
   equals `E_a(q)`. This applies to:
   - letter constancy on planes, giving (a)'s well-definedness;
   - skeleton constancy across planes;
   - the twin rule, whose carriers sit at the same `Z^2`-site of adjacent planes.
2. **Coordinates are central.** Step 1 of the crossing-wire proof applies in each plane.
   Skeleton constancy moves each coordinate projection to any other plane, where (Q2) makes it
   commute with the local edges. Split the space along these central phase projections.
3. **Blocks.** On each summand, Steps 2–4 of the crossing-wire proof apply in each plane by
   (P1)–(P2). Every level-`0` edge of a level-`k` block `B` of plane `λ` lies in the
   commutative algebra `A_k(B)` of `B`'s side inputs. By (P2) these include the table bits
   `τ^λ_k(f)`, `f ∈ F_k`.
4. **Tables are letters (b).** Induction on `|f|`.
   - The base rule gives `τ_0(1) = ℓ`.
   - Delegation coherence is a deterministic evaluation inside `A_{k+1}` (Step 2(c) of the
     crossing-wire proof).
   - A failing zone check annihilates its joint spectral projection, by the (F2) argument, so
     `P[τ_k(sf) = b] = P[τ_k^{(s)}(f) = b]`.
   - The twin rule gives `P[τ^{(s),λ}_k(f) = b] = P[τ^{λs}_k(f) = b]`.
   - This is step 2 of 695a89096, as operator identities.
5. **Letters commute (a).** For `f, f' ∈ F_k`, the projections `L(λf)` and `L(λf')` are table
   bits of one level-`k` block of plane `λ`. They lie in the commutative `A_k(B)`. Since `F_k`
   exhausts `Λ_0`, every pair of planes occurs for large `k`.
6. **Letters are central (c).** A given edge of plane `λ` lies in `A_k(B)` for all large `k`.
   `A_k(B)` is commutative and contains `L(λf)` for all `f ∈ F_k`, so the edge commutes with
   every letter. Every idempotent lives in some plane. ∎

## Theorem B (what E2 is for such lifts)

Apply `extension-rigidity-is-base-centrality-plus-pointwise-rigidity` with base = skeleton plus
letters and tables, which are central by Theorem A. Then `X` is `D`-quantum rigid iff it is
`D`-rigid relative to every frozen base point `(σ, y)`.

The relative problem is about the remaining data. With no cross-plane rules on it, it is a
product over planes (`plane-local-freedom-kills-rigidity-of-plane-lifts`, Lemma 1). So:

**`X` is rigid iff, at every frozen `(σ, y)`:**
1. **(Clustered freedom.)** The planes whose fibre has at least two fillings lie in a set of
   diameter `≤ 2D`.
   - *Necessity.* Otherwise the two far modifications of Theorem 1 there exist.
2. **(Local rigidity.)** The fibre over that cluster is relatively rigid.
   - *Sufficiency.* A singleton fibre makes its idempotents act as `0/1` scalars on the
     localization. So only the cluster's operators remain, and they commute by (2).

## Theorem C (transport coupling is incompatible with minimality)

Suppose, in a crossing-wire table lift of a non-SFT minimal `Y`:
- every undetermined coordinate is coupled across planes by local rules
  `σ^{λs}_k = β_{s,k}(T^λ_k, T^{λs}_k, σ^λ_k)`;
- each `β_{s,k}(t, t', ·)` is a bijection of admissible identities (the fix proposed in
  Part 3 of `plane-local-freedom-kills-rigidity-of-plane-lifts`).

Then `X` is not minimal.

*Proof.*
1. **The key graph.** `G_k` has as vertices the level-`k` tables occurring in `Y`, with edges
   `t —s— t'` whenever `(T^λ_k, T^{λs}_k) = (t, t')` for some `y, λ`. It is connected: every
   table occurs in every `y` by minimality, and `Λ_0` is connected.
   A *parallel section* is a map `g` with `g(t) ∈ Adm(t)` and `g(t') = β_s(t, t', g(t))` on every
   edge. It is determined by one value.
2. **Finite chains are parallel.** Take any `y` and a generic skeleton, so all chains are
   finite; such points exist (step 2 of 695a89096). There the level-`k` identity at a skeleton
   position `π` is `f_k(π, T^λ_k)`. The `β`-rule holds everywhere, so each `f_k(π, ·)` is a
   parallel section.
3. **Infinite chains are parallel, with one section.** Let `x` have an infinite chain, and fix
   a finite `F ∋ 1` containing the generators.
   - By minimality, the pattern of `x` on the identity and table carriers of planes `λF` at
     level `k` occurs in a generic-skeleton point.
   - So `σ^{λf}_k = g_λ(T^{λf}_k)` for a parallel section `g_λ`.
   - Windows `λF` and `λsF` share a plane, so `g_λ` and `g_{λs}` agree at one key. They are
     therefore equal.
   - Hence `σ^λ_k = g_k(T^λ_k)` with one section `g_k` for all planes.
4. **Contradiction.** `g_k` is read continuously from plane `1` (from `T^1_k` and `σ^1_k`),
   and the same value is read from every plane, so it is `Λ_0`-invariant.
   - Put `τ' = (skeleton, (g_k)_k)`. It is a continuous `Λ_0`-invariant factor.
   - Every coordinate is determined by `τ'` and `y`: identities are `g_k(T)`, and the rest is
     determined.
   - Theorem 3(iii) of `strongly-proximal-geometries-are-disjoint-from-measured-inputs` then
     makes `Y` an SFT. ∎

**Remark.** Without the minimality assumption, Theorem A plus the `β`-rules make every plane's
identity algebra generated by plane `1`'s and the (central) letters. So a transport-coupled lift
*is* rigid. It just cannot be minimal. Any subshift of it is rigid too
(`quantum-rigidity-passes-to-subshifts`), but a minimal one would be a proper, non-SFT carving.

**Withdrawal.** The design rule "couple floating identities by bijective transports" of
`plane-local-freedom-kills-rigidity-of-plane-lifts`, Part 3, is withdrawn. Parts 1 and 2 of that
node stand.

## Section 4. The one shape left for Λ_0-constant skeletons (OPEN)

By Theorems B and C, a minimal rigid crossing-wire table lift needs two things.
- **Freedom only at exceptional keys.** Floating options must exist only at planes whose
  tables lie in a set `Bad_∞ = ∩_k Bad_k`.
  - Each `Bad_k` is clopen and admits at least two identities at level `k`.
  - For every `y`, the set `{λ : T^λ ∈ Bad_∞}` must have diameter `≤ 2D`.
  - Nonempty clopen conditions recur syndetically, so `Bad_∞` must be nowhere dense: a
    defect-type condition met at essentially one plane.
- **Local rigidity** of the fibre at that defect.

Minimality then needs the finite-level shadows of the defect's choices (keys in `Bad_k`, which
recur) to be realized by determined data elsewhere.

If no such defect structure exists, the skeleton must vary along `Λ_0`. That is the carrier
principle of SYNTHESIS v4 again: the geometry must be carried by the acting group.

## Lesson for general BH

In table-based plane lifts the input is never the E2 obstruction.
- Crossing of copied table wires makes every letter of every plane a central classical
  observable.
- All of E2 then sits in the floating data, and its only rigid, minimal-compatible shape is
  *clustered* freedom.
- Transports make freedom plane-global, so it is rigid. But they force a single parallel
  section, hence determination by an invariant factor, hence (for non-SFT inputs) failure of
  minimality.

So E2 for `Λ_0`-constant skeletons comes down to building defect-localized freedom. If that is
impossible, the Z^2 base is dead for E2 and the skeleton must live on the acting group.
