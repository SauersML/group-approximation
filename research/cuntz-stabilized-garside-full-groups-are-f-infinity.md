---
rg: 2
id: cuntz-stabilized-garside-full-groups-are-f-infinity
kind: claim
title: For every Li-Garside category with trivial units and no invariant open set beyond a loop ray, the full group of its boundary groupoid times the Cuntz groupoid is of type F_infinity, with no loop, degree-map or (t<d) hypothesis
requires:
  - perron-weights-do-not-give-li-finiteness
  - thin-cycles-decide-li-packing
  - pointed-cube-categories-are-li-garside-categories
distinct_from:
  stabilized-kgraph-full-groups-have-type-a-actions: that gets F_infinity from Li's k-graph theorem, which needs two loops of every colour at every vertex; this needs no loops and no degree map, because the Cuntz colour supplies the merge packing.
  finitely-coded-cantor-actions-give-type-a-hosts: that assumes finite presentation of the stabilized full group; this proves it for every Li-Garside category with trivial units under (Acyc), including non-graded ones such as pointed-cube categories.
  perron-substitution-finiteness-for-garside-full-groups: that tried to replace (t<d) by a spectral condition on the unstabilized coding, and its proof fails; this replaces it by stabilizing, where packing is automatic.
---

**ESTABLISHED** (revised 2026-09-18: the link lemma is now proved directly; cross-check by bh-ref-q115-b pending) through `cuntz-stabilized-garside-full-groups-f-infinity-proof` (lane proof;
X. Li, arXiv:2110.04505v2, §§`s:GarsCat-TFG`, `s:Fn`, read at source; not independently
reviewed; no priority claimed).

**Trust surface (revised 2026-09-18, after referees bh-ref-q115-a and bh-ref-q115-b).**
- The link-lemma step no longer relies on Li's `lem:link:n-conn_3`. Li's written proof of that
  lemma asserts a key element `θ` without argument, and its literal statement fails (§8 of the
  proof). The instance needed here is proved directly: Lemma L of §5, by Dickson's lemma plus
  doubling, due to bh-ref-q115-a.
- (St), (LCM) and lcms for the pure-hole datum are written out in full in
  `cuntz-pure-hole-datum-satisfies-li-st-and-lcm`.
- Imported from Li as stated: `lem:link:n-conn_1`, the deduction of `_2` from `_3`
  (Matui Lemma 6.18, Brown Lemma 4.20), `cor:link:n-conn`, `lem:Stab`, and Witzel's
  `thm:Wit`.
- The whole framework is Li's: bisection categories, Garside maps, the complexes `E(x)` and
  `𝓜_μ`, and the use of Witzel's criterion.

## Statement

**Setting.** `𝔠` is a small category satisfying the standing hypotheses of Li's
`intro:Gars`:
- finitely many objects;
- left cancellative and right cancellative up to `=*`;
- finitely aligned with disjoint mcms, and right Noetherian;
- condition (F);
- a locally finite, `=*`-transverse Garside family `𝔖` with `𝔖 ∩ 𝔠* = ∅`, and every
  `(𝔖^{≤L})^♯` closed under left divisors.

In addition:
- **units are trivial**, `𝔠* = 𝔠⁰`;
- `X ⊆ Ω_∞(𝔠)` is closed and invariant;
- `𝒢 = I_l ⋉ X`, and `G_2` is the Cuntz groupoid on `{x,y}^ℕ`.

**(Acyc).** For every object `v` and every non-unit `σ ∈ 𝔠(v,v)`, the set
`∩_m σ^m·X(v) ∩ X` has empty interior in `X`.

**Theorem.** Under (Acyc), for every object `v_0` and `Y = (X(v_0) ∩ X) × {x,y}^ℕ`, the
topological full group `F((𝒢 × G_2)_Y^Y)` is of type `F_∞`.

No loops, no degree map, no (`t<d`) and no Perron condition are assumed.

## Why this is the right shape

- **The Cuntz colour doubles every cylinder type in one move.** So Li's packing number of
  every object is at least its number of pieces, and (Pack) holds for free.
- **(Acyc) is exactly what a height needs.** It excludes cycles of one-piece refinements.
  Such a cycle is a non-unit endomorphism of an object in Li's bisection category, and
  then no height function exists.
  - Example: the one-loop monoid `ℕ` times `O_2` fails (Acyc).
  - It holds for any 1-graph coding whose boundary `X` has no isolated points, since
    `∩ σ^m X(v)` is one point.
- **The datum matters.** Li's maximal datum on `𝔠 × O_2` has thin cycles (partial Cuntz
  splits), so its packing fails. The proof keeps only cylinders with **pure holes**,
  which no Cuntz move ever creates. This sharpens `thin-cycles-decide-li-packing`:
  (Pack) is a property of the datum, not of the groupoid.

## Consequences

1. **Loops are unnecessary after stabilization.** For degree categories and `k`-graphs
   with trivial units and (Acyc), the finite presentation hypothesis of
   `finitely-coded-cantor-actions-give-type-a-hosts` now holds without Li's two-loop
   condition. In the torsion-free case, the power-and-phase step of
   `tree-lattice-kgraph-power-phase-proof` becomes unnecessary.
2. **BBCMP Q1.15 loses its finiteness gate.** Let `G` act freely and cocompactly on a
   CAT(0) cube complex, and take the pointed-cube category `C_X` of
   `cubulated-groups-act-by-bisections-of-a-pointed-cube-category`. It satisfies every
   hypothesis above except possibly (Acyc):
   - `pointed-cube-categories-are-li-garside-categories` gives the Li-Garside hypotheses;
   - units are trivial by freeness.

   So `F((𝒢_X × G_2)_Y^Y)` is of type `F_∞` whenever (Acyc) holds on a closed invariant
   `X` that carries the action. What remains for Q1.15 is recorded on
   `virtually-torsion-free-cubulated-groups-satisfy-boone-higman` (Attempt 7):
   - (G1) a closed invariant `X` on which `G` acts faithfully by global bisections;
   - (G2) (Acyc) on `X`;
   - (G3) comparison or minimality, to pass from `F_∞` to a type (A) or simple host.
3. **Calibration.** For the raw reduced-word coding of `F_k`, the theorem gives
   `F(G_{F_k} × G_2)` of type `F_∞`. That agrees with Li's `cor:ProdGraphs`, which reaches
   it through Matui's recoding. Here no recoding is needed. The Cuntz factor does the
   recoding's work.

## Lesson for general BH

Stabilizing by the Cuntz groupoid turns the hard half of Li-type finiteness (merge packing,
the half that fails along thin cycles) into a triviality: every piece can be merged with a
copy of itself. What is left is purely order-theoretic:
- a height, which exists iff no clopen set is carried into itself by a loop of the coding;
- Li's lattice hypotheses, which any geodesic combing with median joins has.

So **every finite Garside coding of a Cantor action gives an `F_∞` host after one Cuntz
stabilization.** The finiteness wall for higher-rank hosts (cubulated groups, non-product
codings, deterministic automata) is gone. The remaining gates are dynamical: a closed
invariant set with a bisection action, no invariant open set beyond a loop, and comparison.
