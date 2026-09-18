# BH swarm lane bh-amenable: amenable inputs beyond solvable (2026-09-18)

## Landed this pass (lane proofs, not reviewed)

| Node | Status | Content |
|---|---|---|
| `aperiodic-full-groups-lift-along-factor-maps` | ESTABLISHED | `[[T]] ↪ [[S]]` whenever `(X,T)` is an aperiodic factor of `(Y,S)` |
| `brin-thompson-groups-contain-full-groups-of-their-elements` | ESTABLISHED | `[[g|_U]] ≤ nV` for `g ∈ nV`, `U` clopen `g`-invariant |
| `smart-trace-full-group-embeds-in-brin-thompson-2v` | ESTABLISHED | the SMART trace subshift's full group lies in `2V`; its commutator subgroup is a Juschenko–Monod group (f.g., infinite, simple, amenable) inside a f.p. simple group |
| `decidable-minimal-subshifts-are-brin-thompson-factors` | OPEN | the realization problem; necessity of decidable language and closure properties proved |
| `decidable-minimal-subshift-full-groups-satisfy-boone-higman` | OPEN | BH for all Juschenko–Monod groups with decidable language; route via realization |
| `computable-grigorchuk-groups-satisfy-boone-higman` | OPEN | BH for all `G_ω`, `ω` computable; route via Matte Bon |

## Inputs imported without reading the primary source

- Minimality and aperiodicity of SMART's moving-tape dynamics (COT 2017), read only as quoted in
  Callard–Salo arXiv:2208.00685v3 §1 (TeX in the gq scratchpad `src/callard-salo`).
- Matui 2006 Theorem 5.4 (finite generation of `[[T]]'` for minimal subshifts).
- Brin (simplicity, finite presentation of `2V`), Hennig–Matucci (finite presentation of `nV`).
- Matte Bon arXiv:1408.0762 (abstract only).

## Priority check (bounded)

arXiv API queries: `abs:"Boone-Higman"` (14 hits, 2013–2026); "topological full group" together with
"finitely presented simple" (0 hits); "topological full group" with Thompson or "finitely presented"
(Matui 1210.5800, Gardella–Tanner 2302.04078, Salo 2103.06663, Li 2110.04505, Matui 1512.01724);
"Brin-Thompson" with amenable (1 hit). None embeds the full group of a minimal subshift in a finitely
presented simple group or in `nV`. Barbieri–Kari–Salo (1603.08715, 2303.17270) treat the full group of
the full shift, which is not minimal. No MathSciNet search.

## Open questions, sharpest first

1. Is every infinite minimal subshift with decidable language Brin–Thompson realizable? A first test
   case is the substitutive (Toeplitz-type) subshift of the first Grigorchuk group's Schreier graphs.
2. Is Matte Bon's `X_ω` of decidable language for computable `ω`? This needs the body of 1408.0762.
3. Which other minimal aperiodic reversible Turing machines exist? Each one gives a new Juschenko–Monod
   group in `2V`, through the SMART argument.
