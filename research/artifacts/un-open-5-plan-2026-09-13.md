# un-open-5 plan: which dynamics survives inside the Pestov-type Kazhdan groups

Lane `un-open-5` (open-ended, dynamics lens), 2026-09-13. Plan only; nothing here is established.

## Target
For an infinite minimal subshift `X ⊆ A^Z` and a prime power `q`, put `R_X = LC(X,F_q) ⋊ Z` and
`S_X = EL_3(R_X)/Z`: an infinite, finitely generated, simple, Kazhdan, LEF group
(`simple-kazhdan-lef-group-from-minimal-subshift`). The UN root describes the approximation TYPE, which is
the same for every `X`. This lane asks what the group remembers about the DYNAMICS of `X`.

- **T1 (rigidity of markings, cardinality).** The marked group `(S_X, standard generators)` determines the
  language `L(X)`, since a fixed word `W_w` in the generators is trivial iff `w ∉ L(X)`. So every abstract
  isomorphism class contains at most countably many `S_X`, and there are continuum many pairwise
  non-isomorphic infinite finitely generated simple LEF Kazhdan groups, for every `q`.
- **T2 (computability).** The word problem of `S_X` is Turing equivalent to `L(X)`. For Sturmian `X_α`,
  `L(X_α) ≡_T α`. So every Turing degree is the word-problem degree of an infinite f.g. simple LEF Kazhdan
  group.
- **T3 (orbit equivalence; open).** Conjugacy or flip conjugacy of `X, Y` gives `S_X ≅ S_Y`. Does `S_X ≅ S_Y`
  force strong orbit equivalence? Candidate route: isomorphism theorems for `E_3` over associative rings,
  then algebraic Pimsner–Voiculescu `K_0(R_X) ≅ K^0(X,T)`, then Giordano–Putnam–Skau. Each step must be read
  verbatim, and every firewall recorded.
- **T4 (quantitative LEF; open).** Compare the LEF growth of `S_X` with the complexity function `p_X`. The upper
  bound comes from Rauzy-graph cycles covering all words of length `~r`. The lower bound is the hard side.

## Why it matters
- It turns the measure side of the dichotomy from one example into a continuum. The group carries dynamical
  and computability invariants of the subshift.
- It gives explicit objects with prescribed "complexity" (word-problem degree), all simple, Kazhdan and sofic.
  Before 09-12 no infinite simple sofic Kazhdan group was known.
- It separates what the root sees (approximation type, constant in `X`) from what the isomorphism type sees
  (the language, up to countable ambiguity).

## Not duplicating
- un-measure: builds LEF families and their existence; it does not address isomorphism types or computability.
- un-rf-beyond-free: changes the acting group; this lane stays with `Z`-subshifts.
- un-labbe-ring: the `Z^2` ring; this lane is 1-dimensional.
- un-k1-homology: unit-group MF quotients via K_1. T3 uses only `K_0` as a route, and coordinates if needed.
- un-full-groups-bridge: full groups vs elementary groups; this lane is about isomorphism type and word problems.
- Existing continuum nodes are about non-MF groups (`continuum-nonisomorphic-fg-non-mf`) or extensions
  (`fixed-mf-quotient-kazhdan-extensions-realize-all-word-degrees`), not simple LEF Kazhdan groups.

## Deliverables
1. The T1 artifact plus claims `marked-subshift-elementary-group-determines-language` and
   `continuum-many-simple-kazhdan-lef-groups`, each with its proof route.
2. The T2 artifact plus claims `subshift-elementary-group-word-problem-equals-language` and
   `every-turing-degree-is-a-simple-kazhdan-lef-word-problem`.
3. Open claims for T3 and T4, with Attempts and firewalls.
