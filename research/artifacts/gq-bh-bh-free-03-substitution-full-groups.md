# bh-free-03: topological full groups of substitution subshifts embed in finitely presented simple groups

Lane bh-free-03 (free lane, Cantor dynamics), 2026-09-18. The proofs are the lane's own and have not been reviewed.

## 1. BBMZ inputs, read at source

Source: arXiv:2309.06224v3, TeX `hyperbolic_boone_higman.tex`, fetched through the arXiv e-print on MSI. Local copy: `$GQ/src/bh-free-03/bbmz2-2309.06224.tex`. Line numbers refer to that file.
- **SFT (l. 282):** `Σ_Γ` is the set of infinite directed paths in a finite directed graph `Γ`.
- **Cones and similarities (l. 318–332):** `C_α` is the cone of a finite path `α`. The canonical similarity `C_α -> C_β` for `t(α) = t(β)` is `αω ↦ βω`.
- **Local action (l. 334):** `f(α·ω) = ō_f(α)·f|_α(ω)`, where `ō_f(α)` is the greatest common prefix of `f(C_α)`. **Rational (l. 362):** finitely many distinct local actions.
- **Lemmas `restrict_twice` (l. 392) and `restrict_composition` (l. 413):** `(f|_α)|_β = f|_{αβ}` and `(f∘g)|_α = (f|_{ō_g(α)} ∘ g|_α)|_{t(α)}`.
- **Thompson group `V_{Γ,E}` (l. 476):** homeomorphisms of `E` that are canonical similarities on the pieces of two cone partitions.
- **Irreducible core (l. 513):** an induced subgraph `Γ_0` such that (1) `Σ_{Γ_0}` is irreducible (strongly connected, not a directed cycle); (2) every node reaches `Γ_0`; (3) every path of some length `N` ends in `Γ_0`.
- **Full (l. 556):** `[[G|X]]` is the group of homeomorphisms locally agreeing with `G`.
- **RSG (l. 636):** a subgroup of `R_{Γ,E}` realizing every canonical similarity between proper cones.
- **Prop. `RSGsAndV` (l. 642):** with an irreducible core, "`V_{Γ,E}` is an RSG, as is any subgroup of `R_{Γ,E}` that contains `V_{Γ,E}`."
- **Def. contracting (l. 694):** `Nuc_f` is the set of local actions occurring infinitely often, and `Nuc_G = ⋃_{g∈G} Nuc_g`. `G` is contracting if `Σ_Γ` has an irreducible core and `Nuc_G` is finite.
- **Prop. `NucleusHasProperties` (l. 735):** the nucleus of an RSG is a nucleus of injections.
- **Thm `RSGCharacterization` (l. 770):** for a nucleus of injections `N`, `{f ∈ R_{Γ,E} : Nuc_f ⊆ N}` "is a full RSG with nucleus `N`, and every full RSG has this form."
- **Thm `fin_pres` (l. 840):** "Every full, contracting RSG is finitely presented."
- **Prop. `contr_to_simple` (l. 1752):** "Every full, contracting RSG embeds into a finitely presented simple group." Its proof (l. 1833) uses Zaremsky's action criterion: the host is `SV_G` for the action on the orbit of a rational point.

## 2. DHS inputs, read at source

Source: arXiv:0807.3621 (ETDS 1999), local copy `$GQ/src/bh-free-03/dhs/`.
- **Theorem 1 (section0.tex, l. 88):** the Bratteli–Vershik systems of stationary, properly ordered diagrams are, up to isomorphism, the disjoint union of the substitution minimal systems and the stationary odometers.
- **Prop. 20 (section5.tex, l. 9):** "The system associated to any (primitive, aperiodic) substitution is isomorphic to the system associated to some stationary, properly ordered Bratteli diagram."
- **Lemma 9 (section1.tex, l. 588, Forrest):** a stationary properly ordered diagram is equivalent to one with no multiple edges between levels 0 and 1.
- **Prop. 8 (section1.tex, l. 577, [HPS Thm 4.7]):** equivalent diagrams give pointedly isomorphic systems.
- **Lemma 15 (section3.tex):** "The substitution σ read on B is primitive and proper." In DHS, proper means that for some `p` the first and last letters of `σ^p(a)` do not depend on `a`.
- **Lane remark (telescoping):** telescoping a stationary diagram to the levels `0 < 1 < 1+p < 1+2p < ...` gives a stationary properly ordered diagram. It keeps the level-1 top edges, and its read substitution is `σ^p`, because the ordered paths of length `p` ranging at `V(n+p,a)` read `σ^p(a)`. Taking `p` to be a large multiple of the DHS exponent gives constant first letter `l`, constant last letter `r`, and all lengths `>= 2`.

## 3. The argument

The nodes, in dependency order:
1. `substitution-subshifts-have-stationary-bv-models`: the DHS inputs of §2.
2. `stationary-vershik-maps-generate-contracting-rsgs` (+ `-proof`): the Vershik map `T` is rational with `Nuc_T` of size at most `2|A|`.
   - `T` is singular only at `x_max`, and `T^{-1}` only at `x_min`.
   - Every element of `<V_{Γ,E}, T>` is locally a canonical similarity, except at finitely many points, where it is `c_1 T^{±1} c_2`.
   - This rests on two germ facts: no canonical similarity joins `x_min` to `x_max` (different tails), and `T^{-1} (depth shift at x_min) T` is a depth shift at `x_max`.
   - So the nucleus is contained in `{id} ∪ Nuc_T ∪ Nuc_{T^{-1}}`.
3. `contracting-rsgs-embed-in-fp-simple-groups` (+ `-citation`): the BBMZ imports of §1.
4. `substitution-subshift-full-groups-satisfy-boone-higman` (+ `-proof`): `[[S]] ≅ [[T]] <= G_N <= SV_{G_N}`.

**Checks done.**
- **Odometer calibration** (`A = {a}`, `σ(a) = a^d`, `l = r = a`): `x_min = r_a (a,1)^∞` and `x_max = r_a (a,d)^∞` have different tails because `d >= 2`. `Nuc_T = {id, τ}` with `τ` the adding-machine recursion. This matches the Röver–Nekrashevych group of the odometer.
- **Fibonacci** (`a -> ab, b -> a`): after DHS's return-word recoding and telescoping, the argument applies unchanged. Only primitivity, aperiodicity and the telescoped properness are used.
- **Where it breaks:** non-stationary diagrams. The local action of `T` at `M(v,k)` then depends on the tail from level `k`, so `T` is not rational.

## 4. Priority

- The arXiv API search `all:"topological full group" AND all:"finitely presented simple"` returned 0 hits.
- The Boone–Higman abstract listing (14 entries, through 2609.01868) has no entry on topological full groups, subshifts or minimal systems.
- The BBMZ TeX mentions no Vershik maps, Bratteli diagrams or substitutions (grep).
- Not checked: Nekrashevych's book *Groups and topological dynamics*, and his work on expanding groupoids. Experts may view this as a direct application of BBMZ Theorem C. No priority is claimed, and MathSciNet was not searched.

## 5. Open questions and next directions (lane's own)

- **All minimal subshifts?** A general minimal subshift has non-stationary Bratteli–Vershik diagrams, so its Vershik map is not rational. Question: for a subshift with decidable language, is there another Cantor coding, or a hosting groupoid, in which `[[S]]` becomes contracting? `bh-amenable` owns the general Juschenko–Monod question.
- **S-adic systems** driven by an automatic sequence of substitutions: the local actions might be finite-state in a larger SFT, with states recording the automaton. This is the lane's next attempt.
- **Two-dimensional analogues** (Z^2 substitution tilings) would need a 2-dimensional "Vershik" action; RSGs over Brin–Thompson-type SFTs are a candidate host.
