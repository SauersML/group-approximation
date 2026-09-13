# Nonexistence side of Zaremsky Problem 1.10, part 1: census of candidate classes and two elementary no-gos

Lane `z1-10-simple-amen-block`, 2026-09-13.
- Root `zaremsky-1-10-fp-infinite-simple-amenable-group`; negation `no-fp-infinite-simple-group-is-amenable`;
  existence claim `fp-infinite-simple-amenable-group`.
- Part 2 (`research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part2.md`) proves that finite presentation
  of the alternating full group of a free subshift, over any finitely generated group, forces finite type.

## 0. Outcome

- **Theorem 1.** A finitely generated infinite simple group is not elementary amenable (Chou 1980). Section 2 gives a
  self-contained proof.
- **Theorem 2.** A nontrivial finitely generated group of orientation-preserving piecewise-projective homeomorphisms
  of a compact interval maps onto a nontrivial metabelian group. So no nontrivial finitely generated simple group lies
  in `PL_+[0,1]`, in Thompson's `F`, or in the piecewise-projective group of a compact interval (Section 3).
- **Census (Section 1).** Every recorded class of candidates is dead except three: free minimal SFTs over one-ended
  amenable groups (Labbé, Penrose), non-free or non-expansive groupoid hosts, and candidates with no dynamical model.

Nothing here settles Problem 1.10.

## 1. Census

| Candidate class | Status | Killing reason | Node |
|---|---|---|---|
| Elementary amenable groups | dead | Theorem 1 | `fg-infinite-simple-groups-are-not-elementary-amenable` |
| Residually finite groups: finitely generated linear groups (Malcev), groups acting faithfully on locally finite rooted trees (automaton, branch, self-similar groups) | dead | an infinite simple group has no nontrivial finite quotient | elementary |
| LEF groups and their subgroups | dead | a finitely presented LEF group is residually finite | `finitely-presented-lef-groups-are-residually-finite` |
| Groups with a non-abelian free subgroup, and compressible groupoid hosts (`T`, `V`, Higman–Thompson, Brin–Thompson, Röver–Nekrashevych, one-sided SFT full groups, Leavitt unit groups, Burger–Mozes lattices) | dead | not amenable | `amenable-full-group-forces-invariant-measure`; Status of `fp-infinite-simple-amenable-group` |
| Subgroups of `PL_+[0,1]`, of `F`, of piecewise-projective groups of a compact interval | dead | Theorem 2 | `fg-simple-projective-interval-groups-are-trivial` |
| Finitely generated subgroups of full groups of minimal `Z`-subshifts (Juschenko–Monod groups, Nekrashevych's periodic fragmentations) | dead | periodic approximations; Grigorchuk–Medynets LEF | `periodic-approximable-subshifts-host-no-fp-simple-group` |
| Full groups of minimal topologically free residually finite actions (odometers, boundary actions on rooted trees) | dead | Ma's LEF theorem | `residually-finite-minimal-actions-have-lef-full-groups` |
| Alternating full groups of free subshifts not of finite type, over any finitely generated group | dead | Part 2, Theorem G | `fp-alternating-full-groups-of-free-subshifts-force-sft` |
| Alternating full groups of free subshifts over finitely presented groups with undecidable word problem | dead, conditional | Theorem G and Jeandel's theorem (Section 4) | remark only |
| Free minimal SFTs over one-ended amenable groups (Labbé's `Omega_U`, Penrose tilings) | LIVE | amenability and finite presentation both open | `labbe-shift-derived-full-group-is-amenable`, `labbe-shift-derived-full-group-is-finitely-presented`, `penrose-derived-full-group-is-not-finitely-presented` |
| Non-free or non-expansive groupoid hosts (recurrent groupoids of Juschenko–Nekrashevych–de la Salle, germ groupoids with isotropy) | LIVE | no recorded obstruction | case (S2) in `fp-infinite-simple-amenable-group` |
| Candidates with no dynamical model | LIVE | only isolation in the space of marked groups | `no-fp-infinite-simple-group-is-amenable` |

Two rows are not dead but tie 1.10 to other problems:
- **Intermediate growth.** A finitely presented infinite simple group of intermediate growth would be amenable, and
  also a finitely presented group of intermediate growth, which Grigorchuk asked for (recorded open; not re-checked
  here). Nekrashevych's simple groups of intermediate growth fall under the minimal `Z`-subshift row.
- **Torsion.** A periodic example would also answer Problem 1.11.

## 2. Theorem 1: finitely generated simple groups are not elementary amenable

**Definitions.**
- `EG` is the smallest class of groups containing all finite and all abelian groups and closed under subgroups,
  quotients, extensions and directed unions.
- The statement is due to Chou, "Elementary amenable groups", Illinois J. Math. 24 (1980), 396–407. Chou's paper
  was not re-read; the proof below is self-contained.
- A *section* of `G` is a quotient `H/K` with `K ◁ H ≤ G`.
- `𝒞` is the class of groups `G` such that every finitely generated simple section of `G` is finite or abelian.

**Lemma 2.1.** `𝒞` contains all finite and all abelian groups, and it is closed under subgroups, quotients,
extensions and directed unions. Hence `EG ⊆ 𝒞`.

*Proof.*
1. **Base.** Sections of finite groups are finite, and sections of abelian groups are abelian.
2. **Subgroups and quotients.** A section of `L ≤ G` is a section of `G`. A section of `G/M` has the form
   `(H/M)/(K/M) ≅ H/K` with `M ≤ K ◁ H ≤ G`, so it is a section of `G`.
3. **Extensions.** Let `N ◁ G` with `N, G/N ∈ 𝒞`, and let `S = H/K` be a finitely generated simple section of `G`.
   - `(H ∩ N)K/K` is normal in `H/K`, because `H ∩ N ◁ H`. By simplicity it is trivial or everything.
   - If `H ∩ N ≤ K`: `S` is a quotient of `H/(H ∩ N) ≅ HN/N ≤ G/N`, so `S` is a section of `G/N`.
   - If `(H ∩ N)K = H`: `S ≅ (H ∩ N)/(H ∩ N ∩ K)` is a section of `N`.
   - Either way `S` is finite or abelian.
4. **Directed unions.** Let `G = ⋃_i G_i` be a directed union with every `G_i ∈ 𝒞`, and `S = H/K` a finitely
   generated simple section of `G`.
   - Pick `h_1, ..., h_m ∈ H` whose images generate `S`, and `i` with every `h_j ∈ G_i`. Put `H_0 = <h_1, ..., h_m>`.
   - `H_0 K/K` is a subgroup of `S` containing its generators, so `H_0 K = H`.
   - Then `S = H_0 K/K ≅ H_0/(H_0 ∩ K)`, a section of `G_i`, so `S` is finite or abelian. ∎

**Theorem 1.** A finitely generated infinite simple group `G` is not elementary amenable.

*Proof.* `G` is a finitely generated simple section of itself. It is not finite, and it is not abelian, since an
abelian simple group is cyclic of prime order. By Lemma 2.1, `G ∉ EG`. ∎

**Model tests.**
- The finitary alternating group on a countable set is infinite, simple and locally finite, hence elementary
  amenable. It is not finitely generated, so the hypothesis cannot be dropped.
- `Z/p` is abelian, simple and elementary amenable, which the lemma allows.

## 3. Theorem 2: piecewise-projective interval groups have no finitely generated simple subgroups

**Setting.**
- `I = [a, b]` is a compact interval.
- `PP_+(I)` is the group of orientation-preserving homeomorphisms `g` of `I` with a subdivision
  `a = p_0 < p_1 < ... < p_k = b` such that on each `[p_(i-1), p_i]`, `g` agrees with a real projective map
  `x -> (αx + β)/(γx + δ)`, `αδ − βγ = 1`, with no pole in that interval.
- Affine pieces are projective, so `PP_+(I)` contains `PL_+(I)` and hence Thompson's `F` on `[0, 1]`.

**Theorem 2.** Let `G ≤ PP_+(I)` be nontrivial and generated by a finite set `S`. Put
`c = inf ⋃_(s ∈ S) supp(s)`, where `supp(s) = {x : s(x) ≠ x}`. Then:
- `G` fixes `c`;
- taking the germ at `c` from the right gives a homomorphism `∂ : G -> B`, where `B` is the group of real projective
  maps fixing `c`;
- `B` is metabelian and `∂(G) ≠ 1`.

*Proof.*
1. **`c` is fixed.** Every `s ∈ S` fixes `[a, c)` pointwise, so `G` does, and by continuity `G` fixes `c`. If
   `c = a`, `G` fixes `c` because homeomorphisms of `I` fix the endpoints. Since `G ≠ 1`, `c < b`.
2. **Germs.** For `g ∈ G` there are `ε > 0` and one projective map `P_g` with `g = P_g` on `[c, c + ε)`.
   - A projective map is determined by its restriction to any nondegenerate interval, so `P_g` is well defined.
   - `P_g(c) = g(c) = c`, so `P_g ∈ B`.
   - Each `h ∈ G` fixes `c` and is increasing, so it maps a small `[c, c + ε')` into `[c, c + ε)`. Hence
     `P_(gh) = P_g P_h`, and `∂(g) = P_g` is a homomorphism.
3. **`B` is metabelian.** Conjugating by `x -> −1/(x − c)` moves `c` to `∞`. The projective maps fixing `∞` are the
   affine maps `x -> λx + μ` with `λ > 0`. Their commutators are translations, which commute.
4. **`∂` is nontrivial.** `c` is the infimum of the union of finitely many supports, so some `s ∈ S` moves points in
   every interval `(c, c + ε)`. If `P_s` were the identity, `s` would fix some `[c, c + ε_s)`. ∎

**Corollary 2.2** (`fg-simple-projective-interval-groups-are-trivial`). Every finitely generated simple subgroup of
`PP_+(I)` is trivial.

*Proof.*
1. Let `G` be such a subgroup and suppose `G ≠ 1`. `ker ∂` is a proper normal subgroup, since `∂(G) ≠ 1`, so it is
   trivial by simplicity.
2. So `G ≅ ∂(G)` is metabelian and simple, hence cyclic of prime order.
3. `PP_+(I)` is torsion-free: if `g ≠ id`, some `x` has `g(x) ≠ x`, and then the orbit of `x` is strictly monotone. ∎

**Consequences and model tests.**
- No infinite simple group of Problem 1.10 lies in `F`, in `PL_+[0,1]`, or in `PP_+(I)`. Amenability of `F` would
  not supply a candidate inside `F`.
- `F'` is simple, infinite and not finitely generated. Every finite subset of `F'` fixes neighbourhoods of `0` and
  `1`, since `F'` is the kernel of the endpoint-slope homomorphism `F -> Z^2` (Cannon–Floyd–Parry).
- Thompson's `T` is finitely generated, infinite and simple. It acts on the circle, where the argument has no fixed
  endpoint to start from.

## 4. Remark: finitely presented acting groups with undecidable word problem

- Jeandel, arXiv:1501.06831, abstract (read from the arXiv page on 2026-09-13): "If a finitely presented group `G`
  admits a strongly aperiodic SFT, then `G` has decidable word problem."
- A nonempty SFT with free action is a strongly aperiodic SFT. So, combined with Theorem G of part 2: if `Λ` is
  finitely presented with undecidable word problem, then for every nonempty free subshift `X ⊆ A^Λ` the alternating
  full group `A([[Λ ~ X]])` is not finitely presented.
- Only the abstract was read, so this stays a remark, not a node.
- A fetched abstract of Cohen, arXiv:1412.4572, on strongly aperiodic SFTs over multi-ended groups came back garbled
  (it contradicted the case `Z`), so no ends-based corollary is recorded.

## 5. What is left

- **(L1) Free minimal SFTs over one-ended amenable groups.** By Theorem G, finite type is necessary. The quantum
  rigidity crux for Labbé's shift is being worked on main by the UN lanes; this lane does not duplicate it.
- **(L2) Non-free or non-expansive groupoid hosts.** Theorem G and the periodic-approximation theorem both need a free
  subshift model.
- **(L3) Candidates with no dynamical model.** Only isolation constrains them.
