# sk-sturmian-growth: plan and first reduction (2026-09-14)

Lane sk-sturmian-growth. The problem is Cornulier's Bourbaki 1064 question 7 beyond dyadic subshifts: does [[φ]]′ have uniform exponential growth for Sturmian subshifts, or for every infinite minimal subshift?
- The dyadic case is settled negatively (sk-cornulier-q7): `dyadic-substitution-derived-full-groups-non-uniform-growth`, PASS by sk-verify-16 and sk-verify-17.
- The open node is `topological-full-group-derived-uniform-exponential-growth`.

## 1. What the dyadic proof actually uses
Reading sk-cornulier-q7 parts 1–2 line by line, the substitution enters only through two properties at infinitely many scales m:
- **(H1) constant dyadic towers.** A clopen V_m with X = ⊔_{i<2^m} T^iV_m and T^{2^m}V_m = V_m. This is used for the level model (part 1 §2) and for cutting good sets into three consecutive levels (Step 3).
- **(H2) bounded induced alphabet.** A clopen partition 𝒫_m of V_m with |𝒫_m| ≤ K, whose translates under S_m = T^{2^m}|V_m generate the clopen algebra of V_m.
  - It is used for the type-4 generators ζ_a (a ∈ 𝒫_m) and for the Boolean closure in Step 2(b).
  - In the count it gives the per-point group (Z/3)^K × Z, contributing (3^K(2ℓ+1))^{Cℓ^α}.

Nothing else about ζ is used. The self-conjugacy (V_m,S_m) ≅ (X,T) only supplies (H2) with K = |A|.

**Theorem Q′ (established, unreviewed; node `dyadic-tower-subshift-full-group-non-uniform-growth`).** Let (X,T) be an infinite minimal subshift satisfying (H1) and (H2) for some K and infinitely many m. Then ω([[T]]′) = 1, and [[T]]′ has exponential growth.
- Proof: parts 1–2 verbatim with m = n+3 ranging over the good scales, A replaced by 𝒫_m, and |A| replaced by K.
- The generating sets have size 20166 + K, and C, β depend only on K.

## 2. Why Sturmian subshifts escape: no constant towers
**Lemma O (routine).** If X = ⊔_{i<N} T^iV with T^NV = V and N ≥ 2, then f = Σ_j e^{2πij/N} 1_{T^jV} is continuous with f∘T = e^{2πi/N}f. So e^{2πi/N} is a continuous eigenvalue, V is T^N-invariant, and T^N is not minimal.
- A Sturmian subshift X_α (α irrational) is an almost one-to-one extension of the rotation by α. Its continuous eigenvalues are e^{2πikα}, with no nontrivial root of unity, so it is totally minimal.
- So (H1) fails at every scale.
- The same holds for every totally minimal subshift, e.g. weakly mixing subshifts and codings of irrational interval exchanges. Only systems with an odometer factor of dyadic type can satisfy (H1).

What Sturmian subshifts do have is Rauzy renormalization.
- For every n there is a Kakutani–Rokhlin partition with two towers, of heights q_n and q_{n−1} (continued-fraction denominators), over a base W_n = A_n ⊔ B_n.
- The first-return system on W_n is again a Sturmian coding, of slope G^n(α) (Gauss map), with letter partition {A_n, B_n}. So a bounded induced alphabet (K = 2) holds at every scale, but with two heights.

## 3. Routes for the Sturmian case
- **R1 (two-height level models).**
  - Replace Y_n = {0,1}^n × {1,…,8} by the hierarchical level set of the Rauzy towers: tower A_{n+1} is the concatenation A_n^{a_{n+1}}B_n, and B_{n+1} = A_n.
  - The levels form a spherically non-homogeneous "S-adic" rooted structure. One needs a group of level permutations with intermediate growth acting on it with separation and connectivity (analogues of SS2–SS5).
  - Candidates: Grigorchuk groups G_ω on binary trees, embedded along a dyadic sub-block of each tower, with remainder levels attached; or Šunić-type groups on spherically homogeneous trees of bounded branching.
  - The obstacle is the remainder levels: bounded linking generators cannot reach unboundedly many remainder levels unless the remainders are themselves organized by the renormalization.
- **R2 (only a dyadic block, remainder absorbed by the base).**
  - Use a KR partition whose towers all have heights in a set {h, h+1, …} and choose sheets inside a common dyadic block of 8·2^m levels.
  - Absorb the remainder levels into the base structure: treat "remainder level pieces" as clopen subsets of a larger base V′ carried by the shift pair.
  - This needs a variant of Step 3 where good sets meeting remainder levels are moved into the block by twisted 3-cycles of bounded twist.
- **R3 (uniform growth instead).** For unbounded partial quotients the renormalization is not "self-similar at bounded cost". A uniform lower bound would need, in every generating set, a free semigroup at bounded radius, as for elementary amenable groups (Osin) or via ping-pong from the lamplighter subgroups (Matui). Test first on α with a_n → ∞ fast.

**Model tests for any proposed hypothesis.**
- Thue–Morse must satisfy it: (H1) and (H2) hold with K = 2.
- The odometer (not a subshift) must fail it: (H2) fails, since induced alphabets are unbounded.
- A Sturmian X_α with bounded partial quotients is the target case.

## 4. First steps
1. Land Theorem Q′ plus its route, and merge Progress and Attempts onto the open node.
2. At source (MSI): Grigorchuk groups G_ω and Šunić groups on non-binary or spherically homogeneous trees, looking for intermediate-growth bounds and separation properties.
3. Work out R2 for X_α with bounded partial quotients: can the remainder levels be linked by a bounded family of commuting local generators, keeping the per-point group finite-by-cyclic?
