# SK review 4, part 4: the swap double (FAIL), the density patch, the universal host, and the index-3 defect

Lane `sk-verify-4`, 2026-09-13. This part covers queue items 4–7, 10–15 and 17, in the coordinator's priority order
(message of ~20:30). Sources were read on main at tips 36350a600c to 55d5916c79.

## 0. Verdicts

| Priority | Node | Verdict |
|---|---|---|
| 1 | `double-swap-embeds-group-in-derived-subgroup` (+ `-proof`) | **FAIL**: false for nonabelian Γ. Demoted: invalidated through `wreath-products-keep-the-abelianization-of-the-base`, `refuted_by` added |
| 1 | `wreath-products-keep-the-abelianization-of-the-base` (sk-sofic-embedding-a) | PASS; wired as invalidator of `double-swap-embeds-group-in-derived-subgroup-proof` |
| 1 | `amenable-groups-embed-in-simple-kazhdan-linear-sofic` | no firing route (it requires the refuted claim); status restated as OPEN |
| 1 | `sofic-universal-envelope-forces-non-lef-simple-kazhdan` | PASS (independent of the swap double) |
| 2 | `tower-simplicity-holds-for-topologically-free-actions` | PASS for simplicity; scope repair applied: "finitely generated" holds only when `R` is |
| 2 | `clopen-towers-at-every-scale-iff-topologically-free` | PASS |
| 2 | `binary-el-simple-iff-minimal-topologically-free` | PASS |
| 3 | `countable-rf-groups-embed-in-simple-kazhdan-lef-groups` | PASS |
| 3 | `universal-simple-kazhdan-lef-groups-exist` | PASS |
| 3 | `no-finitely-generated-group-contains-all-fg-rf-groups` | PASS |
| 3 | `simple-kazhdan-lef-host-for-countably-many-rf-groups` | PASS; duplicates the sk-strong-1 host (see §3) |
| 4 | `rf-groups-have-free-minimal-subshifts-with-finite-models` | defect confirmed in the claim sentence only; repaired to index ≥ 4. Correction to my part 1 §8 |

## 1. The swap double (priority 1)

**The claim.** `ι(γ) = (γ,γ^(-1)) = [(γ,1),s]` embeds every `Γ` in `[Δ,Δ]`, `Δ = (Γ×Γ)⋊C_2`.

**Why it fails.**
- `Γ×Γ` is a direct product, so `ι(γ)ι(δ) = (γδ, γ^(-1)δ^(-1))`, while `ι(γδ) = (γδ, δ^(-1)γ^(-1))`. They agree for
  all `γ, δ` iff `Γ` is abelian.
- The route's repair (second factor read in `Γ^op`) does not help. The involution of `Γ×Γ^op` that exchanges the
  factors is `τ(a,b) = (b^(-1),a^(-1))`; I checked it is multiplicative for the opposite product.
  - Under the isomorphism `Γ×Γ^op → Γ×Γ`, `(a,b) ↦ (a,b^(-1))`, `τ` is the plain swap, and the homomorphism
    `γ ↦ (γ,γ^(-1))_op` is the diagonal `γ ↦ (γ,γ)`.
  - In `Δ^ab = Γ^ab × C_2` the diagonal maps to `2γ̄`, which is nonzero in general, e.g. for `Γ = Z × A_5`.
  - Meanwhile `[(γ,1),s] = (γ,γ^(-1))` in `Γ×Γ` is not the diagonal. So "both give the same subgroup" is false.
- The statement holds exactly for abelian `Γ`. Each `ι(γ)` really is a single commutator; the homomorphism claim is what
  fails.

**The invalidator.** sk-sofic-embedding-a's `wreath-products-keep-the-abelianization-of-the-base`. I re-derived it:
- `Δ = (⊕_Ω Γ)⋊Λ` with `Λ` transitive gives `Δ^ab = Γ^ab × Λ^ab`, because the coinvariants of `⊕_Ω Γ^ab` under a
  transitive action are `Γ^ab`.
- The composite `Γ_ω → Δ^ab → Γ^ab` is abelianization, so `Γ_ω ∩ [Δ,Δ] = [Γ,Γ]_ω`.
- `γ ↦ γ_ω(γ^(-1))_(ω')` is multiplicative iff `Γ` is abelian.

PASS. I added `invalidates: [double-swap-embeds-group-in-derived-subgroup-proof]` to it, and
`refuted_by: [wreath-products-keep-the-abelianization-of-the-base]` to the false claim, both merged onto main's blobs.

**Consumers.**
- `amenable-groups-embed-in-simple-kazhdan-linear-sofic`: its route requires the refuted claim (steps 1 and 7), so it no
  longer fires. I restated the status as OPEN, pointing to the perfect case
  `amenable-perfect-groups-embed-in-kazhdan-linear-sofic` (sk-sofic-embedding-a; queued with me, not yet reviewed).
- `sofic-groups-embed-in-simple-kazhdan-sofic-groups`, `sofic-groups-have-measured-free-minimal-subshifts` and the
  proposal artifact `sk-sofic-embedding-b-proposal-2026-09-13.md` mention the swap double. I did not edit them; the owner
  was told by name.
- `sofic-universal-envelope-forces-non-lef-simple-kazhdan` uses only:
  - LEF passes to subgroups;
  - `BS(2,3)` is finitely presented, residually solvable hence sofic, and not residually finite (non-Hopfian);
  - Vershik–Gordon: finitely presented LEF groups are residually finite.

  PASS. Its route cites `gap-sofic-approximations-are-local-embeddings` only for the witness record.

## 2. The density patch (priority 2)

**`clopen-towers-at-every-scale-iff-topologically-free`.**
- (1)⇒(2): a finite union of closed nowhere dense fixed sets is nowhere dense. A point `x` off it is separated from each
  `γx` by clopens `A_γ ∋ x`, `B_γ ∋ γx`, and `V = U' ∩ ⋂(A_γ ∩ γ^(-1)B_γ)` is `F`-free.
- (2)⇒(1): an `F`-free `V` inside `Fix(γ_0)` has `γ_0V = V`, a contradiction.
- Lemma 2': if `h ≠ 0`, `γ^(-1){h≠0}` contains an admissible `V`, and `h` is nonzero on `γV`.

PASS.

**`binary-el-simple-iff-minimal-topologically-free`.**
- **Scalar step.** Commuting with `e_ij(e_V)` gives `g_(pi)e_V = 0` (`p≠i`), `e_Vg_(jq) = 0` (`q≠j`), and
  `g_(ii)e_V = e_Vg_(jj)`. Here `g_(pi)e_V = Σ f_γ e_(γV)u_γ`, so `f_γ` vanishes on `γV` for every admissible `V`, and
  `f_γ = 0` by Lemma 2'.
  - On the diagonal, for `γ ≠ e`, `γ ∈ B ⊆ B^(-1)B` (since `e ∈ B`) makes `γV` and `V` disjoint, so both sides
    vanish.
  - At `γ = e` the two coefficients agree on all admissible `V`, hence everywhere (Lemma 2).
  - The unit `c ∈ LC(X,F_2)^×` is `1`.
- **Tower.** `ε_(αβ)ε_(α'β') = δ_(βα')ε_(αβ')`, from `(B^(-1)B)`-freeness. `ψ` is injective and multiplicative.
  Products `(fu_α)e_V(f'u_β) ∈ {0, ε_(α,β^(-1))}`, with constancy on atoms and `B` symmetric.
- **Commutator.** `k − I = (ghg^(-1)−h)h` and `k^(-1) − I = h(ghg^(-1)−h)`, in characteristic 2.
- **Rest.** `d = n|B| ≥ 3`; the level ideal; covering by translates via minimality.
- **Backward direction.** `R` is the Steinberg algebra of `Γ⋉X`, and it is simple iff the groupoid is minimal and
  effective (import, reviewed). A proper nonzero ideal `I` gives the nontrivial proper normal subgroup `EL_n(R,I)`: it is
  the kernel side of `EL_n(R) ↠ EL_n(R/I) ≠ 1`.

PASS.

**`tower-simplicity-holds-for-topologically-free-actions`.**
- Route steps 1–5 are correct: dense small sets by Baire; the entrywise criterion for commuting with `e_ij(r)`; `c e_V = 0`
  for all small `V` forces `c = 0`; agreement on a dense set; the tower; the commutator; covering.
- **Scope defect in the claim sentence.** "Then `EL_n(R)` is an infinite, finitely generated simple group" for every
  finitely generated `L` acting minimally and topologically freely on a Cantor set. Finite generation of `EL_n(R)` forces
  finite generation of `R`: all entries of words in finitely many generators lie in the subring `S` they generate, and
  `e_12(r) ∈ EL_n(S)` gives `r ∈ S`.
  - Over an odometer `Z` (minimal and free), `R` is not finitely generated: a finitely generated subring lies in
    `LC_k ⋊ Z` for a level `k`, since the levels are invariant.
- **Repair applied.** "finitely generated whenever `R` is, for instance when `Z` is an `L`-subshift". The route already
  says "G is finitely generated when R is".

PASS after the scope repair.

## 3. The universal host (priority 3)

**sk-strong-1.**
- `countable-rf-groups-embed-in-simple-kazhdan-lef-groups`: Wilson Theorem A gives `G ≤ Ĝ`, 2-generated and residually
  finite. Theorem E (`rf-groups-embed-in-simple-kazhdan-lef-groups`, PASS by sk-verify-3 and me) finishes.
- `universal-simple-kazhdan-lef-groups-exist`.
  - (a) The restricted direct sum of a countable family of countable residually finite groups is countable and residually
    finite, through the coordinate projections.
  - (b) There are countably many recursively presented f.g. groups up to isomorphism. F.g. linear groups are recursively
    presented: `A = Z[x]/I` with `I` finitely generated, and ideal membership over `Z` is decidable (recalled by the owner
    and standard).
- `no-finitely-generated-group-contains-all-fg-rf-groups`: countably many f.g. subgroups against uncountably many f.g. RF
  groups. The Chong–Wise abstract (verbatim) gives residually finite doubles and uncountably many up to isomorphism.
  Grigorchuk's groups would also do.

PASS.

**sk-strong-3.** `simple-kazhdan-lef-host-for-countably-many-rf-groups` is the same composition (direct sum, Wilson,
Theorem E), with the example classes counted correctly. PASS.
- It duplicates `universal-simple-kazhdan-lef-groups-exist` (a), and `wilson-countable-rf-embeds-in-2-generator-rf`
  duplicates `wilson-countable-rf-into-two-generator-rf-groups`: same theorem, same quote, two nodes.
- The two owners should keep one canonical pair and add `distinct_from` or retire the other. I did not merge them.
- I did not re-read the Wilson PDF. Both citation routes quote the same verbatim Theorem A with page and DOI.

## 4. The index-3 defect (priority 4)

At `[K_m:K_(m+1)] = 3` each level has exactly two nonidentity cosets of `K_(m+1)`, valued `1` and `2`, so `x` takes no
value `0`.
- The claim sentence "the configurations equal to `x` off `K_n` and constant on `K_n` generate a finite subshift with the
  `F`-patterns of `X`" is then false: the constant `0` creates patterns with a letter absent from `X`.
- The route uses `b ∈ x(K_n)` and is correct at every index `≥ 3`.
- Freeness and minimality are unaffected. At index 3 the two special cosets are the two nonidentity elements of `Z/3`,
  and exactly one of `κ_1g`, `κ_2g` lies in `K_(m+1)`, which is what the argument needs.

**Repair applied.** The claim now requires index `≥ 4`, so all three letters occur in each `K_n` and every constant
configuration is a model. It also notes that index 3 works with values in `x(K_n)`.
- sk-draft-general's Proposition 2(c) is correct as written: it uses `x(K_n)` with index `≥ 3`.
- sk-draft-rich uses constants `c ∈ {0,1,2}` and index `≥ 4`, which is also correct.
- **Correction to part 1 §8.** My PASS there checked the route, and missed the overclaiming sentence in the claim.
