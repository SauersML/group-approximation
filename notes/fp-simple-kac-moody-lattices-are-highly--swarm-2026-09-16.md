# fp-simple-kac-moody-lattices-are-highly-transitive: swarm lane notes (2026-09-16)

Lane `swarm-fp-simple-kac-moody-lattices-a`. Target: the root claim
`fp-simple-kac-moody-lattices-are-highly-transitive`, BFFHZ Question 3.6 part one.

**Outcome.** Obstruction to one class of constructions. The question stays OPEN.

## Setup

- **The group.** `Λ = 𝒢(F_q)` is a minimal Kac--Moody group over a finite field, of Coxeter type
  `(W,S)`, irreducible, infinite and non-affine for the simple lattices.
- **The completion.** `G` is its completion in the positive building topology (Caprace--Marquis
  §4 = Caprace--Rémy `\overline Λ_+`). `B` is compact open, `(B,N)` is a BN-pair and `P_J` is
  open.
- **Explicit members.** `S_q = Λ_q/Z`, type `(2,4,6)`, `q ≥ 4`
  (`km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`).
- **Building-open.** `M ≤ Λ` is building-open if `Λ ∩ V ⊆ M` for some open `V ≤ G`. Examples
  are chamber fixators, the Borel subgroup `𝓑_+` and parabolics `𝓟_J`.

## What was proved (nodes written)

1. **`km-building-open-subgroups-have-infinite-bi-index`** (route
   `km-building-open-subgroups-bi-index-proof`, `requires: []`). A building-open `M` has finite
   index or infinitely many double cosets. The same holds in `Λ/N` for `N ⊆ Z_Λ(Λ^†)`. When all
   proper `W_K` are finite there is a shorter proof, which avoids the Coxeter step. The proof has
   four steps:
   - **Transfer.** Pass to the closure `O`: `Λ ∩ O = M`, with the same index and double-coset
     count.
   - **Classification.** Caprace--Marquis `thm complet`: `O` is conjugate to a finite-index
     subgroup of some `P_K`.
   - **Bruhat.** `W_K\W/W_K` injects into `P_K\G/P_K`.
   - **Coxeter.** `|W_K\W/W_K| = ∞` for proper `K`, via combinatorial roots, a root-counting
     length bound, and the Caprace--Marquis nesting lemma `wα ⊊ α`.
2. **`km-building-open-subgroups-have-infinite-ht-orbits`** (route
   `km-building-open-ht-orbits-from-bi-index-proof`, requires item 1).
   - **(a)** In a transitive action with finitely many orbitals, point stabilizers contain no
     `Γ_V`.
   - **(b)** In a `2k`-transitive action, `Γ_V`-orbits have more than `k` points.
   - **(b')** In a highly transitive action, all orbits of `Γ_V` and of its finite-index
     subgroups are infinite.
   - **(c)** For primitive actions with finitely many orbitals, the closure of the stabilizer
     preimage is `G` or non-open.
   - **(d)** A subgroup of finite bi-index and infinite index has non-open closure, or open
     closure of finite index.

All proofs are in `research/artifacts/km-building-open-subgroups-bi-index-2026-09-16.md`.

## Candid assessment

- **For `S_q` the theorem is nearly elementary.** `(2,4,6)` is compact hyperbolic, all proper
  parabolics are finite, and Caprace--Marquis Corollary `corintro2` says every proper open
  subgroup of `G` is compact. Compact open subgroups are commensurated, and a commensurated
  subgroup of finite bi-index has finite index. The write-up uses a compactness count (A'), which
  is the same content.
- **The Coxeter step is needed only for other types.** It matters for types with infinite proper
  parabolics, such as hyperbolic non-compact types or higher rank. There it rests on the nesting
  lemma, whose proof in [CM] cites Hée Prop. 8.1, not read.
- **No novelty is claimed.** This may be folklore.
- **The real content for the root question** is (b'). A highly transitive action of these
  lattices cannot have any "building-local" subgroup with a finite orbit. So point stabilizers
  must have non-open closure in both natural completions, if the negative-building analogue
  holds; that analogue was not checked. This rules out the naive approach "take a parabolic or
  a chamber fixator and act on cosets of something containing it".

## Approaches and where each dies

1. **Hull--Osin, through acylindrical hyperbolicity.** Dies: an infinite simple group is not
   SQ-universal (already in the root's Attempts). Rybak's hyperbolic action is lim-free but not
   claimed acylindrical.
2. **Tree-action criteria (Fima--Le Maître--Moon--Stalder, arXiv:2003.11116, high transitivity
   from actions on trees).**
   - **For Kazhdan members.** They die: property (T) implies property (FA), a standard fact not
     re-read this session. So `S_q` has no action on a tree without a fixed point, and no
     nontrivial amalgam or HNN splitting.
   - **For non-Kazhdan members** this obstruction does not apply, but no suitable splitting is
     known.
3. **Linear-group methods.** Die by the Malcev argument: finitely generated linear groups are
   residually finite, and infinite simple groups are not, so these lattices are not linear.
   Garion--Glasner (arXiv:1008.0563) record high transitivity of `SL_n(Z)`, `n ≥ 3`, as open. It
   is the linear analogue, and its current status was not re-checked.
4. **Le Boudec--Matte Bon confined-subgroup obstruction (Ann. H. Lebesgue 5 (2022)).** Dies as a
   route to a negative answer: `kac-moody-lattice-confined-subgroups-are-lim-free-and-mif` shows
   confined subgroups pass all their listed obstructions.
5. **Building-local positive constructions** (this lane). They die by Corollary B:
   - no point stabilizer, or finite-orbit subgroup, can contain a chamber fixator or any `Λ ∩ V`;
   - more generally, no finite bi-index subgroup can have open closure of infinite index.
6. **Boundary-point stabilizers.** The action on a `Λ`-orbit of a point `ξ` of the ideal
   boundary of the Davis realization is not touched. Its stabilizer lies in the closed subgroup
   `G_ξ`, which one expects not to be open for generic `ξ`. Two things were not investigated:
   - whether `Λ_ξ` acts with finitely many orbits on `Λξ × Λξ`;
   - the Le Boudec-type topological freeness obstruction recorded in the root's Attempt 2.

## Open directions

- **The negative-building version of Theorem A.** It should follow by symmetry of twin root
  data; not checked. "Mixed" subgroups `Λ ∩ (V_+ × V_-)` are finite, by discreteness of `Λ` in
  `G_+ × G_-`, and give nothing.
- **Subgroups with non-open closure in both completions.** The only remaining candidates for
  highly transitive stabilizers include discrete subgroups of `G_±`, stabilizers of ideal points,
  and subgroups dense in `G_±`.
- **Extending (A) from `Λ` to `[Λ,Λ]`.** Needed when `Λ` is not perfect, for Caprace--Rémy's
  simple groups `[Λ,Λ]/Z`. The natural route is to show `closure([Λ,Λ]) · B = G`.

## Literature gate (2026-09-16)

**arXiv API queries**, with sleeps between calls, all returning 0 entries:
- `abs:"highly transitive" AND abs:"Kac-Moody"`;
- building and open-subgroup variants.

**Primary sources consulted:**
- **Recent (2024--2026):**
  - Rybak arXiv:2605.14159v3
  - Hyde--Lodha arXiv:2509.09788
  - Caprace--Thom arXiv:2606.27993
  - Flores arXiv:2607.28316
  - Chakraborty arXiv:2607.26267
  - Elliott arXiv:2601.15185
  - Avni--Gelander arXiv:2510.03492
  - Vigdorovich arXiv:2503.12737
  - Bischof arXiv:2504.17513
- **Older:**
  - André--Guirardel arXiv:2212.06020
  - Abramenko--Gates arXiv:1912.05611
  - Garion--Glasner arXiv:1008.0563
  - Glasner--Kitroser--Melleray arXiv:1601.07538
  - Hull--Osin arXiv:1501.04182
  - Fima--Le Maître--Moon--Stalder arXiv:2003.11116
  - Caprace--Rémy arXiv:math/0607664v2 (TeX read)
  - Caprace--Marquis arXiv:1108.4934v2 (TeX read)
- **Via the repo:**
  - Creutz--Peterson arXiv:1311.4513v3
  - Le Boudec--Matte Bon, Ann. H. Lebesgue 5 (2022)

None proves or refutes high transitivity of finitely presented simple Kac--Moody lattices, and
none states Theorem A.

## Files

- `research/artifacts/km-building-open-subgroups-bi-index-2026-09-16.md`
- `research/km-building-open-subgroups-have-infinite-bi-index.md`
- `research/km-building-open-subgroups-bi-index-proof.md`
- `research/km-building-open-subgroups-have-infinite-ht-orbits.md`
- `research/km-building-open-ht-orbits-from-bi-index-proof.md`

No experiments were run.

## Referee (2026-09-16)

**What was checked.**
- **Pins.** Re-fetched the e-prints and re-read the quoted lines:
  - Caprace--Marquis arXiv:1108.4934v2, `OpenKM_rev.tex`: setup l.819--826, l.844, Theorem
    `thm complet` l.907--916, Lemma `lemme racine essentielle` l.782--784 (proof via Hée Prop. 8.1),
    `corintro2` l.152--154 and its proof l.1209, essential subsets l.227, `Φ_J` l.779;
  - Caprace--Rémy arXiv:math/0607664v2, `SimplSuperrigid.tex`: simplicity theorem l.132--136,
    kernel `Z_Λ(Λ^†)` l.511--512, Prop. `prop:TopoCompletions` (ii)--(iii).
  All quotes match. No irreducibility or field-size hypothesis sits in the [CM] §4 setup.
- **Step 1 (transfer).** Re-traced: `MV` clopen, `Λ ∩ O = M`, and the orbit comparison through
  `oS_g ∩ M ≠ ∅`. Correct. It also survives if `G` is read as the effective completion, since
  `ker(Λ → G) ⊆ Λ ∩ V ⊆ M`.
- **Step 2.** `thm complet` applies to any open `O`; the case `K = S` gives finite index.
- **Step 3.** (B1) induction, (B2) iteration of (BN3), (B3) injectivity. Correct.
- **Step 4 (Lemma C).** Re-traced (C0)--(C8): folding, connectivity of `α_s`, cut sets, the
  root-counting bound `ℓ(w) ≥ #{β : 1 ∈ β, w ∉ β}`, and the chain argument. Correct, given the
  imported nesting lemma and the textbook identification (C7).
- **Sanity computation.** Tits representation (exact integers) of the irreducible Coxeter group on
  `{a,b,c,d}` with `m(a,b)=m(b,c)=m(a,c)=m(a,d)=3`, `m(b,d)=m(c,d)=2`, `K = {a,b,c}` (infinite
  affine `Ã_2`). Minimal `(W_K,W_K)`-double coset representatives were found at lengths
  0, 1, 6, 7, 9, 11 (enumeration to length 11), consistent with Lemma C. Script:
  scratchpad only, not landed.
- **(A').** Compactness count re-checked; it needs only `W_K` finite, (BN3), (B1) and `thm complet`.
  `(2,4,6)` is compact hyperbolic, so this covers `S_q`.
- **Corollary B.** (a), (b) (orbit counting on pairs of `m`-subsets, `≤ m+1` orbits), (b'), (c)
  (maximality of stabilizers in primitive actions), (d). Correct.
- **Citations.** arXiv ids in the literature list resolve to the expected titles (spot-checked
  2509.09788, 2607.26267, 2601.15185, 2510.03492, 2504.17513, 1912.05611, 1008.0563, 1601.07538).
  Garion--Glasner arXiv:1008.0563 TeX l.122 does say high transitivity of `SL_n(Z)` is unsolved
  ("it might very well be the case that SL_n(Z) fails to admit such a highly transitive
  permutation representation").
- **Duplicates.** `bin/cairn search --similar` on both claims: no duplicate. All `distinct_from`
  ids exist.

**What was changed.**
- Both claim bodies: "not independently reviewed" replaced by a one-line referee record.
- `km-building-open-subgroups-have-infinite-ht-orbits` (b') and its route: added the one-line
  extension from `Γ_V` to every subgroup containing some `Γ_V` and its finite-index subgroups, which
  the claim title asserts but the body did not state.

**Remarks, not errors.**
- (A'') does not actually need `N ⊆ Z_Λ(Λ^†)`; that hypothesis is only used to make chamber
  fixators of `Γ` into some `Γ_V`.
- The trust surface of the direct proof is: [CM] `thm complet`, the [CM] nesting lemma (only for
  types with infinite proper parabolics), [CR] Prop. `prop:TopoCompletions`, and textbook Coxeter
  and BN-pair facts. For `S_q` the nesting lemma and (C7) are not used.
- The result is a no-go for one class of constructions. It does not decide
  BFFHZ Question 3.6, part one, which stays OPEN.

**Verdict.** Sound as written, with minor clarifying edits. Landed.
