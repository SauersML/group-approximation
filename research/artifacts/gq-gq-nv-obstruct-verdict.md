# Brin–Thompson and twisted Brin–Thompson hosts for GL_n(Q): verdict (lane gq-nv-obstruct, 2026-09-17)

Target: root `gl-n-q-embeds-in-fp-simple-group`. Questions from the lane assignment and from the coordinator:
(a) does `SL_3(Z)` embed in `nV`; (b) can `nV` or twisted Brin–Thompson groups host `GL_n(Q)` for `n >= 3`;
(c) does O4 (no distorted cyclic subgroups, which kills `VA`) extend to `nV`, and does `nV` contain `BS(1,2)` or
`H_3(Z)`?

## 1. Answers

| Question | Answer | Basis |
|---|---|---|
| Distorted cyclic subgroups in `nV`, `n >= 2` | **Yes.** O4 does not extend to `nV`. | Callard–Salo arXiv:2208.00685v2, Thm E (`brin-thompson-mv-contains-a-distortion-element`) |
| `(Q,+) <= nV`, `n >= 2` | **Yes.** O3 does not extend. | Kojima–Sheng arXiv:2603.18410v3, Thm 1.2 (`rationals-embed-in-brin-thompson-group-2v`) |
| `BS(1,2) <= nV` | **Open.** It gates `GL_2(Q)`, `Aff(Q)` and `SL_2(Q)` in plain `nV`. | `bs12-embeds-in-brin-thompson-2v`; `rational-stepping-stones-in-nv-need-bs12-or-heisenberg` |
| `H_3(Z) <= nV` | **Open.** It gates `U_3(Q)` and `GL_n(Q)`, `n >= 3`. | `heisenberg-group-embeds-in-no-brin-thompson-group` (the negation, OPEN) |
| `SL_3(Z) <= nV` | **Open.** This is Zaremsky Problem 2.19(c)/(d). It gates `GL_n(Q)`, `n >= 3`, in plain `nV`. New: "no" follows from the transversal cnd function alone (§5). | `every-gl-n-z-embeds-in-some-brin-thompson-group`, `kazhdan-subgroups-of-brin-thompson-groups-are-finite` (both OPEN); new route `gl-3-z-in-no-nv-via-cnd-transversal` |
| O2 for twisted Brin–Thompson hosts | **Fails.** Every f.g. subgroup of `GL_n(Q)` lies in a f.p. simple `SV_Γ`, and `SV_Γ ⊇ 2V ⊇ Q`. | new node `fg-subgroups-of-gl-n-q-embed-in-fp-simple-twisted-bt-groups` |

**Verdict.**
- **Plain `nV` (n >= 2): alive and open.** It is not excluded by O1–O4. For `n = 2` it is gated by
  `BS(1,2) <= nV`. For `n >= 3` it is also gated by `H_3(Z) <= nV` and `SL_3(Z) <= nV`, which is Zaremsky
  2.19(c). A positive `SL_3(Z)` answer would also make `nV` fail the Haagerup property (Zaremsky 2.7).
  Since `nV` is explicit, natural, finitely presented and simple (survey §4), a plain `nV` host would settle
  both G and G' at once.
- **Twisted Brin–Thompson `SV_Γ`: alive, and with no finitary obstruction at all.** The question for this
  family is exactly `gl-n-q-in-permutational-boone-higman-class` (route `gl-n-q-bh-via-permutational-class`).

## 2. Distortion in nV (coordinator's O4 question)

- Callard–Salo, arXiv:2208.00685v2 (ETDS 44 (2024) 1757–1817), Theorem E, as quoted in
  `brin-thompson-mv-contains-a-distortion-element-citation`: "The Brin-Thompson group mV contains a distortion
  element; indeed there is an element f such that |f^n| = O(log^4 n)." It holds for every `m >= 2`.
- Their Corollary 1.2: "The Brin-Thompson group mV does not act properly on a CAT(0) cube complex for m ≥ 2."
- Kojima–Sheng, arXiv:2603.18410v3, Corollary 4.3 (read from the v3 HTML on 2026-09-17): "The group nV does not
  act on CAT(0) cube complexes properly by isometries for n≥2." Their argument uses the unbounded roots of
  `Q <= nV`.
- So O4 is specific to `VA` (Burillo–Felipe arXiv:2605.09763v1). The distortion `O(log^4 n)` is not the
  exponential distortion of `BS(1,2)`. Whether exponential distortion occurs in `nV` is not known to this lane.

## 3. BS(1,2) and H_3(Z) in nV: literature status

- **Sheng, arXiv:2209.11982.** It claimed that "a selection of the interesting Baumslag-Solitar groups are
  excluded as the subgroups of SV and SV_G". It was **withdrawn** in v2 (2 April 2025), with the comment
  "a flaw in one of the proofs". It must not be cited as an obstruction. Its twisted part could not hold in
  full anyway: BLIW put every Baumslag–Solitar group in the permutational class, hence in some f.p. simple
  twisted Brin–Thompson group.
- **Kojima–Sheng, arXiv:2603.18410v3.** No statement about Baumslag–Solitar groups, Heisenberg groups,
  `SL_3(Z)` or `GL_n(Z)` in `nV`. Checked in the v3 HTML: the only related items are Thm 1.2 and Cor 4.3.
- **Salo's open-problem list** (villesalo.com/openproblems.html, read 2026-09-17). It asks, for the automorphism
  group `Aut_2` of the binary full shift, "Can we embed the 3 × 3 Heisenberg group in Aut₂?" (Q56041295) and
  "Can we embed the Baumslag-Solitar group BS(1, 2) in Aut₂?" (Q47805222), both after Cyr–Franks–Kra–Petite
  2018. These concern `Aut_2`, not `2V`. They show that the analogous questions are open in the neighbouring
  symbolic-dynamics setting.
- No paper found (web search, 2026-09-17) that embeds or excludes `BS(1,2)` or `H_3(Z)` in `nV`, `n >= 2`.

## 4. Lemma (lane proof, not independently reviewed): BS(1,2) in nV needs a drift-free base

Notation of `heisenberg-in-nv-forces-drift-free-central-element`: `s_g` is the offset (slope) cocycle, and for a
`g`-invariant Borel probability measure `μ`, `ρ_μ(g) = ∫ s_g dμ ∈ R^n`. Let `D(g) ⊂ R^n` be the set of all
`ρ_μ(g)`. It is nonempty, compact and convex.

**(i)** `D(g^k) = k D(g)` for `k >= 1`.
- `⊇`: an `g`-invariant `μ` is `g^k`-invariant, and `∫ s_{g^k} dμ = Σ_{j<k} ∫ s_g∘g^j dμ = k ρ_μ(g)`.
- `⊆`: for `g^k`-invariant `ν`, the average `ν' = (1/k) Σ_{j<k} g^j_* ν` is `g`-invariant, and
  `∫ s_{g^k} dν = Σ_j ∫ s_g d(g^j_*ν) = k ρ_{ν'}(g)`.

**(ii)** `D(hgh^{-1}) = D(g)`. By the cocycle identity, `s_{hgh^{-1}}(hp) = s_h(gp) + s_g(p) − s_h(p)`. So for
`g`-invariant `μ`, `ρ_{h_*μ}(hgh^{-1}) = ρ_μ(g)`, and `μ ↦ h_*μ` is a bijection of the invariant measures.

**(iii)** If `hgh^{-1} = g^k` with `|k| >= 2`, then `D(g) = kD(g)` (use `g^{-1}` if `k < 0`), so `D(g) = {0}`.

**Consequences.**
- In any `BS(1,2) = Z[1/2] ⋊ Z` inside `nV`, every nontrivial element of `Z[1/2]` is conjugate to its square,
  so it is drift-free. This also follows from distortion and item 1 of that node.
- **The Kojima–Sheng root towers over a `V`-element never give the translation subgroup of a `BS(1,2)`.** In the
  graph's version (`rationals-embed-in-brin-thompson-group-2v-proof`, radix 2), `s_0 = t × id` fixes
  `(0^∞, y)` with slope `(−1, 0)`, so `D(s_0) ≠ {0}`. Then `D(s_j) = 2^{-j} D(s_0) ≠ {0}` for every root `s_j`.
- The same holds for roots of any `g × id` whose `g ∈ V` has a periodic point of nonzero slope. By the
  revealing-pair description of `V`, that is every infinite-order `g` (cited, not rechecked here).
- **What survives:** the translation part must be a divisible tower over a **drift-free** infinite-order element
  of `nV`, such as a Callard–Salo distortion element. This is the same requirement as for the central element of
  `H_3(Z)`.

## 5. SL_3(Z) in nV: why the V/VA proofs do not transfer, and what route remains

- **O2 for `V`** uses Higman's torsion-free nilpotent theorem (survey Thm 4.4). For `n >= 2` its input fails,
  since `nV` has drift-free distortion. **O2 for `VA`** (survey Rem. 4.12) uses FW of `SL_3(Z)` (Cornulier) and
  the proper Farley action of `V` on a CAT(0) cube complex. For `n >= 2` no proper cubical action exists
  (Callard–Salo Cor 1.2; Kojima–Sheng Cor 4.3), so the argument has nothing to act on.
- The gq-germ-design template (`normal-germ-extensions-of-thompson-v-contain-no-sl3z`) needs, for a base `B`:
  (i) no finite-index `SL_3(Z)` in `B`; (ii) the point germs of `B`. For `B = nV`, (ii) is `Z^n`
  (`nv-point-germ-groups-embed-in-zn-by-slope`), but (i) is the open question itself.
- **Live route to "no"** in the graph:
  - `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup` (OPEN; three live routes need it);
  - together with `triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z` (ESTABLISHED 2026-09-17, not
    reviewed by a verifier lane).

  New route `gl-3-z-in-no-nv-via-cnd-transversal` (this lane). A Kazhdan subgroup `K` has bounded `ψ_1`, so it
  is covered by finitely many left cosets of `T_n`. Each nonempty `K ∩ gT_n` is a coset of `K ∩ T_n`, so
  `[K : K ∩ T_n] < ∞`. Item 3 of the triangular theorem forbids any power of an `SL_3(Z)` root element in
  `T_n`. So the **transversal half alone** (without properness on `T_n`) answers Zaremsky 2.19(c)/(d) with
  "no", and kills plain `nV` for `GL_n(Q)`, `n >= 3`.
- **"Yes" direction.** It needs `H_3(Z) <= nV` with a drift-free central element. Such elements exist
  (Callard–Salo), but no Heisenberg relation has been realized.

## 6. Twisted Brin–Thompson hosts

- `SV_Γ` contains `Γ`, and it contains `kV` for `k <= |S|` (hand check in
  `fg-subgroups-of-gl-n-q-in-twisted-bt-proof`). So it holds `SL_3(Z)`, `BS(1,2)` and `H_3(Z)` whenever `Γ`
  does, and always holds `Q` when `|S| >= 2`.
- Every finitely generated subgroup of `GL_n(Q)` lies in some finitely presented simple `SV_Γ`. So the
  family faces no finitary obstruction. Any proof that `GL_n(Q)` embeds in no such group must use the whole
  countable group, for instance a failure to glue the chain `GL_n(Z[1/m!])`.
- By BFFHZ universality (survey §4.4, last paragraph), this family is universal among finitely presented simple
  groups with faithful highly transitive actions. So deciding it is deciding the permutational form
  `gl-n-q-in-permutational-boone-higman-class`.

## 7. Not done

- No construction of `BS(1,2)`, `H_3(Z)` or `SL_3(Z)` in `nV`, and no unconditional proof of their absence.
- `ψ_1` itself (`brin-thompson-nv-cnd-proper-modulo-triangular-subgroup`) was not attacked. Its recorded
  forced shape: unbounded but `O(log^8 N)` on the Callard–Salo element, and not a finite wall count.
