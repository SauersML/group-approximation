# Family-wide calibration: which (A_7, A_7, A_8) hyperbolic triangles have small quotients at all

Lane `ex-hyperbolic-triangle-search`, 2026-09-13. The code is
`experiments/hyperbolic-triangle-search/config.g` (GAP 4.14 on MSI).

## 1. The question

The four candidates `G_1..G_4` have no small quotients. The companion artifacts are
`hyperbolic-triangle-quotient-search-2026-09-13.md` and
`hyperbolic-triangle-linear-search-2026-09-13.md`. Is this a property of these four groups, or of
the whole family they were drawn from? If no member of the family has a quotient in some range,
then zeros in that range say nothing about the candidates in particular.

**The family `F`.** A member of `F` is a triangle of groups with:
- vertex groups `A_7, A_7, A_8`, each given by a generating pair of 7-elements `(x_A, y_A)`,
  `(x_B, y_B)`, `(x_C, y_C)`;
- edge groups `Z/7` identified with any twists `(e_1, e_2, e_3)`, so that
  `G = <p,q,r | R_A(p,q), R_B(q^{e_1}, r), R_C(r^{e_2}, p^{e_3})>`;
- trivial face group;
- link girths `girth Γ(A; <x_A>, <y_A>) = 6`, `girth Γ(B; <x_B>, <y_B>) = 6` and
  `girth Γ(C; <x_C>, <y_C>) = 8`.

Every member is infinite and hyperbolic, of half-girth type `(3,3,4)`. The candidates are members.

## 2. Configurations

**Lemma.** A finite group `S` receives a nontrivial homomorphism from some member of `F` iff `S`
contains a *configuration*: elements `p, q, r` of order 7 with
- `<p,q> ≅ A_7`, `<q,r> ≅ A_7`, `<r,p> ≅ A_8`;
- the coset graphs `Γ(<p,q>; <p>, <q>)`, `Γ(<q,r>; <q>, <r>)`, `Γ(<r,p>; <r>, <p>)` of girths
  `6, 6, 8`.

*Proof.* Suppose `φ: G -> S` is nontrivial. Then `φ` is injective on the simple vertex groups, and
it maps `<p>`, `<q>`, `<r>` onto `<φ(p)>`, `<φ(q)>`, `<φ(r)>`. The subgroup `<q^{e_1}>` equals `<q>`,
and likewise for the other twists. So `(φ(p), φ(q), φ(r))` is a configuration, with the same coset
graphs up to isomorphism.

Conversely, a configuration defines the member with vertex pairs `(p,q)`, `(q,r)`, `(r,p)` and
twists `(1,1,1)`. The inclusions define a homomorphism from that member onto `<p,q,r>`. ∎

So one configuration search covers every member and every twist at once.

## 3. The search

Throughout, the first vertex pair runs over the 108 generating pairs of 7-elements of `A_7` with
coset-graph girth 6, taken up to conjugacy in `A_7`. The first vertex group is placed by its
embedding classes. `r` runs over double cosets exactly as in the completeness lemma of
`hyperbolic-triangle-quotient-search-2026-09-13.md` §2, and the relator test for `C` is replaced by
the configuration test.

**`S = S_n`.** The embedding classes are `A_7`-sets of degree `n`.
- **(natural, natural) pairs are impossible.** Suppose every nontrivial orbit of `A` and of `B` is a
  natural 7-point orbit. Then the `B`-orbits through the cycles of `q` are exactly their supports.
  So `r`, and hence `C = <r,p>`, preserves a 7-set on which `p` acts as a 7-cycle. That is
  impossible for `A_8`.
- **A symmetry halves the search.** `(p,q,r) -> (r,q,p)` exchanges the roles of `A` and `B` and
  fixes `C`. So (natural `A`, non-natural `B`) cases correspond to (non-natural `A`, natural `B`)
  cases.
- **Complete enumeration.** `α` runs over all `A_7`-sets and `β` over those with an orbit of
  degree more than 7.

**Other `S`.** All classes from `AllHomomorphismClasses(A_7, S)`.

**Configuration test.**
- The orders of `rp`, `rp^{-1}`, `r^2p`, `rp^2`, `[r,p]` and `rprp^3` must lie in `{1,2,3,4,5,6,7,15}`.
- `|<r,p>| = 20160`, and `<r,p>` has an element of order 15; this excludes `L_3(4)`.
- `girth Γ(<r,p>; <r>, <p>) = 8`.

**Calibration.**
- **Unit checks** (`cfgcal.g`, `cfgcal.out`). All four candidates pass. Each candidate's `C` pair passes
  the configuration test, and each candidate's `A` and `B` pair is `A_7`-conjugate to one of the 108 listed pairs.
  The full-slice positive control in the same file was stopped after 15 minutes without output and is
  superseded by the next item.
- **Positive control** (`cfgcal_narrow.g`, `cfgcal_narrow.out`).
  - **Setup.** The literal `(A_7,A_7,A_7)` triple of `tri_cal2.g` has pairwise link girths `6, 6, 6`.
    Its pairs `(p,q)` and `(q,r)` are listed pairs number 44 and 21.
  - **Run.** Same pair list, same `A_7`-set construction and same double-coset core. The configuration
    test is replaced by "`<r,p> ≅ A_7` with girth 6", and the run is restricted to those two pairs and to
    15-point `A_7`-sets in `S_15`.
  - **Result.** 392 double cosets, 12 configurations found; at least 1 was required. So the enumeration
    finds configurations when they exist.

## 4. Results

| `S` | `α` sets | `β` sets | double cosets | configurations | time |
|---|---|---|---|---|---|
| `S_15` | 432 | 216 | 5,715,360 | 0 | 171 s |
| `S_16` | 432 | 216 | 10,287,648 | 0 | 295 s |
| `S_17` | 432 | 216 | 10,287,648 | 0 | 528 s |
| `S_18` | 432 | 216 | 10,287,648 | 0 | 860 s |
| `S_19` | 432 | 216 | 10,287,648 | 0 | 1434 s |
| `S_20` | 432 | 216 | 10,287,648 | 0 | 1545 s |
| `S_21` (types `21`, `7+7+7` added) | 648 | 324 | 38,292,912 | 0 | 2571 s |
| `L_5(2)` (2 classes of `A_7`; `|C(t)| = 42`) | 216 | 216 | 979,776 | 0 | 34 min |
| `O_8^-(2)` (1 class; `|C(t)| = 21`) | 108 | 108 | 81,648 | 0 | 114 s |
| `Sp_8(2)` (2 classes; `|C(t)| = 42`) | 216 | 216 | 734,832 | 0 | 14 min |
| `O_8^+(2)` (3 classes; `|C(t)| = 7`) | 324 | 324 | 734,832 | 0 | 16 min |
| `L_6(2)` (3 classes; 5 classes of 7-elements) | 324 | 324 | 1,714,608 | 0 | 42 min |

An earlier `S_15` run that took only non-natural `α` examined 4,572,288 double cosets and also found 0
(`job_cfg_sn_nonnatural_only.out`). The `n = 22` run was stopped, because the estimate was about `2·10^8` double cosets.

## 5. Consequence

**Computational conclusion (complete enumeration, unreviewed).** No member of `F` has a nontrivial
homomorphism into any of the following:
- `S_n` for `n <= 21`, so no finite group with a faithful permutation representation of degree at
  most 21;
- `L_5(2)`, which contains `A_8 = L_4(2)`;
- `O_8^+(2)`, which contains `A_9` and `Sp_6(2)`, and `O_8^-(2)`;
- `L_6(2)`, which contains `L_5(2)`;
- `Sp_8(2)`, which contains `Sp_6(2)`.

**How each range is settled.**
- For `n <= 13`: the support argument.
- For `n = 14`: the orbit-type argument.
- Otherwise: this search.

**The 4-type reduction.** In characteristic 2, suppose the vertex groups act on `V = F_2^d` as
`4 ⊕ 1^{d−4}`, which is semisimple because `H^1(A_7, 4) = H^1(A_7, 4*) = H^1(A_8, 4) = 0`.
- The spaces `W_X = [V, X]` are 4-dimensional, and `W_A ∩ W_C ⊇ [V,p]` has dimension 3.
- If two of the `W_X` coincide, the image lies in `GL_4(2) = A_8`, which contains no configuration.
- Otherwise `U = W_A + W_B + W_C` has dimension 5 and is `G`-invariant.
- So the `L_5(2)` zero excludes, for every member of `F` and every `d`, all such representations over `F_2`.

So for `n <= 16` the candidates' permutation zeros are forced for the whole family. They carry no
information about `G_1..G_4` in particular. Evidence specific to a candidate can only come from
quotients that some member of `F` actually has. The first open question for calibration is therefore
whether any member of `F` has a finite quotient in a searchable range.

## 6. Linear power calibration on random members (`sample_members.g`, `stat_lin.py`)

`members.py` holds 150 random members of `F`. Each has independent random girth-6 pairs of `A_7`
for `A` and `B`, a random girth-8 pair of `A_8` for `C`, and random twists `e ∈ {1..6}^3`, with seed
20260913. Each member is run through the same linear searches as the candidates.

| search | members | eigenvalue sign `σ = −1` | trace ideals `(1)` | representation found |
|---|---|---|---|---|
| dimension 4, characteristic 2 (`stat_d4c2.out`) | 150 | 76 | 74 | 0 |
| dimension 6, characteristic 2, irreducible (`stat_d6c2.out`) | 150 | — | 150 | 0 |
| dimension 7 over `F_29`, modules `1 ⊕ 6` and `7` (`stat_d7p29.out`) | 150 | — | 150 | 0 |

The sign split `76/74` matches the predicted `1/2`. No sampled member has a representation in any of
these three settings. So the candidates' linear zeros are typical of the family, not specific to them.

## 7. Heuristic: how many finite quotients should a member have?

Average over edge identifications. The number of conjugacy classes of homomorphisms `G -> S` that are
injective on the vertex groups is about `∏_e |C_S(E_e)| / (|S| ∏_v |C_S(A_v)|)`, up to bounded factors
(predecessor artifact). This is a count, not a proof. It is valid in the regime where the
positions of the edge groups behave randomly. The exponents in the main families of targets:
- **`L_4(2^m)`**, with `A_7` and `A_8` on `4`: `q^{9 − 15} = q^{−6}`, where `q = 2^m`.
- **`L_5(2^m)`**, with `4 ⊕ 1`: `q^{−9}`.
- **`GL_7` in characteristic 0 or odd characteristic**, with `1 ⊕ 6` and `7`: `q^{−32}`.
- **`A_n` in the free-orbit regime:** `|S|^{−χ_orb}` with `χ_orb ≈ 0.572`. Bounded-support actions with
  many fixed points decay polynomially in the number of fixed points.

**Consequence.**
- **The sum converges.** In every family the exponent is negative, and `A_8` must embed in `S`. So the
  sum over finite simple `S` converges and is dominated by the smallest groups containing `A_8`.
- **The dominant targets are empty.** For `A_n` with `n <= 21`, and for `L_5(2)`, `O_8^±(2)` and
  `Sp_8(2) ⊇ Sp_6(2)`, the configuration searches of §4 cover the whole family and find nothing.
- **Prediction.** A typical member of `F` has no finite quotient at all, and no structured source of
  small quotients has turned up that would override that prediction.
- **Caveat.** This is a heuristic. It proves nothing, and it fails exactly where hidden structure
  (congruence-like quotients, rigid representations) appears. It is also why computation cannot tell
  the four candidates apart from other members.
