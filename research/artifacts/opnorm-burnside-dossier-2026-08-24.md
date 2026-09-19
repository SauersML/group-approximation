# Operator-norm restricted Burnside dossier — ingestion audit, 2026-08-24

External research dossier ("full-norm routes to non-MF groups"), 26 sections.
Its own executive status is honest: **no second proof of the Leavitt target**,
and no finished new non-MF example. What it delivers is one proved equivalence
theorem, a small set of open statements around it, and a set of audited dead
ends. This file records the disposition of each.

Nothing landed here establishes or refutes any existing program claim. The
manuscript's proof of the Leavitt result is untouched and uncited by this
region.

## Landed as established

| node | content |
|---|---|
| `finite-order-unitary-has-uniform-opnorm-gap` | `u^N=1, u≠1 ⟹ ‖u−1‖ ≥ 2sin(π/N)`, in **any** unital C*-algebra |
| `restricted-burnside-finiteness` | Zelmanov, imported; `R(m,N)` finite and universal among finite `m`-generated exponent-`N` groups |
| `corona-restricted-burnside-equals-power-law-moduli` | the CRBP equivalence (A) ⟺ (B), both directions |
| `exponent-two-modulus-is-the-commutator-norm` | `‖(UV)²−I‖ = ‖UV−VU‖` for exact involutions — the calibration |
| `universal-relations-cannot-force-proper-infiniteness` | the regular-representation kill for Cuntz/proper-isometry shortcuts |
| `augmentation-lifting-equals-full-mf-radical` | the augmentation route is **exactly** circular, not merely close |

## Landed as open, with the routes

```
osin-periodic-quotient-is-non-mf            [root]
  ├ osin-non-mf-from-general-bounded-exponent
  │     infinite-fg-bounded-exponent-groups-are-non-mf
  │       ├ bounded-exponent-non-mf-from-corona-burnside
  │             operator-norm-restricted-burnside
  │               ├ corona-burnside-from-power-law-moduli
  │                     matrix-restricted-burnside-gap        <- the leaf hole
  │                     corona-restricted-burnside-equals-power-law-moduli  [est.]
  └ non-mf-from-stable-osin-horn-separator
        osin-horn-separator-is-opnorm-stable                  <- the cheap hole
        osin-torsion-universal-theory-separator               [est., citation]
        finite-order-unitary-has-uniform-opnorm-gap            [est.]
```

Two independent roads into one concrete target: the whole restricted Burnside
family of moduli, or **one** inequality attached to one fixed presentation.

## Re-derivation notes (everything below was checked, not copied)

* **The gap lemma.** `u` normal, so `‖u−1‖ = max{|λ−1| : λ ∈ σ(u)}`;
  `σ(u) ⊆ μ_N`; `u ≠ 1` with one-point spectrum is impossible for a normal
  element; nearest non-identity root gives `2sin(π/N)`. Holds verbatim in the
  corona because it needs only normality and functional calculus.
* **CRBP (B)⟹(A).** The load-bearing detail is that `W` is **finite**, so one
  threshold `n` serves the whole hypothesis; with an infinite `W` the argument
  would need a diagonal and would fail.
* **CRBP (A)⟹(B).** Genuinely constructive: the diagonal tuple *is* the
  witnessing corona subgroup. This is what makes the statement a fork rather
  than a sufficient condition, and it is worth more than the forward direction.
* **The `ε < δ_N` sharpening.** The dossier notes it and it is right: once
  `s_j(u)` lies in an exponent-`N` group, any bound below the torsion gap
  forces triviality, so quantifying over all `ε > 0` is unnecessary. The open
  node `matrix-restricted-burnside-gap` is stated in the sharpened form only.
* **Exponent two.** `U(VU−UV)V = (UV)² − U²V²`, and with `U²=V²=I` that is
  `(UV)²−I`; unitary invariance gives the identity. The approximate version
  carries an `‖U²V²−I‖ ≤ a+b` error, giving `‖UV−VU‖ < 3η`.
* **The augmentation no-go is sharper than the dossier says.** The dossier
  calls the lifting hypothesis "so close to the conclusion" that the argument
  "becomes a disguised restatement". It is not close — it is **equal**:
  lifting ⟹ zero (coordinate maps must vanish), and zero ⟹ lifting (lift by
  zero). The node states the three-way equivalence with lifting, vanishing,
  and `Rad_MF(G) = G`, which converts a soft misgiving into a theorem.

## Corrections to the dossier

1. **Hrushovski–Rodríguez Fanlo is not a 2026 paper.** arXiv:2209.01262,
   *On metric approximate subgroups*, was posted September 2022, v2 April
   2024, published in the Journal of Mathematical Logic in 2025. The dossier
   says "their 2026 arXiv version". Verified this session. The mathematical
   description — bounded exponent brings a `(k,r)`-metric approximate subgroup
   close to a `(1,r')`-one, under a covering hypothesis
   `N_(2^-m)(X) ≤ C^m N_1(X)` — is right, and so is the dossier's refusal to
   claim it proves the missing lemma.
2. **Osin's separator is not automatically a single-conclusion Horn
   sentence.** The verified theorem (arXiv:0903.3978; Groups Complexity
   Cryptology 1(2), 2009, 311–319) is that the universal theory of torsion
   groups is *properly* contained in that of finite groups, answering a
   question of Dyson. A universal sentence, negated and put in disjunctive
   normal form, yields an implication with a **disjunctive** conclusion; a
   quasi-identity is the special case. All downstream nodes are written for
   the disjunctive form, and the extra subsequence step it costs is spelled
   out in `non-mf-from-stable-osin-horn-separator`.
3. **The specific `G = ⟨x|R⟩`, `Ḡ = G/G^n` shape was not source-verified**
   here — only the headline theorem was. That is flagged inside
   `osin-torsion-universal-theory-separator` rather than smoothed over.
4. **"Proper isometry among the group elements" is impossible for free**, not
   for the trace reason the dossier gives: a group word in unitaries is a
   unitary. The trace argument is needed only once the construction moves into
   the closure of the group algebra. Recorded in
   `universal-relations-cannot-force-proper-infiniteness`.

## Already in the graph, so not duplicated

* **Candidate D (additive Fredholm/parity indices).** `additive-index-instability`
  already states the exact objection — `φ ⊗ I_k` multiplies the index by `k` —
  and already carries an `invalidates:` key. The new gap claim is written as
  its positive counterpart and cites it.
* **§19, the relative-commutant no-growth hope.** `corona-commutant-no-growth`
  is a root that is **refuted** (`refuted_by: corona-commutant-growth-witness`),
  which is exactly the dossier's report that the repository contains slow-phase
  corona witnesses of genuine growth. No node authored.
* **Candidate F, generic Horn packaging.** `mf-universal-horn-obstruction` and
  `mf-relation-closure` already own the direction *established non-MF theorem
  ⟹ Horn obstruction*. Only the reverse direction — a classical separator plus
  a new operator-norm modulus — is new, and that is what landed.
* **The abelian case of the missing inequality.** `corona-commuting-torsion-lifts-proof`
  Step 2 is a finite exactification lemma with a dimension-free modulus for
  *commuting* torsion tuples. It is cited as the abelian instance of
  `matrix-restricted-burnside-gap` and as attempt 3 there.
* **The fixed-finite-group case.** `finite-group-opnorm-support-profile` gives
  precisely the dimension-free operator-norm correction once a finite group and
  presentation are fixed in advance, and `finite-group-corona-tail-exactification`
  is its corona-level form. Both are cited as attempt 1: the gap between them
  and the missing lemma is exactly "which finite group", since the hypothesis
  names only an exponent.
* **Candidate A (pointwise matricial stability), Candidate G (spectral
  dynamics), the torsion-kernel stability compiler.** The dossier itself
  rejects or demotes all three; nothing was authored for them. The compiler's
  mechanism — an exact representation with `‖π(t)−1‖ < 2sin(π/m)` and
  `π(t)^m = 1` forces `π(t)=1` — is the gap lemma applied twice and is
  subsumed by `finite-order-unitary-has-uniform-opnorm-gap`.

## Declined

* **No `invalidates:` key was added anywhere.** The dossier's rejected
  candidates read as kills, but each would need a named live route in this
  graph with the excluded shape, and the two no-go claims that did land are
  written as theorems about proposed strategies, not as obstructions to
  specific route ids.
* **The dossier's own novelty audit is partially unverified by its own
  admission** — it had no live `.git` and could not run `git log`. Its file
  citations (`scale-index-route`, `corona-commutant-no-growth`,
  `additive-index-instability`, `opnorm-leavitt-coarse-fine-return-row`, and
  the two named artifacts) were all checked here and **all exist**, so its
  repository reading is in good faith.

## The one thing to check before investing

Attempt 4 of `operator-norm-restricted-burnside` records it, and it is the
most important line in this region: a proof of `matrix-restricted-burnside-gap`
may turn out to be **equivalent to a strong LEF statement for the large free
Burnside groups**, whose status is delicate in exactly the range that matters.
That check is cheaper than the proof and should precede it.

## Status of the six established claims

Four are load-bearing and consumed by routes: `restricted-burnside-finiteness`
feeds the CRBP proof, `corona-restricted-burnside-equals-power-law-moduli`
feeds `corona-burnside-from-power-law-moduli`,
`finite-order-unitary-has-uniform-opnorm-gap` feeds
`non-mf-from-stable-osin-horn-separator`, and
`osin-torsion-universal-theory-separator` feeds both Osin routes.

Three are **recorded findings consumed by no route**, deliberately:
`exponent-two-modulus-is-the-commutator-norm` (a calibration, whose job is to
show the scheme is not vacuous and to locate where the difficulty starts),
`universal-relations-cannot-force-proper-infiniteness` and
`augmentation-lifting-equals-full-mf-radical` (two theorems *about proposed
strategies*, whose job is to stop them being re-proposed). Turning either
no-go into a live obstruction would need a named live route in this graph with
the excluded shape; none was identified, so no `invalidates:` key was written.

## Verification run

`cairn check` on the live tree with the region in: **exit 0, 0 errors**. All
six established claims compile as established via their own companion routes
and nothing else; the four new routes each report "missing only" their single
open prerequisite. `cairn why matrix-restricted-burnside-gap` prints the full
chain `osin-periodic-quotient-is-non-mf -> infinite-fg-bounded-exponent-groups-are-non-mf
-> operator-norm-restricted-burnside -> matrix-restricted-burnside-gap`, which
is the intended architecture. No duplicate warning names any node of this
region, and no orphan warning either. One authoring slip was caught by the
checker and fixed before landing: a `distinct_from` key naming
`leavitt-direct-finiteness-failure-from-left-invertible-lift`, which is a
*route*; the claim is `leavitt-unit-group-algebra-not-directly-finite`.

`research/FRONTIER.md` was **not** regenerated: the shared tree carries several
peer lanes' uncommitted work, and `origin/main` is independently red from a
lane mid-repair, so a regenerated index would be neither honest nor stable.
