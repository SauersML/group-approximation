# Swarm note: deligne-twisted-group-algebra-is-not-stably-finite (2026-09-16)

- **Agent:** `swarm-deligne-twisted-group-algebra-` (lock taken 2026-09-16, TTL 180m).
- **Outcome:** reduction. The target stays OPEN. It is now equivalent to a statement about weakly finite
  representations of `E_3`, and both twisted factors satisfy "stably finite iff rank condition".
- **Artifact:** `research/artifacts/deligne-twisted-sf-rank-condition-dichotomy-2026-09-16.md`.
- **New nodes:**
  - `lef-graded-simple-base-sf-iff-rank-condition`, with route `lef-graded-simple-base-sf-iff-rank-condition-proof`;
  - `deligne-twisted-sf-iff-wf-rep-detects-center`, with route `deligne-twisted-sf-iff-wf-rep-detects-center-proof`.

## Setup

- `1 -> <z> = C_3 -> E_3 -> Gamma = Sp_4(Z) -> 1` is Deligne's triple cover, and `a` is its section cocycle.
- For a field `F` of characteristic `p != 3` containing `w`:
  - `A_j(F) = F^(w^(ja))[Gamma] = F[E_3]/(z - w^j)`;
  - `F[E_3] = F[Gamma] x A_1(F) x A_2(F)`;
  - `F_0 = F_p(w)`.
- **Target.** For some `p`, `F` and `j`, `A_j(F)` is not stably finite.
- **Known on main.**
  - `Res_fin(E_3) = <z>`.
  - `Sp_4(Z)` is residually finite, so `F[Gamma]` is stably finite.
  - `A_j` has no finite-dimensional modules.
  - Stable finiteness of `A_j` follows from rank-approximate projective representations, i.e. from linear
    soficity (2026-09-12 artifact).

## What was proved

1. **Absorption (artifact Lemma 1.1, Proposition 1.2).** Let `A` be strongly `Gamma`-graded with simple
   `A_1`. Every unital `phi : A -> R` with `R != 0` is injective on each `A_g`, and
   `Σ x_g -> Σ phi(x_g) g` embeds `A` unitally in `R[Gamma]`.
2. **Theorem 2.1** (`lef-graded-simple-base-sf-iff-rank-condition`). For LEF `Gamma` these are equivalent:
   - stable finiteness;
   - a nonzero weakly finite image;
   - the rank condition;
   - a state on `(K_0, [1])`;
   - no properly infinite `M_n(A)`.

   The Goodearl–Handelman step (rank condition iff state) is proved in full, by Hahn–Banach over `Q`. The
   Toeplitz algebra shows the grading hypothesis is needed.
3. **Theorem 3.1** (`deligne-twisted-sf-iff-wf-rep-detects-center`). For `p != 3`, the target at `p` is
   equivalent to each of:
   - `A_j(F)` fails for all `F` and `j`;
   - `A_1(F_p(w))` fails the rank condition;
   - some `M_n(A_1(F_0))` is properly infinite;
   - `z in N_p`, the common kernel of all homomorphisms from `E_3` into units of weakly finite
     characteristic-`p` rings.

   Also `N_p in {1, <z>}`.

   The steps behind this:
   - the antipode, `A_j^op ≅ A_(3-j)`;
   - scalar restriction, `A_j(F) ⊂ M_d(A_j(F_0))`;
   - corners by central idempotents, which turn any weakly finite representation moving `z` into a weakly
     finite image of some `A_j(F_0)`;
   - Theorem 2.1.
4. **Proposition 3.4.** Twisting by a cocycle inflated from a finite quotient does not change stable
   finiteness of twisted group algebras, for any group.
5. **Section 4, under the target.**
   - A witness normalizes to a rectangular split `XY = I_(n+1)`, whose defect has trace `-1`, or to a
     properly infinite matrix ring. So a counterexample must be a compression.
   - Every Sylvester rank function on `F[E_3]` is pulled back from `F[Gamma]`.
   - No homomorphism from `E_3` to an `F_p`-linear sofic group is injective on `<z>`.
6. **Remark 2.4 (unverified setup).** For the Kun–Thom Clifford skew ring `A_S = C_S * G` with nondegenerate
   `b_S`, the complete graph included:
   - `C_S` is simple (minimal-support argument);
   - if `G` is residually finite, as the Clifford artifact states, Theorem 2.1 gives that `A_S` is stably
     finite iff it has the rank condition.

   This was not made a node, since that artifact's setup was not re-checked.

## Approaches tried and where each dies

**Positive side: a weakly finite image of `A_j`, equivalently a weakly finite representation of `E_3`
moving `z`.**
- **PI images, finite-dimensional algebras, commutative rings.** Dead (Proposition 5.1). Posner gives
  `M_d(L)`, Malcev makes the image residually finite, and that contradicts `Res_fin(E_3) = <z>`.
- **Exact products, algebraic ultraproducts and `Π/⊕` of matrix algebras.** Dead (Proposition 5.2). `E_3`
  is finitely presented, so the relations hold coordinatewise, and Malcev applies again.
- **Noetherian images (Goldie).** They reduce to `rho : E_3 -> GL_d(D)` over a division ring `D` with
  `rho(z) = w^j`.
  - Commutative `D`: dead.
  - `D` finite-dimensional over its centre: dead, by splitting to a field and Malcev.
  - `D` infinite-dimensional over its centre: **open**. Malcev fails there, for example for `BS(2,3)`
    inside a division ring (Lewin–Lewin, not re-fetched), and no candidate is known.
- **Rank-metric models.** This is linear soficity of `E_3` in characteristic `p`, open on main. Theorem 3.1
  shows it is only one of many admissible images, so nothing here needs a metric.
- **Central deformation through `Sp~/mZ`.** Dead. Only `m | 2` can be residually finite, no specialization
  transports weak finiteness in the parameter, and `Sp~` is not LEF.

**Negative side: forcing `z in N_p`.**
- **Herstein-type torsion obstructions**, such as cyclicity of finite subgroups of `D^x`, or `z` being a
  commutator inside a finite subgroup. Vacuous (Proposition 5.4). The Bockstein and pullback model gives
  every finite `H~ <= E_3` a character with `z -> w`.
- **Trace or defect counting.** No mod-`p` trace constraint exists. Square witnesses have defect trace `0`
  and rectangular splits have `-1`, and both occur.
- **Compression designs.** The strict-pair designs on main (Leavitt corners, table groups) come from hosts
  with `R ≅ R^2`. Theorem 2.1 shows a compression `A^n ≅ A^(2n) ⊕ Q` over `A_1(F_0)` is necessary. No
  mechanism producing one from a multiplier on `Sp_4(Z)` was found.

**Not attempted.**
- Computer search. A modest search over small supports cannot certify `BA = 1 != AB` in an
  infinite-dimensional algebra, and it gives no information on the rank condition.
- An OPEN node for the division-ring case. To refute the target it would have to be posed for every
  `p != 3` at once. No candidate construction exists, so it stays in this note.

## Weakest steps

- **Malcolmson import.** Theorem 2.1 (iii => ii) is imported through
  `rank-condition-rings-have-weakly-finite-images`, whose local proof is on main and was not re-verified
  here. Items 1, 2 and 5 of Theorem 3.1 do not use it, since they only need absorption and the LEF node.
- **Classical citations.** Posner, Goldie, Behr, Elek–Szabó, Hazrat and Lewin–Lewin were not re-fetched.
  They are used only in Sections 4.3 and 5 and in remarks, never in the two routes.

## Literature consulted (2026-09-16)

- **Fetched (abstract pages).**
  - arXiv:2410.02913, Chapman–Dikstein–Lubotzky (v2 Dec 16 2024): non-soficity of p-adic Deligne
    extensions, conditional on stability. Nothing on stable finiteness.
  - arXiv:2505.21030, Lorensen–Öinert (v3 Mar 24 2026): rank conditions for Ore extensions. It cites
    Malcolmson and has nothing on twisted group rings.
  - arXiv:2608.06222, Kun–Thom (v3 Aug 20 2026): nonsofic wreath products. Nothing on Deligne extensions.
  - Phung, CJM 76(4) 2024: a different "twisted group ring".
  - Thom's guest post on Tao's blog (2026-09-11): the non-sofic group construction. No Deligne or
    Kaplansky content.
- **Search listing only.** arXiv:2608.02025, Fournier-Facio, *A torsion-free non-sofic group* (Aug 17 2026),
  contents not checked.
- **Cited via main, not re-fetched.** Malcolmson, PAMS 80 (1980); arXiv:2201.01432 (Hung–Li).
- **Not found.** No source states the absorption proposition or Theorem 2.1, and no 2024–2026 source
  decides the target.

## Referee (2026-09-16)

**Checked.**
- **Absorption and Theorem 2.1, every step re-derived.** Components: `ker phi ∩ A_1 = 0` and
  `x = Σ (x a_i) b_i` with `1 = Σ a_i b_i`, `a_i in A_(g^-1)`, `b_i in A_g`. The padding argument for
  (i) ⇒ (iii), the properly infinite argument for (i) ⇒ (v), and the composed retractions for (v) ⇒ (iii).
- **Lemma 2.2 (Goodearl–Handelman).** Re-derived the lower bound `p >= -N`, subadditivity, integer
  homogeneity, torsion invariance, `f <= p` on `Qu`, and the one-step Hahn–Banach extension over `Q` with
  real values. Sound.
- **Imports on main.**
  - `lef-group-rings-over-stably-finite-rings-are-stably-finite` is ESTABLISHED, allows noncommutative
    `R`, and uses the same LEF definition.
  - `rank-condition-rings-have-weakly-finite-images` is ESTABLISHED by a local direct proof, verified twice
    on main. I skimmed the key lemma and the weak-finiteness step, and both are correct.
  - `deligne-triple-cover-finite-residual-is-center` and `finitely-generated-linear-groups-are-residually-finite`
    are ESTABLISHED.
  - "Weakly finite" is used throughout in Cohn's sense, which equals stably finite, matching both imports.
- **Theorem 3.1, re-derived.**
  - The antipode computation `S(z - w^j) = -w^j z^(-1)(z - w^(-j))`.
  - The embedding `A_j(F) -> M_d(A_j(F_0))` by left multiplication on a free right module.
  - `R ⊗ F_0` inside `M_2(R)` by left multiplication on the free right `R`-module.
  - Centrality of `rho(z)` in `S`, the idempotents (they need `p != 3` and `w in F_0`), and the corner
    trick `(X + (1-e_j)I)(Y + (1-e_j)I) = I`.
  - Step 6 needs only the inclusion `Res_fin(E_3) <= <z>`.
  - The quantifiers match the target statement, where `F` contains `w`.
- **Artifact Sections 3.4–5, re-derived.** Inflation invariance, the trace identity
  `alpha(g, g^-1) = alpha(g^-1, g)`, the Sylvester rank corner argument, Proposition 5.1 (Posner, then
  Malcev), Proposition 5.2 (finite presentation), the Bockstein/pullback model in 5.4, and the Clifford
  simplicity argument in Remark 2.4. No errors found.
- **Literature spot-checks, fetched 2026-09-16.**
  - arXiv:2410.02913: title, authors and dates (v1 Oct 3 2024, v2 Dec 16 2024) confirmed.
  - arXiv:2505.21030: title, authors and v3 date (Mar 24 2026) confirmed. The abstract does not name
    Malcolmson, so the Malcolmson quote rests on the earlier check recorded on main.
  - A further novelty search could not be run (web search budget exhausted). Novelty is not asserted in
    any node, and the artifact already calls Theorem 2.1 "probably folklore".
- **Duplicates.** `bin/cairn search --similar` found no duplicate. Closest is
  `simple-ring-stably-finite-iff-unit-not-paradoxical`, the trivial-grading case via `V(R)`.

**Changed.**
- `lef-graded-simple-base-sf-iff-rank-condition`:
  - added `distinct_from` for `simple-ring-stably-finite-iff-unit-not-paradoxical`;
  - stated the unital and "weakly finite = stably finite" conventions in the claim.
- `deligne-twisted-sf-iff-wf-rep-detects-center-proof`: added `residually-finite-groups-are-lef` to
  `requires:`, replacing the inline RF ⇒ LEF argument.
- `deligne-twisted-sf-iff-wf-rep-detects-center`:
  - item 1 now says `F` contains `w`, matching the target;
  - the "Consequences" paragraph is relabelled as remarks not certified by the route, and flags the
    classical results it uses that were not re-fetched.
- Artifact Proposition 5.4: the statement now restricts to finite subgroups containing `z`, with values in
  a finite extension `L` of `K`, matching its proof.

**Verdict: landed with minor fixes.** Both new claims are sound reductions with complete routes over
established imports. The target stays OPEN.
