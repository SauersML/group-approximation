# Hard fp simple groups via self-similar hosts: swarm attack, 2026-09-16

- **Lane:** `swarm-fp-simple-groups-with-arbitrar`.
- **Root:** `fp-simple-groups-with-arbitrarily-complex-word-problem`.
- **Hole locked and worked:** `fp-self-similar-groups-with-arbitrarily-hard-word-problem`
  (OPEN, and still OPEN).
- **Full proofs:** `research/artifacts/fp-self-similar-hard-wp-swarm-2026-09-16.md`.
- **Scripts:** none; this lane did no computation.

## Setup

The hole asks, for each recursive `T`, for a finitely presented self-similar group
whose word problem is not decidable in time `C*T(C*l) + C*l + C`. Through Zaremsky's
envelope this implies the root. By
`rover-nekrashevych-word-problem-reduces-to-self-similar-group`, it is also necessary
for the Röver--Nekrashevych branch of the root.

Committed state before this lane:
- **Necessary conditions.** A witness needs infinitely many states and must be
  residually finite.
- **Attempt 1.** Goes through the open embedding claim.
- **Attempt 2.** Dismissed Zaremsky's affine hosts `R^n x| GL_n(R)` (Example 4.7 of
  arXiv:2405.09722) because they "land inside linear groups over fields". For
  non-commutative `R` that was never proved in the graph.
- **Attempt 3.** Direct virtual-endomorphism constructions, not executed.

The most natural source of finitely presented self-similar groups with complicated
linear parts is Example 4.7 over *non-commutative* rings. That is the gap this lane
attacked.

## What was proved

1. **`char-p-untwisted-self-similar-affine-groups-are-linear`**, established by the
   direct proof `char-p-untwisted-self-similar-affine-groups-linear-proof`.
   - **Setting.** `A` is an elementary abelian `p`-group. `ν` is an injective
     endomorphism with `A/νA` of dimension `r` and `∩ ν^k A = 0`.
   - **The embeddings.** Expanding in `ν`-adic digits gives an injective
     `ι: A -> F_p[[t]]^r` with `ι(νa) = tι(a)`, and a ring embedding
     `End_ν(A) -> M_r(F_p[[t]])` with `ν -> tI`. So `A x| Γ` embeds in
     `GL_((r+1)[Γ:Γ_0])(F_p[[t]])` whenever a finite-index `Γ_0` commutes with `ν`.
   - **Example 4.7 in characteristic `p`.** Every ring satisfying its hypotheses
     embeds in `M_s(F_p[[t]])`, so it is PI. For every `Γ <= GL_n(R)`, `R^n x| Γ`
     embeds in `GL_(ns+1)(F_p[[t]])`.
   - **Twisted hosts.** Hosts from Corollary 4.5 whose twist `γ -> φγφ^(-1)` is
     virtually, up to a power, conjugation by a filtration-preserving automorphism
     reduce to the same case.
2. **`char-p-untwisted-affine-hosts-have-polynomial-word-problem`**, by
   `char-p-untwisted-affine-hosts-polynomial-wp-proof`.
   - Every finitely generated subgroup of such a host has polynomial word problem, in
     the single class `F(2^n)`.
   - The KMS group of `kms-groups-avoid-commutative-algebra-affine-hosts` embeds in
     none of them.
   - Proof: restrict the linearization to the finitely generated coefficient algebra,
     then apply `commutative-algebra-affine-groups-have-polynomial-word-problem`.
3. **Route `hard-type-a-actors-from-hard-fp-self-similar-groups`** (OPEN; it needs the
   hole).
   - The hole implies `type-a-actors-with-arbitrarily-hard-word-problem`. By (a) of
     `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, a hard finitely
     presented self-similar group lies in a type (A) actor. Substitution then
     transfers hardness upward.
   - **Correction to a committed node, not edited.** The `distinct_from` of
     `type-a-actors-with-arbitrarily-hard-word-problem` says that neither claim is
     known to imply the other. One direction is now a route. The converse remains
     unknown.

**Outcome class:** obstruction, plus a reduction.

## Approaches and where each dies

1. **Example 4.7 over non-commutative rings of characteristic `p`.** *Dies*, by (1)
   and (2). The ring is forced into `M_s(F_p[[t]])`. The host is linear over
   `F_p((t))`, and its finitely generated subgroups share the bound `2^n`.
2. **Corollary 4.5 over elementary abelian `A` with a mildly twisted `Γ`.** A finite
   order twist, or conjugation by an element of `Γ`, reduces to (1). *Dies.*
3. **Corollary 4.5 over elementary abelian `A`, genuinely twisted.** *Open.*
   - Linear parts act digit by digit through the states `σ^k(γ)`, as `F_p`-linear
     transducers that are not `F_p[[t]]`-linear.
   - This is where the hole's "infinitely many states" condition lives. It is the
     only surviving affine route over elementary abelian groups.
   - The tree maps involved appear to be the affine tree automorphisms of
     Savchuk--Sidki (abstract only).
   - Heuristic, not checked: without self-similarity, filtration-preserving linear
     tree automorphisms contain many residually-`p` groups, so no linear-algebra
     obstruction is expected here.
4. **Example 4.7 in characteristic `0` or exponent `p^m` with `m >= 2`.** *Not
   closed.*
   - The completion `lim A/ν^k A` is a finitely generated module over
     `(∏_(p | N) Z_p)[[t]]`, and a saturation argument places finitely generated
     subgroups in `Aff_S(M)` over finitely generated commutative rings `S`. This is
     sketched in artifact §9 and not promoted.
   - What is missing is a polynomial word-problem bound over finitely generated
     commutative rings of mixed or zero characteristic, for example by strong Gröbner
     bases over `Z`. It is not in the graph.
   - So Attempt 2's dismissal remains unproved there for non-commutative rings.
5. **Attempt 3 of the hole (virtual endomorphisms of the KMS groups).** Not executed.
   By (2), any self-similar host of a KMS group of the form `A x| Γ` over an
   elementary abelian `A` must be genuinely twisted.

## Suggested edits for a later non-swarm lane

These are not made here, per swarm rules.
- Append to the hole's Attempt 2: "proved in characteristic `p` by
  `char-p-untwisted-affine-hosts-have-polynomial-word-problem`; unproved in
  characteristic `0` for non-commutative rings".
- Update the `distinct_from` rationale in `type-a-actors-with-arbitrarily-hard-word-problem`
  to cite `hard-type-a-actors-from-hard-fp-self-similar-groups`.

## Weakest step

The fragile points are the two finite-index and twist extensions: the
induced-representation step and the twist reduction (d). Both are written out in full
in the direct proof. The word-problem consequence relies on the imported Gröbner-basis
trust surface of `commutative-algebra-affine-groups-have-polynomial-word-problem`.

## Literature (checked 2026-09-16)

Web search budget was exhausted, so the arXiv export API was used instead.
- **Zaremsky**, arXiv:2405.09722v2 (v1 2024-05-15, v2 2025-01-21). §4 read from TeX:
  Corollary 4.5 and Example 4.7. No linearization is stated.
- **Fournier-Facio--Wu--Zaremsky**, arXiv:2603.24687v2 (2026-03-25, v2 2026-04-02).
  Abstract only.
- **Almeida--Dantas--Oliveira-Tosti**, arXiv:2609.01868v1 (2026-09-01). Abstract only.
- **Livramento--Noseda**, arXiv:2410.22639v1 (2024-10-30). Abstract only.
- **Dantas--Santos--Sidki**, arXiv:2004.08941v2 (2020-04-19/21). Abstract only.
- **Savchuk--Sidki**, arXiv:1510.08434v1 (2015-10-28). Abstract only.
- **Bartholdi--Mitrofanov**, arXiv:1710.10109v4 (2017-10-27, updated 2017-11-27).
  Abstract only. Undecidable word problem for functionally recursive groups; these
  are not finitely presented and no time bounds are given.
- **BFFHZ**, arXiv:2503.21882v2, through committed graph nodes only; not re-read.
- **arXiv API abstract searches:** "self-similar" with "virtual endomorphism";
  "self-similar" with "word problem"; "Boone-Higman"; "finitely presented simple" with
  "word problem"; "linear automata" with "group"; "self-similar" with "affine" and
  "tree". None states the linearization or a hard finitely presented self-similar
  group.
- **Standard, not re-read:** Amitsur--Levitzki; Cox--Little--O'Shea.

## Referee (2026-09-16)

**What was checked.**
- **Linearity proof, line by line.** Layer dimensions (Step 1), bijectivity of the
  digit maps `π_k` (Step 2), additivity, filtration and shift of `ι` (Step 3), the
  formula `ι(ea) = M(e)ι(a)` with multiplicativity and injectivity of `M` (Step 4),
  the affine block embedding (Step 5), the induced-representation block product and
  its kernel (Step 6), Example 4.7 with column-vector action and left
  multiplications (Step 7), and the twist reduction `ν = μ^m δ`, including
  `ν^k A = μ^(mk) A` (Step 8). No gap found. Characteristic, finite corank and
  separation are all used and stated; no finite generation is needed.
- **Numerical sanity check** (scratch script, not landed): for the non-commutative
  ring `R = F_4[t; Frob]`, `x = t`, `s = 2`, the matrices `M(λ_b)` built from the
  proof's definition satisfy `M(λ_a)M(λ_b) = M(λ_(ab))` and `ι(ac) = M(λ_a)ι(c)`
  modulo `t^8` on 500 random triples. `M(λ_t)` and `M(λ_ω)` do not commute, as
  they must not.
- **Word-problem route.** The finitely generated coefficient algebra `S <= F_p[[t]]`
  is commutative and finitely generated; `Ψ(H) <= GL_N(S) <= Aff_S(S^N)` matches the
  hypotheses of `commutative-algebra-affine-groups-have-polynomial-word-problem`
  and of `kms-groups-avoid-commutative-algebra-affine-hosts` exactly.
- **Type (A) route.** (a) of `fp-self-similar-subgroups-satisfy-permutational-boone-higman`
  is ESTABLISHED; type (A) includes faithfulness and finite presentability; the
  substitution matches `complexity-bounded-host-classes-are-not-universal-proof` and
  the committed route `hard-type-a-actors-from-permutational-boone-higman`. Sound.
- **Literature spot-check.** arXiv:2405.09722 (v1 2024-05-15, v2 2025-01-21) fetched:
  Corollary 4.5 requires a surjective proper virtual endomorphism mutually stable
  with `Γ`; Example 4.7 has the finite-index principal left ideal `Rx`,
  non-zero-divisor `x`, and `∩ Rx^k = 0`. The paper states nothing about linearity
  or word-problem complexity. Other citations are abstract-only as labelled.
- **Duplicates.** `bin/cairn search --similar` on both new claims finds no
  near-duplicate; the distinct_from rationales are accurate after the fix below.

**What was changed.**
- Linearity claim: the `digit-affine-hosts-...` distinct_from rationale said "whatever
  their linear parts"; corrected to the actual commuting hypothesis. In (d), `μ` is
  now stated additive.
- Linearity proof: stated `ι(g(ν)x) = g(t)ι(x)` explicitly (used in Step 4), and
  justified finiteness of `A/μ^m A` in Step 8.
- Word-problem claim: "hardness has to come from genuinely twisted virtual
  endomorphisms" narrowed to Corollary 4.5 hosts over elementary abelian `p`-groups,
  with the uncovered cases named.
- Artifact: same narrowing in §6; `μ` additive; the "Correction" bullet no longer
  says linearity was previously proved over all commutative rings.

**Verdict.** Landed with small fixes. Both obstruction claims are sound and honestly
labelled (no novelty claimed; the linearization is elementary and may well be
folklore). The type (A) route is a correct open implication. The hole
`fp-self-similar-groups-with-arbitrarily-hard-word-problem` remains OPEN. The
committed `distinct_from` of `type-a-actors-with-arbitrarily-hard-word-problem`
("neither is known to imply the other") is now stale in one direction and was not
edited.
