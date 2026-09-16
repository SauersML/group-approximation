# `some-braid-group-has-no-proper-cat0-action` (swarm, 2026-09-16)

Agent `swarm-some-braid-group-has-no-proper`. The hole was locked for this
session (TTL 180m) and is unlocked at the end. Nothing was committed.

## Setup

- **Root.** `zaremsky-3-06-braid-groups-cat0`, Zaremsky Problem 3.6, whether
  braid groups are CAT(0). That root forbids `requires: []` routes into it.
- **Hole.** Some `n` has `B_n` with no proper isometric action on any proper
  CAT(0) space. Necessarily `n ≥ 8`, since `B_n` is CAT(0) for `n ≤ 7`
  (Haettel–Kielak–Schwer arXiv:1304.5990 for `n = 6`; Jeong arXiv:2009.09350 for
  `n = 7`).
- **Consumers.**
  - `braid-not-cat0-from-no-proper-cat0-action` gives `some-braid-group-is-not-cat0`.
  - `braid-not-z-linear-from-no-proper-cat0-action` gives
    `some-braid-group-embeds-in-no-glnz`.
- **Negation.** `every-braid-group-acts-properly-on-a-proper-cat0-space`, which
  has routes via CAT(0)-ness and via number-field linearity.
- **Definitions.** Proper means in the Bridson–Haefliger I.8.2 sense. The
  translation length is `|γ| = inf_x d(x, γx)`. An isometry is either
  semisimple (elliptic or hyperbolic) or parabolic; a parabolic is neutral if
  `|γ| = 0`.

## Literature gate (2026-09-16)

- **Searches.** arXiv API (`export.arxiv.org/api/query`), all run 2026-09-16:
  - `abs:braid AND abs:CAT(0)`, sorted by date;
  - `abs:Artin group AND abs:CAT(0)`;
  - a listing of recent `abs:braid` submissions through `2609.08091` (2026-09-08).
- **Result.** No 2024–2026 paper decides whether `B_n`, `n ≥ 8`, is CAT(0) or
  acts properly on a proper CAT(0) space. As far as these searches show, the
  problem is open.
- **Sources consulted.**
  - **Read in full or in part:**
    - Bridson, "Semisimple actions of mapping class groups on CAT(0) spaces",
      arXiv:0908.0685. The LaTeX source was read. Quoted: Proposition `l:hyp`,
      the centralizer criterion; Theorem `t:paras` and its proof via
      Karlsson–Margulis and Busemann characters; Remark `r:abelian`, on
      induction to `X^n`; the attribution to Kapovich–Leeb.
  - **Abstract only:**
    - Bregman–Libgober–Zhu, "CAT(0) geometry of complex curve complements and
      families", arXiv:2411.18067 (2024-11-27). Motivated by the braid question;
      shows that the universal-family groups for `E_6, E_7, E_8` are not CAT(0).
      Not read beyond the abstract, so the obstruction they use is unverified
      here.
    - Barré–Pichot, "A virtual geometric action of a braid group",
      arXiv:1912.13391 (2019-12-31). A finite-index subgroup of `B_4/Z` acts
      geometrically on a CAT(0) space.
    - Haettel, arXiv:2109.07891 (2021, v5), and Huang–Osajda, arXiv:1904.09060
      (2019, v4). Garside and FC-type Artin groups act geometrically on injective
      metric spaces and Helly graphs. These are CAT(0)-like but not CAT(0).
  - **Title or listing only:** Brady–McCammond, "Braids, posets and
    orthoschemes", arXiv:0909.4778.
  - **Known only through Bridson's citation:** Kapovich–Leeb, Math. Ann. 306
    (1996). The PDF could not be text-extracted in this environment.

## What was established

**New claim** `braid-centralizer-characters-detect-infinite-order`, established by
route `braid-centralizer-characters-detect-infinite-order-proof` (`requires: []`)
with artifact `research/artifacts/braid-centralizer-characters-2026-09-16.md`.

- **Theorem.** Every infinite-order `β ∈ B_n` has infinite order in
  `H_1(Z_{B_n}(β); Z)`.
  - The property passes to subgroups, finite-index overgroups and products.
  - So it also holds in `P_n`, `P_n/Z ≅ PMod(S_{0,n+1})`, `B_n/Z` and
    `Mod(S_{0,n+1})`.
- **Proof outline.**
  - **Transfer lemma.** For `H ≤ Z(β)` of finite index `j`, the transfer sends
    `β` to `[β^j]`. So it suffices to find a character on a finite-index subgroup
    of the centralizer that is nonzero on a power of `β`.
  - **Set-up.** Take the canonical reduction system `C` of a pure power `f^k` of
    `π(β) ∈ Mod(S_{0,n+1})`. By naturality `Z(β)` preserves `C`.
  - **Case A: a pseudo-Anosov component.** McCarthy's theorem (the centralizer
    of a pseudo-Anosov is virtually `Z`) gives the character.
  - **Case B: all components trivial.**
    - Then `β^k` is `Δ^{2e}` times a multitwist about `C`, and linking numbers
      read off `e·χ_{[n]} + Σ e_c χ_{S_c}`.
    - A laminar-family lemma shows that the pair-indicator vectors of nested or
      disjoint puncture sets are independent. So some linking number is nonzero.
- **Consequence (obstruction).** Bridson's criterion forces `|γ| = 0` on elements
  that are torsion in the abelianization of their centralizers. It applies to
  hyperbolics (Prop. `l:hyp`) and to non-neutral parabolics (proof of Thm
  `t:paras`).
  - In `B_n`, and in every group above, such elements are exactly the
    finite-order ones.
  - So the Kapovich–Leeb/Bridson template cannot seed an obstruction to this
    hole or to `some-braid-group-is-not-cat0`. The template is: a twist torsion
    in the abelianization of its centralizer, hence neutral, hence elliptic under
    semisimplicity, contradicting properness.
  - This is the genus-0 contrast with `Mod(Σ_g)`, `g ≥ 3`. There the
    complementary pieces have finite abelianization; here they are punctured
    disks whose braid groups have abelianization `Z`.
- **Check.** `check.sh` on the claim, the route and the artifact gave exit 0.
  (An earlier draft said "landed `abc9e1536`"; that is an unrelated commit and
  the referee removed the phrase.)
- **Experiment.** `experiments/braid-centralizer-characters-2026-09-16/`
  (`check_laminar_and_lk.py`, `output.txt`) contains two checks.
  - The laminar lemma, exhaustively for all `(2n−3)!!` maximal laminar families
    with `n ≤ 7`.
  - The linking-number formula `lk_{ij}(w Δ_S² w⁻¹) = [{i,j} ⊆ perm_w(S)]` on 400
    random cases.

## Reformulation of the hole

Existence of a proper isometric action on a proper CAT(0) space passes along
three operations:
- **Subgroups:** restrict the action.
- **Finite-index overgroups:** induce to the `ℓ²`-product `X^m`, as in
  Bridson's Remark `r:abelian`. Properness can be read on one coordinate after
  restricting to the normal core.
- **Products with `Z`:** use `X × R`.

`P_n = ker(lk_{12}) × ⟨Δ²⟩` with `ker(lk_{12}) ≅ PMod(S_{0,n+1})`, which has
finite index in `Mod(S_{0,n+1})`. So, for each `n`, **`B_n` acts properly on a
proper CAT(0) space iff `Mod(S_{0,n+1})` does**, iff `B_n/Z(B_n)` does.

The hole is therefore the genus-0 case of "does `Mod(S)` act properly on a proper
CAT(0) space". For closed genus `g ≥ 3`, Kapovich–Leeb rule out proper
*semisimple* actions. This was recorded in the artifact, §6, and not made a
separate node, because it is a reformulation and not progress.

## Approaches and where each dies

1. **Semisimplicity (Kapovich–Leeb / Bridson template).**
   - **Idea.** Force an infinite-order element to have `|γ| = 0`. Semisimplicity
     then makes it elliptic, which contradicts properness.
   - **Where it dies.**
     - Proper actions on proper spaces need not be semisimple. A neutral
       parabolic of infinite order is compatible with properness, so step 2
       needs cocompactness.
     - Step 1 already fails for braids: by the new theorem no infinite-order
       element of `B_n` or `Mod(S_{0,n+1})` is torsion in the abelianization of
       its centralizer.
     - Step 1 also fails after passing to finite-index overgroups (Lemma P(ii)),
       so induction to `X^m` cannot rescue it.
2. **Busemann characters for non-neutral parabolics.**
   - **Idea.** Karlsson–Margulis gives a fixed point at infinity, and the
     Busemann homomorphism gives a character.
   - **Where it dies.** It needs the same centralizer-torsion input as 1, so it
     is subsumed.
3. **Residual finiteness or linearity-type obstructions.**
   - **Where it dies.** They cannot work, because a proper action on a proper
     CAT(0) space implies neither.
   - **Example.** `BS(2,3) = ⟨a, t | t a² t⁻¹ = a³⟩` is non-Hopfian, hence not
     residually finite, yet it acts properly on the proper CAT(0) space `H² × T`.
     - On `H²`: `a ↦ (x ↦ x + 1)` and `t ↦ (x ↦ 3x/2)`, affine maps of the upper
       half-plane.
     - On `T`: the Bass–Serre tree, locally finite of valence 5.
     - Properness: fix a vertex `v` and `r > 0`. The tree is locally finite, so
       the elements moving `v` by at most `r` form finitely many cosets
       `g_i Stab(v)`. `Stab(v)` is a conjugate of `⟨a⟩`, which acts on `H²` by a
       discrete group of parabolic translations, hence properly. So for compact
       `K ⊆ H²`, only finitely many `s` in each coset meet `K` back. (Referee
       expansion of the solver's one-line argument.)
     - Checked by hand: `t a² t⁻¹` is `x ↦ x + 3`.
   - In any case `B_n` is linear (Bigelow, Krammer), hence residually finite.
     Whether it is linear over a number field is open.
4. **Coarse geometry.**
   - **Where it dies.** `B_n` has finite asymptotic dimension, as mapping class
     groups do (Bestvina–Bromberg–Fujiwara). Finite asymptotic dimension gives a
     coarse embedding into a finite product of locally finite trees
     (Dranishnikov). Both citations are unverified in this pass.
   - So coarse embeddability into a proper CAT(0) space gives no obstruction
     (the orbit map of a proper action is a coarse embedding), and any
     obstruction must be equivariant.
5. **Amenable and abelian subgroups.**
   - **Where it dies.** Abelian subgroups of `B_n` are free abelian of rank at
     most `n − 1` and `B_n` is torsion-free. Proper actions of `Z^r` on proper
     CAT(0) spaces exist with no restriction (e.g. on `R^r`).
   - The Flat Torus and Solvable Subgroup theorems need semisimplicity or
     cocompactness, so they give nothing for proper actions.
6. **Linear representations (the negation side).**
   - **Where it dies.** The number-field route
     (`braid-proper-cat0-action-via-number-field-linearity`) dies at
     transcendence. Lawrence–Krammer–Bigelow is faithful at generic
     transcendental parameters, and faithfulness at algebraic specializations is
     not known.
   - Quantum representations have images defined over number fields but are
     only asymptotically faithful, so they reduce to the same open question.
     This side is recorded here only for orientation.
7. **Weil–Petersson completion of Teichmüller space.**
   - **Where it dies.** For `S_{0,n+1}` it is CAT(0) and `Mod` acts on it, but
     the space is not locally compact and multitwists fix boundary strata. So
     the action is neither on a proper space nor proper, and it gives no
     positive answer either.

## What remains open

- **The hole itself.** No candidate obstruction survives. Any proof that some
  `B_n` has no proper action on a proper CAT(0) space must use one of:
  - relations among translation lengths of **non-commuting** elements;
  - the local compactness of `X`, through the topology of `∂X` or through the
    structure of neutral parabolics in locally compact CAT(0) spaces;
  - rigidity for higher-rank free abelian subgroups (rank `n − 1` in `B_n`)
    without semisimplicity.

  The new theorem shows that abelian characters of single centralizers are
  exhausted.
- **A natural test case.** Is there an isometric action of `B_n` (`n ≥ 8`) on a
  complete CAT(0) space in which some infinite-order braid is neutral? The new
  theorem says the centralizer mechanism never forces this. It is not known
  whether anything else does.
- **Unverified in this pass.**
  - The Bregman–Libgober–Zhu non-CAT(0) mechanism (abstract only).
  - Kapovich–Leeb's exact statement (known through Bridson's quote).
  - Statement numbers for the standard mapping class group inputs used by the
    new route: Farb–Margalit, Ivanov, Birman–Lubotzky–McCarthy, McCarthy.

## Files

- `research/braid-centralizer-characters-detect-infinite-order.md` (claim)
- `research/braid-centralizer-characters-detect-infinite-order-proof.md` (route,
  `requires: []`)
- `research/artifacts/braid-centralizer-characters-2026-09-16.md` (artifact)
- `experiments/braid-centralizer-characters-2026-09-16/check_laminar_and_lk.py`
  and `output.txt`
- this note

## Referee (2026-09-16)

**What was checked.**
- **Files.** All six listed files were read in full. `git status` shows no
  unlisted solver files with this slug.
- **Duplicates.** `bin/cairn search --similar` and `bin/cairn search centralizer`
  found no existing claim with this statement.
- **Proof, step by step.**
  - Lemma T: transfer of a central element and the rescaling `N ψ(g^j) = j ψ(g^N)`.
  - Lemma P (i)–(iii).
  - Lemma L: private pairs, the incidence `p_A ⊆ B ⇔ A ⊆ B`, unitriangularity.
  - Step 2: finite index of `H`, `H ≤ P_n`, `g ∈ H`.
  - Case A: `θ(H) ≤ Z(φ)`, the cyclic subgroup, the character on `H'`.
  - Case B: the multitwist decomposition, the linking vector, and why `F` is
    laminar, injective and has sizes in `[2, n−1]`.
  - Theorem (b): the splitting `P_n = ker(lk_{12}) × ⟨Δ²⟩` and the index `(n+1)!`.
  No gap found. For the forgetful map, the twist about `c` becomes `σ_1²` in
  `P_2` if `c` encloses both strands and is trivial otherwise.
- **Experiment.** Re-ran `check_laminar_and_lk.py` (exit 0). Its output
  matches `output.txt` exactly.
- **Bridson citation.** Fetched the arXiv:0908.0685 LaTeX source
  (`anogiaARXIV.tex`). Proposition `l:hyp`, Theorem `t:paras` with its
  Karlsson–Margulis/Busemann proof, Remark `r:abelian` (induction to `X^n`), the
  Kapovich–Leeb attribution, and the `B_n → Mod(S_{0,n+1})` discussion in
  §`s:genus2` all match the quotes.
- **Standard inputs.** Pinned through Chen–Salter arXiv:1804.11235v1 §2 (ar5iv):
  - (N1) is Farb–Margalit Corollary 13.3, with Chen–Salter Proposition 2.2;
  - (N3) is McCarthy Theorem 1, which is Chen–Salter Proposition 2.6;
  - (N2) is Farb–Margalit Proposition 3.20, a number taken from a committed
    repository artifact.
  The Farb–Margalit book itself could not be fetched (HTTP 403).

**What was changed.**
- The claim and the artifact no longer say that Kapovich–Leeb's proof uses the
  centralizer mechanism. They now say Bridson's argument recovers the theorem,
  and that Kapovich–Leeb's own proof was not read.
- "Gives no constraint on any isometric action" became "forces nothing beyond
  finite order".
- Added the statement-number pins above to the route and the artifact.
- Notes:
  - removed the false "landed `abc9e1536`" (that hash is an unrelated commit);
  - expanded the properness argument for `BS(2,3)` on `H² × T`;
  - narrowed "no coarse obstruction exists" to coarse embeddability.
- Added one `## Attempts` bullet to `some-braid-group-has-no-proper-cat0-action`
  pointing to the new claim.

**Verdict.** Landed with fixes.
- The theorem that every infinite-order braid has infinite order in the
  abelianization of its centralizer is sound as a direct proof, given textbook
  Nielsen–Thurston inputs (a literature import in the README's sense).
- The CAT(0) consequence removes exactly one mechanism, the centralizer-character
  criterion. It does not advance the target, which stays OPEN.
