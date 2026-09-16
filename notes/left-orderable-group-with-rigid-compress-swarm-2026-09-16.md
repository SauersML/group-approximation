# Swarm attack: left-orderable-group-with-rigid-compression-pair (2026-09-16)

Agent `swarm-left-orderable-group-with-rigi`. Lock held on the target for this
session. Nothing was committed.

## Setup

The target asks for `Gamma <= G` with the following properties:

- `G` is left-orderable;
- `Gamma` and `G` have property (T);
- `P_Gamma = { g : g Gamma g^-1 <= Gamma }` generates `G`;
- `Gamma` is not normal in `G`.

It implies Navas's Question 3 (`infinite-left-orderable-kazhdan-group`), through
`infinite-left-orderable-kazhdan-group-from-rigid-pair`. So a positive solution is at
least as hard as that question. The realistic contributions are constraints on how a
witness must look, and status checks.

## Outcome

This is an **obstruction**: necessary conditions on any rigid compression pair. It does
not decide the target. Everything proved is order-free.

New nodes:

- `research/compressed-subgroup-commensurator-has-infinite-index.md`, a claim that
  becomes ESTABLISHED once its route is checked;
- `research/compressed-subgroup-commensurator-has-infinite-index-proof.md`, a route with
  `requires: []`;
- `research/artifacts/compressed-subgroup-commensurator-2026-09-16.md`, carrying the full
  proof, sharpness examples, the credited descent lemma and the literature audit.

## What was proved

The notation is that of the artifact.

1. **Relative index homomorphism.** For commensurable subgroups
   `rho(A,B) = [A : A cap B] / [B : A cap B]`. It is multiplicative on commensurable
   triples and conjugation-invariant. So `Delta(g) = rho(Gamma, g Gamma g^-1)` is a
   homomorphism `Comm_G(Gamma) -> Q^x_{>0}`. On compressors of finite index it equals
   the index.
2. **Proposition 2.1.**
   - A strict compressor of finite index gives `Comm_G(Gamma) ->> Z`, through `v_p o Delta`.
   - If `[G : Comm_G(Gamma)]` is finite, a power of any strict compressor has finite
     index, so again `Comm_G(Gamma) ->> Z`.
3. **Theorem 2.2.**
   - (a) If `Gamma` is infranormal and not normal and `Hom(G,Z) = 0`, some compressor has
     infinite index. The compressors of infinite index generate `G`.
   - (b) If `Gamma` has a strict compressor and no finite-index subgroup of `G` maps onto
     `Z`, then `[G : Comm_G(Gamma)]` is infinite.
   - (c) Kazhdan `G` satisfies both hypotheses. The inputs are BHV Theorem 1.7.1 and
     Corollary 1.3.6, transcribed from the preprint text, plus a direct `l^2(Z)` check.
4. **Sharpness.**
   - `SL_3(Z) x| Z^3` inside `(SL_3(Z) x Z) x| Z[1/2]^3`, where `Z` acts by doubling, is
     a Kazhdan, infranormal, non-normal, commensurated subgroup. So (T) is needed for the
     ambient group, not only for `Gamma`.
   - `Z e_1` inside the Kazhdan group `SL_3(Z[1/2]) x| Z[1/2]^3` has a strict compressor
     of index 2, and every compressor has finite index. So infranormality is needed in
     (a). The (T) input is BHV Remark 2.8.4 ((FH), as a lattice) together with the
     Delorme--Guichardet equivalence stated in BHV's introduction.
5. **Consequences for the target.** A witness `Gamma` is an infinite left-orderable
   Kazhdan group isomorphic to a subgroup of itself of infinite index. It is not
   virtually commensurated by `G`. So any Hecke-pair or scaling construction is dead,
   where the host commensurates the rigid subgroup and compresses it by scalings of
   finite index.
6. **Descent (credited, not new).**
   - Rigid pairs restrict to finite-index normal subgroups of the host. The combinatorics
     are step 2 of `rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group-proof`.
   - Hence the target is equivalent to the existence of a rigid pair whose host is
     *virtually* left-orderable (artifact Corollary 4.2).
   - This is a reformulation, so it was not made a node.

## Approaches tried and where each dies

### (a) Dynamics of the compressor on the line

- Realize `G` in `Homeo_+(R)`. Put `Fix(Gamma)` for the common fixed set and
  `supp(Gamma)` for its complement.
- Each component `I` of `supp(Gamma)` is `Gamma`-invariant, because its endpoints are
  global fixed points. By the trichotomy recorded in the root node, and (T), `Gamma`
  acts on `I` through a type 2 or type 3 action.
- For a compressor `p`, `Fix(Gamma) <= Fix(p Gamma p^-1) = p Fix(Gamma)`. So
  `p(supp Gamma) <= supp Gamma`, and `p` maps each component into a component,
  possibly onto a proper subinterval.
- **Dies:** nothing contradicts this. On `pI`, `p Gamma p^-1` acts conjugately to
  `Gamma` on `I` and sits inside `Gamma`. Excluding it needs a dynamical rigidity
  statement for Kazhdan groups on the line, which is Navas's Question 3 itself.

### (b) Compressions of finite index

This covers affine scalings `v |-> 2v` on a lattice-by-arithmetic Kazhdan group, and
Hecke pairs where the host lies in the commensurator.

- **Dies:** Theorem 2.2. In a Kazhdan host the commensurator has infinite index, and
  some compressor has infinite index.
- These shapes also carry torsion as soon as `SL_n(Z)` with `n >= 3` appears
  (`finite-index-subgroups-of-el-n-are-not-left-orderable`).

### (c) Compressions of infinite index through ring substitutions (the Theorem E shape)

- Monomial substitutions shrink `EL_r(F_q[x_1..x_d])` with infinite index, so this
  shape fits Theorem 2.2.
- **Dies:** in positive characteristic on torsion, and in characteristic zero on
  `finite-index-subgroups-of-el-n-are-not-left-orderable`. That node gives torsion or a
  finite-index subgroup of `SL_n(Z)`.
- Any rigid subgroup of the form `EL_n(R)` with `n >= 3`, or containing one with finite
  index, is dead for the target.

### (d) Virtually left-orderable hosts of known pairs

- By artifact Corollary 4.2, a host with a left-orderable finite-index subgroup would
  suffice.
- **Theorem E host.** It contains the root subgroup `{ e_12(f) }` over the Laurent ring,
  an infinite elementary abelian `p`-group. A finite-index subgroup `H` meets it in a
  subgroup of finite index, which is infinite, so `H` has elements of order `p`.
  **Dies.**
- **Nine-leaf Leavitt pair.** The target node records Thompson's `V` inside it.
  - If `V <= G` and `[G:H]` is finite, then `V cap H` has finite index in `V`.
  - `V` is infinite and simple (standard; Cannon--Floyd--Parry, not re-read here). So `V`
    has no proper subgroup of finite index, and `V <= H`.
  - `V` contains the involution exchanging `[0,1/2)` and `[1/2,1)` by translation, so
    `H` has torsion. **Dies.**
- **Hyperbolic Leavitt cover and Fournier--Facio pair.** Virtual left-orderability of
  their hosts would contain Navas's Question 3 for the rigid subgroup. **Dies** at Q3.

### (e) The target from Navas's Question 3

- A positive answer to Q3 gives a left-orderable Kazhdan `Gamma`. The target also needs
  a left-orderable Kazhdan host in which `Gamma` is infranormal and not normal.
- By Theorem 2.2, `Gamma` must then embed in itself with infinite index.
- The known rigid pairs (Theorem E, nine-leaf Leavitt, hyperbolic Leavitt cover,
  Fournier--Facio) each come from a specific compression mechanism. None of them takes
  an arbitrary Kazhdan group as input.
- **Dies:** no generic construction. The obvious host, an ascending HNN extension of
  `Gamma`, maps onto `Z` and is not Kazhdan.

### (f) Other necessary conditions noted, not made into nodes

- `Gamma` is not a torsion-free hyperbolic group. This rests on three inputs, none
  **re-read here**:
  - property (T) implies (FA) (Watatani);
  - (FA) excludes nontrivial free splittings;
  - freely indecomposable torsion-free hyperbolic groups are co-Hopfian (Sela).

  Theorem 2.2 needs a self-embedding of infinite index, and a co-Hopfian group has no
  proper self-embedding at all. This point is recorded only as a heuristic constraint.
- Relatively Kazhdan amenable variants were already dead in the target's Attempts
  (Alekseev--Bradford, GKEP).

## Literature gate

- **Repository.**
  - Searched with `bin/cairn search --similar` on the new claim text. Hits:
    `finite-bi-index-kazhdan-subgroup-forces-nonamenability`,
    `cd-two-groups-have-no-infranormal-kazhdan-pairs` and others.
  - Also searched `bin/cairn search commensurator` and ran `git grep` for
    "commensurator", "co-Hopf", "relative index", "unimodular" and "Schlichting".
  - No node states the commensurator-index obstruction. `distinct_from` entries were
    added for the closest nodes.
- **Current status of Navas's Question 3.**
  - Vergara, arXiv:2407.03579v3 (8 Dec 2025), p. 1, still calls it open. This is quoted
    in the root node.
  - arXiv API searches on 2026-09-16 found no resolution. Web search was unavailable in
    this session.
  - Later items seen in listings, none resolving the question: 2509.09856v1,
    2608.06222v3 (Kun--Thom), 2608.05362v1, 2609.12196v1 (10 Sep 2026, property (T) for
    quotients of `Aut(F_3)`; orderability not examined), 2607.04038v1, 2609.08428v1,
    2510.17003v2, 2505.07424v2. Only their listing metadata was consulted, not full
    texts.
- **Novelty searches** (arXiv API, 2026-09-16):
  - `abs:"Hecke pair" AND abs:"property (T)"` returned 1405.1540v2 and 1509.06654v2,
    both unrelated;
  - `abs:commensurated AND abs:unimodular AND abs:"property (T)"` returned nothing;
  - `abs:commensurated AND abs:Kazhdan` returned 2507.16677v3, 1811.12226v3,
    1803.08572v2, 1311.0538v2 and math/0306259v1, none stating the result;
  - `abs:infranormal` returned nothing.
  - The obstruction is plausibly folklore via Schlichting completions, since Kazhdan
    locally compact groups are unimodular (BHV Corollary 1.3.6(ii)). No primary source
    stating it was found, and the proof given is self-contained.
- **Verified primary text.** B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property
  (T)*, preprint dated February 23, 2007, read from its text:
  - definition of (T) (introduction);
  - Theorem 1.7.1;
  - Corollary 1.3.6;
  - Theorem 1.4.15 and Corollary 1.4.16;
  - Proposition 1.7.8;
  - Example 1.7.4(i);
  - Remark 2.8.4;
  - the Delorme--Guichardet sentence (introduction).
- **Not fetched and unverified:** Sela's co-Hopficity theorem, Cannon--Floyd--Parry on
  the simplicity of `V`, and all literature on Schlichting completions.

## Certificate boundary

- The established claim concerns discrete groups and uses only algebra plus the two BHV
  statements.
- It does not use or say anything about left orders.
- The target stays OPEN and gated by Navas's Question 3.

## Files touched

- `research/compressed-subgroup-commensurator-has-infinite-index.md` (new)
- `research/compressed-subgroup-commensurator-has-infinite-index-proof.md` (new)
- `research/artifacts/compressed-subgroup-commensurator-2026-09-16.md` (new)
- `notes/left-orderable-group-with-rigid-compress-swarm-2026-09-16.md` (this file)

## Referee (2026-09-16)

**Checked.**

- *Algebra, line by line.*
  - Lemma 0.1(5): the map `x(A cap B cap C) |-> x(B cap C)` is well defined and injective.
  - Lemma 1.1(b),(c): transitivity and multiplicativity of `rho`.
  - Lemma 1.2: products, inverses and the homomorphism identity via Lemma 1.1(d).
  - Lemma 1.3, Proposition 2.1 (the pigeonhole power and the strictness of `t^e`).
  - Theorem 2.2(a),(b): the generation trick `q = p^-1 (pq)`.
  - Lemma 4.1. I re-derived the generation step independently (a Schreier-style
    rewriting with representatives in `P_Gamma`). It matches the lemma in
    `rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group-proof`, step 2.
  - No hidden hypotheses: there is no finite generation, amenability or countability
    assumption, only discreteness.
- *Remark 2.3.* The formula `||pi(s) f_k - f_k||^2 = 2 min(|psi(s)|, k)/k` was
  re-checked numerically for `k < 30` and `|d| <= 40`.
- *Remark 2.4 examples.* Recomputed the conjugation formulas
  `t(A,0,v)t^-1 = (A,0,2v)` and `(A,v)(I,w)(A,v)^-1 = (I,Aw)`, the indices 8 and 2,
  infranormality in the first example, `Comm = G` there, and the infinite orbit of the
  line `Q e_1` in the second.
- *Citations.* I fetched the BHV preprint (perso.univ-rennes1.fr/bachir.bekka/KazhdanTotal.pdf,
  dated February 23, 2007) and extracted its text. These quotes match verbatim, with
  numbering as stated: the Theorem 1.7.1 statement, Corollary 1.3.6, Example 1.7.4(i),
  Remark 2.8.4 and the Delorme--Guichardet sentence. The text also contains Corollary 1.7.2
  (finite-index subgroups of discrete Kazhdan groups have finite abelianization), which is
  exactly the statement-3 input.
- *Duplicates.* `bin/cairn search --similar` gives the nodes already covered by
  `distinct_from`. No node states the commensurator-index obstruction.
- *Status of Navas's Question 3.* An arXiv API search on 2026-09-16
  (`abs:"orderable" AND abs:"property (T)"`, newest first) returned nothing newer than
  2512.04531v2, which is on measure equivalence. No resolution was found. The web search
  budget was exhausted, so no broader search was done.
- *Consistency with known pairs.* The hyperbolic Leavitt cover pair has a non-hyperbolic,
  non-quasiconvex rigid subgroup. So note (f), that a witness is not torsion-free
  hyperbolic, does not conflict with it.

**Changed.**

- Claim node: replaced the declared "**ESTABLISHED**" with "Proved by the direct
  route". Added a Provenance paragraph: `Delta` is the standard Hecke-pair modular
  function, and statement 1 is plausibly folklore through Schlichting completions and
  unimodularity. No novelty is claimed beyond the compression packaging.
- Route and artifact: added the BHV Corollary 1.7.2 reference, which I verified.

**Not verified.** Tzanev-style Hecke-pair literature and Schlichting completions (novelty
only). Sela co-Hopficity, Watatani, and Cannon--Floyd--Parry are used only in these notes,
and they are already marked unverified.

**Verdict.** The direct route is sound and complete. The only external input is BHV,
which I verified. The claim lands as established, with honest provenance. The target
`left-orderable-group-with-rigid-compression-pair` stays OPEN.
