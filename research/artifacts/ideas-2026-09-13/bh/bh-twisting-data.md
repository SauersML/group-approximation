# Idea lane bh-twisting-data: twisting data as the carrier of the algorithm

Target: `boone-higman-conjecture`.

Lens: twisted Brin--Thompson groups `SV_G`, Stein and Higman--Thompson type
twists, and Röver--Nekrashevych twists at cloned positions. Known envelopes put
the input group into the twist. The question here is whether the twist itself
can carry the input's word-problem algorithm without being finite-state or
tree-realizable, and whether the finite-presentation proofs survive computable
rather than finite twisting data.

Status: ideation only. Nothing here is claimed established, and no Cairn node
was edited.

## Sources actually checked

- Zaremsky, *Finite presentability of twisted Brin--Thompson groups*,
  arXiv:2405.18354v2, dated November 27, 2024. PDF text extracted and read
  locally. Items used, all quoted from that text:
  - **Theorem A:** "Let G be a group acting faithfully on a set S. Then the
    twisted Brin–Thompson group SV_G is finitely presented if and only if the
    action of G on S is of type (A)."
  - **Proposition 2.1:** "If SV_G is finitely presented, then the action of G
    on S is of type (A)." The proof shows `Z ≀_S G` is a quasi-retract of
    `SV_G`, then applies Citation 2.2 (Cornulier [dC06, Theorem 1.1]): "For
    W ≠ {1}, the group W ≀_S G is finitely presented if and only if W is
    finitely presented and the action of G on S is of type (A)."
  - **Proposition 3.1** (finite presentation with bad edge stabilizers). Let K
    be a simply connected simplicial complex, and Γ a group acting cocompactly
    and orientation-preservingly on K with every vertex stabilizer finitely
    presented. Suppose that for each edge e = {v,w} there is an edge path
    e_1, ..., e_n from v to w whose stabilizers are finitely generated and
    whose intersection has finite index in Γ_e. Then Γ is finitely presented.
  - **Lemma 4.5 (Cocompact):** finitely many G-orbits of k-element subsets
    make the action of `SV_G` on `X_m(k)` cocompact.
  - **Lemma 4.9 (Long edge stabilizers):** a long edge is joined by a path of
    short edges.
  - **Proposition 5.3:** every finitely presented, strongly shift-similar
    `G ≤ Sym(N)` admits an action of type (A).
  - **Corollary 5.4:** not every finitely presented group embeds into a
    finitely presented strongly shift-similar group.
  - **Corollaries 5.11 and 5.12:** type (A) from a finitely generated,
    non-normal simple subgroup with finitely many double cosets. The source's
    remark: "if the two embeddings from the Boone–Higman–Thompson theorem can
    be done in such a way as to ensure finitely many double cosets (and
    non-normality), then the conjecture holds."
  - The bibliography entry [MZ] is Mallery--Zaremsky, arXiv:2202.00822.
- Belk--Zaremsky, *Twisted Brin--Thompson groups*, arXiv:2001.04579. Read at
  search-summary level only.
- arXiv:2209.11982, on obstructions for subgroups of nV and SV_G: the arXiv
  page says the paper is **withdrawn** due to a flaw in a proof. It is not
  used here.
- Repo nodes read on origin/main:
  - `twisted-brin-thompson-finite-presentation-criterion`
  - `twisted-brin-thompson-wp-equals-actor-orbit-problem` (statement and part
    (a); part (c) only as summarized in other nodes)
  - `type-a-actors-with-arbitrarily-hard-word-problem` (OPEN)
  - `arbitrarily-complex-fp-simple-via-hard-type-a-actors`
  - `complexity-bounded-host-classes-are-not-universal`
  - `rational-homeomorphism-subgroups-have-exponential-wp`
  - `decidable-fp-groups-need-not-embed-in-rational-group`
  - `baumslag-gersten-embeds-in-no-rover-nekrashevych-group`
  - `decidable-groups-embed-in-rover-nekrashevych-hosts` (REFUTED)
  - `decidable-inputs-have-fp-shell-envelopes` (OPEN)
  - `decidable-inputs-have-computable-non-fp-shell-envelopes`
  - `shell-recursive-presentations-compute-enumerations`
  - `boone-higman-via-fp-shell-envelopes`
  - `mallery-zaremsky-shift-similar-envelope`
  - `boone-higman-via-shift-higman-compiler`
  - `compilers-cannot-drop-the-decidability-hypothesis`
  - `fp-strongly-shift-similar-admits-type-a-action`
  - `fp-full-binary-cantor-groups-have-type-a-actions`
  - the root's September 8 sections on shell stabilizer overgroups and the
    computable-core automorphism upgrade.

## Approach T1: computable, non-type-(A) twisting action for `SV_G`

**Idea.** Take `G` finitely presented, containing the input, acting on a
countable set `S` through a computable but wild action, with infinitely many
orbits of pairs, carrying the input's algorithm in its orbit structure. Hope
that `SV_G` is still finitely presented, because the Stein complex proof might
only need local data.

**What it would prove.** Finitely presented simple twisted Brin--Thompson hosts
for inputs with no type (A) actor, bypassing the OPEN hard-actor premise.

**Kill test.** Does finite presentation of `SV_G` force type (A) with no
faithfulness or finite-state hypothesis?

**Result.** Yes: Zaremsky Proposition 2.1. The proof makes `Z ≀_S G` a
quasi-retract of `SV_G`, and Cornulier's theorem forces type (A) for any
finitely presented permutational wreath product with nontrivial finitely
presented base. So every finitely presented `SV_G` has an orbit-finite-on-pairs
twist with finitely generated point stabilizers.

**Verdict: killed.** In twisted Brin--Thompson hosts, finite presentation
forces *orbit-finiteness of the twist on pairs*. It does **not** force the twist
to be finite-state: type (A) actions are not known to have bounded orbit
problems. So the algorithm can only live inside a type (A) actor, which is
exactly the OPEN `type-a-actors-with-arbitrarily-hard-word-problem`.

## Approach T2: hide the algorithm in higher-arity orbit data

**Idea.** Type (A) constrains only 2-element subsets and point stabilizers.
Let the input's hard decision problem sit in the orbits of triples, or in
stabilizers of finite sets of size ≥ 2, which condition (A) leaves free. The
twist would be "type (A) on pairs, arbitrarily complex above".

**What it would prove.** A way to put hardness into finitely presented simple
hosts while keeping the pair-orbit condition cheap.

**Kill test.** Can hardness invisible to the orbit problem `OP(G,S)` raise the
word problem of `SV_G`? If not, hosts built this way contain only inputs whose
word problems reduce to `OP(G,S)`.

**Result.**
- By (a) of `twisted-brin-thompson-wp-equals-actor-orbit-problem`, `OP(G,S)`
  (the word problem of G plus point-stabilizer membership) reduces to the word
  problem of `SV_G` in linear time. As summarized in
  `type-a-actors-with-arbitrarily-hard-word-problem` and
  `arbitrarily-complex-fp-simple-via-hard-type-a-actors`, finitely presented
  twisted Brin--Thompson hosts beat a recursive bound only if their actors do.
  I did not re-derive part (c).
- Any input inside `SV_G` has its word problem reduce to `SV_G`'s. So data
  that doesn't show in `OP(G,S)` is never seen by the host's word problem.

**Verdict: killed as a carrier; kept as a constraint.** The algorithm must be
visible in the actor's own word problem or in point-stabilizer membership.
Triple-orbit complexity can matter structurally, e.g. for which inputs embed,
but it adds no complexity budget.

## Approach T3: shift-similar twists (ψ_j recursion on N instead of a tree)

**Idea.**
- The shift maps `ψ_j` on `Sym(N)` are a twist at a deleted position, like a
  Röver--Nekrashevych twist at a cloned position, but on N with no locally
  finite tree.
- The input's algorithm would be encoded in the ψ_j-recursion.
- Mallery--Zaremsky embed every finitely generated group in a finitely
  generated strongly shift-similar group. Proposition 5.3 gives type (A)
  whenever such a group is finitely presented.
- Corollary 5.4 only rules out inputs with unsolvable word problem.

**What it would prove.** BH, via "every f.g. group with solvable word problem
embeds in a finitely presented strongly shift-similar group". This also avoids
the locally-finite-tree and Deligne/BG walls, which concern `Aut(T_d)` and
almost-automorphism hosts.

**Kill test.** Is this already a recorded route on main?

**Result.**
- Yes. `boone-higman-via-shift-higman-compiler` routes every decidable input
  through Clapham's finitely presented overgroup and a bijection `ν: P → N`
  making the Mallery--Zaremsky envelope `E_ν(P)` finitely presented, then
  applies Proposition 5.3 and Corollary B.
- `compilers-cannot-drop-the-decidability-hypothesis` shows that finite
  presentation of `E_ν(P)` forces solvable word problem. That is consistent
  with Corollary 5.4 and explains why ν must carry the decision procedure.
- The shell envelope `E_nu = <V, hat(P)>` of the shell nodes seems to be the
  same kind of ν-envelope. Unverified: I did not check that the two
  constructions coincide.

**Verdict: killed as a duplicate.** This twist lens on shift-similar groups
*is* the existing ν-compiler route. Its premise is that some computable ν gives
a finitely presented envelope, and `decidable-inputs-have-fp-shell-envelopes`
is OPEN. What this lens adds is the reading "ν is the twisting data".

## Approach T4: prove finite presentation of ν-envelopes with bad edge stabilizers

**Idea.** The OPEN premise is finite presentation of `E_ν` for a suitable
computable ν. Stein-complex finite-presentation proofs usually need finitely
generated edge stabilizers, and for computable ν the long-edge stabilizers
presumably see infinite ν-data. Zaremsky's Proposition 3.1 allows a bad edge if
a path of good (finitely generated) edges joins its endpoints with a
finite-index intersection of stabilizers. That is exactly his Lemma 4.9 pattern
for long versus short edges in `X(k)`. The plan:
1. build a Stein-type complex for `E_ν`, with vertices as ν-expansions;
2. let short edges be the elementary splits away from the singularity, whose
   stabilizers should be finitely generated because point stabilizers of `E_ν`
   are finitely generated for every ν (as stated in
   `boone-higman-via-fp-shell-envelopes`);
3. isolate the separating property of ν as "every long edge is joined by short
   edges whose stabilizers meet in finite index".

**What it would prove.** A checkable, local sufficient condition on ν for
finite presentation of `E_ν`, hence BH through the recorded shell /
shift-compiler routes, whenever a computable ν satisfying it exists for each
decidable input.

**Kill tests.**
1. Does main already have a Stein complex or a Proposition 3.1-type argument
   for shell envelopes?
2. Is the condition vacuous or impossible for computable ν?

**Results.**
1. The grep of shell nodes and Boone--Higman artifacts on origin/main for
   "Stein complex" and "bad edge stabilizers" found only the Leavitt-host and
   frontier artifacts, and there "Proposition 3.1" refers to a different
   source. No shell node uses Zaremsky's Proposition 3.1.
2. `decidable-inputs-have-computable-non-fp-shell-envelopes` produces computable
   ν with non-finitely-presented `E_ν` in every finite-prescription
   neighbourhood. So any sufficient condition must fail on those ν. The
   finite-index-intersection condition is a plausible separating property,
   since it concerns how ν interleaves stabilizers along a path, not
   computability alone. Not tested:
   - cocompactness of the `E_ν`-action on such a complex, which would need
     finitely many orbits of k-configurations, as in Lemma 4.5;
   - simple connectivity of the sublevel complexes.

**Verdict: unclear, the best survivor of this lens.** Next test: write the
Stein-type complex for the virtually cyclic case, where finitely presented
shell envelopes are known to exist near every finite prescription. Check
whether the good ν there satisfy the Proposition 3.1 path condition and the bad
computable ν violate it. If the condition tracks finite presentation there, it
becomes a concrete target for arbitrary decidable inputs.

## Approach T5: double-coset twist (Zaremsky Corollary 5.11)

**Idea.** Choose the simple subgroup H of the Boone--Higman--Thompson embedding
as a twisted group over a computable action, so that H\G/H is finite and H is
not normal. Corollary 5.11 then gives type (A) directly, and the source says
this would prove the conjecture.

**What it would prove.** BH, from finitely many double cosets of a finitely
generated simple subgroup in a finitely presented overgroup.

**Kill test.** Is this a recorded route, and are there recorded obstructions
to finite bi-index?

**Result.**
- Recorded. The root's September 8 section describes
  `boone-higman-via-shell-stabilizer-overgroups`: keep H, get a faithful coset
  action with finitely generated point stabilizers, and "the remaining type
  (A) condition is finite bi-index of H in Γ".
- `shell-finite-biindex-hosts-require-large-intersections` forces the shell
  envelope to meet every conjugate infinitely, and proper almost malnormal
  hosts fail.
- `terminated-digit-host-has-infinite-shell-biindex` gives infinitely many
  double cosets in one restricted model.

**Verdict: killed as a duplicate.** Corollary 5.11 is the published form of the
existing finite bi-index premise; the twist adds nothing to it.

## Synthesis for this lens

- **Pairs.** Finite presentation of twisted Brin--Thompson hosts forces the
  twist to be orbit-finite on pairs with finitely generated point stabilizers
  (T1, via Cornulier). It does not force finite-state-ness.
- **Where the algorithm lives.** In the actor's word problem or stabilizer
  membership (T2), or in the enumeration ν of the ν-envelope (T3). All three
  places already sit behind recorded OPEN premises:
  `type-a-actors-with-arbitrarily-hard-word-problem` and
  `decidable-inputs-have-fp-shell-envelopes` /
  `boone-higman-via-shift-higman-compiler`.
- **New contribution.** T4: Zaremsky's bad-edge-stabilizer criterion as a
  concrete, local test separating good ν from computable bad ν in the
  ν-envelope premise.
