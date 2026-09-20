---
rg: 2
id: proper-sft-domains-admit-no-dual-failures
kind: claim
title: No proper strongly irreducible subshift of finite type maps onto the full shift by a strongly post-surjective automaton that is not pre-injective
distinct_from:
  every-group-is-dual-surjunctive: that is about automata from the full shift to itself; this is about automata from a proper strongly irreducible SFT inside the full shift onto the full shift. Neither statement is recorded as implying the other.
  strict-pairs-admit-post-surjective-decoders: that asks for a decoder that is post-surjective on the whole full shift; this asks that no automaton on a proper strongly irreducible SFT is strongly post-surjective without being pre-injective.
  dual-surjunctive-groups-are-surjunctive: that transfers the full-shift dual statement to surjunctivity group by group; this proper-domain statement implies surjunctivity of the same group directly, through strict-pairs-give-dual-failures-on-bounded-defect-domains.
artifacts:
  - research/artifacts/bounded-defect-domain-duality-2026-09-17.md
---

**OPEN.**

**Statement.** Let `G` be a group and `A` a finite alphabet. Let `X ⊊ A^G` be a strongly irreducible subshift of
finite type, and let `F : X → A^G` be an automaton (continuous and equivariant). Suppose `F` is strongly
post-surjective with lifts inside `X`, as defined in `strict-pairs-give-dual-failures-on-bounded-defect-domains`.
Then `F` is pre-injective on `X`.

The claim is read group by group: "`G` satisfies the claim" means it holds for every `A`, `X` and `F` over `G`.

**Why it matters.** By `strict-pairs-give-dual-failures-on-bounded-defect-domains`, every group that satisfies
the claim is surjunctive. That result needs no choice of decoder. The route `gottschalk-via-proper-domain-duality`
records this.

**Amenable groups (sketch, not imported verbatim).** For amenable `G` the claim holds vacuously: no such `F`
exists, whether or not it is pre-injective.
- By Doucha–Gismatullin (the line-176 quotation in `research/artifacts/gk3-post-surjective-decoders-2026-09-14.md`),
  a strongly post-surjective automaton onto the strongly irreducible target `A^G` is surjective.
- Factor maps do not raise topological entropy. So `log|A| ≤ h(X)`.
- On an amenable group, a proper subshift of `A^G` has entropy strictly below `log|A|`. That is the standard
  input to the Garden of Eden theorem (Ceccherini-Silberstein–Coornaert).
- These together give a contradiction.

**Caution: strong irreducibility is essential.** On nonamenable groups, SFTs built from arrows (each site
points to `k + 1` disjoint targets through bounded injections) carry post-surjective, non-pre-injective maps
onto full shifts. These SFTs appear not to be strongly irreducible. A strongly irreducible example of this
kind would refute the claim on that group.
- This is the main kill-test. It is recorded in the artifact.
- Refuting the claim on one group does not refute Gottschalk.

## Attempts

- **2026-09-17, swarm-0917-w7-w7-gs-last1 [entropy]: sofic calibration, sketch only. OPEN.** On sofic groups
  surjunctivity is already known, so this is a test of the claim, not progress on Gottschalk.
  - **Plan.** Show that no strongly post-surjective automaton maps a proper strongly irreducible SFT
    `X ⊊ A^G` onto `A^G` at all.
  - **Step (i), entropy deficit.** `X` has sofic topological entropy `< log|A|` along every sofic
    approximation, and `−∞` is allowed. The reason is that a forbidden pattern must be avoided on a positive
    proportion of the sites of good models.
  - **Step (ii), no entropy gain.** Take the arbitrary words that serve as microstates of `A^G`, and pull them
    back one site at a time using the lift constant `Φ`. This should give about `|A|^{(1−δ)n}` microstates of
    `X`.
  - **Where it dies.** Step (ii) edits microstates, not genuine points. The lift lemma holds only for genuine
    points, and transferring it to microstates needs the strong irreducibility of `X` in a quantitative form
    that is not proved.
  - **A strongly irreducible SFT with no microstates would break step (ii).** Such an SFT, on a sofic group,
    with a strongly post-surjective map onto a full shift, is the kill-test.
- **2026-09-17, swarm-0917-w7-w7-gs-last1 [arrow-shifts]: nonamenable test domains. Deferred.** Arrow SFTs give
  post-surjective, non-pre-injective maps onto full shifts, but they are not strongly irreducible. The open
  question is whether a strongly irreducible SFT, for instance a strongly irreducible factor or cover of an
  arrow SFT, can keep the post-surjective map. That question was not attacked.
- **2026-09-17, swarm-0917-w8-w8-gs-last1 [finite-models]: fixed-point and microstate counts; bypass by
  constant-point domains. OPEN here; sofic case now proved for the domains the route uses.** Artifact:
  `research/artifacts/constant-point-domain-count-2026-09-17.md`.
  - *Established (`proper-sft-covers-exclude-finite-orbits-and-sofic-constants`).* A proper SFT that strongly
    post-surjects onto `A^G` has no `H`-fixed point for finite-index `H ⊴ G` avoiding an explicit finite set,
    so it has no finite orbit if `G` is residually finite. Over a sofic group it has no constant point. No SI
    and no non-pre-injectivity is used. The method is to lift one coset, or one separated color class, at a
    time, then count words that avoid a forbidden pattern.
  - *Where this attack on the claim as stated dies.* Over residually finite `G`, a counterexample must be an SI
    SFT without periodic points. On free groups, whether one exists is open (arXiv 2401.16774). The
    microstate count needs one point of `X` with sofic microstates, and a general SI SFT on a sofic group is
    not known to have one. This is the same gap as the entropy sketch above.
  - *Bypass.* The domains the route uses always contain the constant `τ(a^G)`. New route
    `gottschalk-via-constant-point-domains` needs only
    `constant-point-sft-domains-admit-no-post-surjective-covers` (OPEN in general, proved for amenable and
    sofic groups).
  - *Side result.* The branching-orientation compression SFT on `F_2` is not SI (cap obstruction, artifact
    §5).
- **2026-09-18, swarm-0917-w8-w8-gs-break [group-rings]: linear sector settled. The claim stays OPEN.** See
  `linear-proper-domain-duality-is-stable-finiteness` (ESTABLISHED, elementary).
  - **Result.** For group subshifts over `F_q^k` with linear automata, the claim holds for `G` exactly when
    `F_q[G]` is stably finite.
  - **One direction.** Under stable finiteness, post-surjectivity at the point `0` alone forces the domain to
    be the whole full shift. So no proper linear domain works. Neither strong irreducibility nor finite type
    is used.
  - **Other direction.** A one-sided inverse `NM = I ≠ MN` gives a counterexample. The domain is
    `X = (A^G)MN`, which is a proper strongly irreducible SFT. The map `x ↦ xM²` on it is strongly
    post-surjective and not pre-injective.
  - **Consequences.**
    - The claim, for all groups, implies Kaplansky stable finiteness over every finite field directly.
    - On every group with stably finite modular group algebras, which includes all sofic groups, any
      counterexample must be nonlinear. Linear kill-tests are dead there.
- **2026-09-19, swarm-0917-w15-w15-gs-break [host-geometry]: ownership and arrow kill-tests are dead. The
  claim stays OPEN.** See `ownership-subshifts-conserve-shell-waste` (ESTABLISHED, elementary).
  - **Target of the attack.** The node caution above, which says the arrow and branching SFTs carrying
    post-surjective, non-pre-injective maps "appear not to be strongly irreducible". The deferred
    arrow-shift step would have made one of them SI.
  - **Result.** Waste is conserved across shells. For an ownership point, the number of unclaimed vertices
    in `T ⊇ QS` is `|T| - k|Q|` minus the claims from the shell `W ⊇ TS^(-1) \ Q`. For an arrow point, the
    indegree excess is `|Q| - 2|T|` plus the arrows from `W`. Both are read from the point on `W`.
    - An SI subshift of `Own(S,k)` or of `X_S` is therefore all-perfect (all-exact) or syndetically
      wasteful.
    - The full shifts contain both kinds of point, by Mendelsohn–Dulmage. So none of them is SI:
      - `Own(S,k)` whenever `e ∈ S` and `Own(S,k+1)` is nonempty;
      - `X_S` whenever some indegree is at least 3;
      - `X_{S^2}` whenever `X_S` is nonempty;
      - on `F_2`, both `Own(B_1,2)` and `X_{B_1}`.
    - Factor images of SI shifts are SI. So the same dichotomy binds every ownership design `π : X -> Own(S,k)`
      whose map reads exclusive data through the claims.
  - **Where it dies.** The surviving candidates are all-perfect or syndetically wasteful SI subshifts of
    ownership or arrow shifts. For `k ≥ 2` they have no finite orbits. On `F_2`, an SFT survivor would
    therefore be an SI SFT without periodic points, which Poirier–Salo (arXiv 2401.16774, after Question
    6.16) suspect does not exist.
  - **Evidence, not proof.** On the all-perfect branch in `F_2`, `experiments/ownership-sft-si-2026-09-17/`
    shows that translates of the explicit perfect point already fail to glue across a perfect shell. The
    deficiency histogram is `{0: 42, 1: 101, 2: 18}` at `n = 5`. This suggests a further tree-branch flux
    invariant, which has not been proved.
- **2026-09-20, swarm-0917-w22-w22-gs-last1 [census-computation]: SI SFTs on `F_2` without periodic points. The
  claim stays OPEN.** See `free-group-bank-sfts-path-mix-but-are-not-strongly-irreducible` (ESTABLISHED).
  - **Target.** The `F_2` gap above: a counterexample must be an SI SFT without periodic points.
  - **Result.** On `F_2`, SI of a nearest-neighbour SFT is exactly half-tree mixing, which is computable. Path
    mixing is strictly weaker.
  - The bank SFTs have no periodic points, no invariant measure and no sofic microstates, by bank conservation.
    They are path-mixing (constant 8 at `K = 4`), but they are not SI: far patterns pin the root symbol at every
    depth.
  - The exact census is 5206 SI pairs at `n = 3` and 1577 at `n = 4`, all periodic.
  - **Where it dies.** No SI `F_2`-SFT without periodic points was found, so there is still no `F_2` kill-test
    domain. The Farkas certificate alone does not contradict half-tree mixing, so proving that SI forces periodic
    points on `F_2` needs a new idea.
- **2026-09-20, swarm-0917-w23-w23-gs-pull [reframing]: the pre-injective clause is inert. This is an
  equivalence and a class kill. The claim stays OPEN.** See `pre-injective-si-cover-pairs-are-conjugacies`
  (ESTABLISHED, unreviewed, elementary).
  - **Result.** A pre-injective SFT cover pair splits as `(Z × A^G, pr_2)`, with `Z = F^-1(d^G)`. The splitting
    comes from a local transport cocycle built out of unique lifts.
    - On an SI domain, `Z` is an SI SFT with no asymptotic pairs, so it is a single constant. Hence `F` is a
      conjugacy `X ≅ A^G`, and if `X ⊊ A^G`, then `G` is not surjunctive.
  - **Equivalence.** This claim at `G` holds iff no proper SI SFT `X ⊊ A^G` carries a strongly post-surjective
    automaton onto `A^G` with lifts in `X`. Pre-injective pairs exist exactly at non-surjunctive groups, and
    this claim already implies surjunctivity. So `PSD ⟺ Gottschalk ∧ PSD_col`, and the bijective fragment is
    exactly Gottschalk, as in the CP split.
  - **Class kill.**
    - The approach: derive pre-injectivity from post-surjectivity on an SI domain, by pruning collisions,
      passing to subsystems or changing the cover.
    - Invariant: pre-injectivity, which is the same as `F` being a conjugacy.
    - Where it dies: at any surjunctive group, pre-injectivity is never attained, so every such scheme
      manufactures a Gottschalk counterexample. Only non-existence proofs survive: entropy, counting, microstates.
    - The w7 "no such `F` at all" plan is therefore not lossy. It is equivalent to this claim.
  - **Side data.** `experiments/psd-tree-sft-census-2026-09-17/` checks all 3-symbol nearest-neighbour tree SFTs
    on `F_2`. There are 84 ordered disjoint-cone pairs, none of them path-mixing, and the witness word is always
    `ab`. So none is SI, which fits Poirier–Salo. This is a finite census.
  - **What is left.** Unchanged in substance, restated: show that no proper SI SFT covers `A^G`. On residually
    finite groups the domain has no periodic point, and on `F_2` no invariant measure.
