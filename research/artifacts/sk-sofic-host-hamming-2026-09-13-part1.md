# sk-sofic-host-hamming, part 1: the permanence closure cannot produce the hosts

Lane `sk-sofic-host-hamming` (ROSTER-H), 2026-09-13. Question (rev4 candidate, decision 79): is every finitely
generated sofic group a subgroup of an infinite finitely generated simple Kazhdan **sofic** group? Open node:
`sofic-groups-embed-in-simple-kazhdan-sofic-groups`. Everything below is unreviewed.

## 0. Summary

- **Already on main:**
  - algebraic models through gap targets are local embeddings (`gap-sofic-approximations-are-local-embeddings`);
  - the question costs a non-LEF sofic simple Kazhdan group (`sofic-universal-envelope-forces-non-lef-simple-kazhdan`,
    PASS);
  - Kazhdan subgroups of amenable orbit full groups are RF (`kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`);
  - an ergodic centralizer forces LEF (`kazhdan-ergodic-sofic-centralizer-forces-lef`);
  - the IRS soficity test (`almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`);
  - landed today by sk-fp-sofic-host: finitely presented Kazhdan groups in the permanence closure of the LEA groups are
    residually finite (`lea-permanence-closure-fp-kazhdan-groups-are-residually-finite`).
- **Theorem K (§3).**
  - **Class 𝒫:** start from amenable and LEF groups; close under subgroups, directed unions, finite direct products,
    extensions with amenable quotient, fundamental groups of graphs of groups (any edge groups), and limits in the space
    of marked groups.
  - **Statement:** every finitely generated Kazhdan group in 𝒫 is LEF.
  - **Relation to the peer result.** Theorem K is the finitely generated form of the peer result. It is what the hosts
    need, because infinite simple LEF groups, and the lamplighter hosts, are not finitely presented. It also allows
    iterated marked limits.
- **Consequences (§3.4).**
  - A host for a non-LEF input lies outside 𝒫.
  - A positive answer to Alekseev–Thom Open problem 6.1 lies outside 𝒫, as the peer result already shows.
  - Deligne's lattice and de Cornulier's groups lie outside 𝒫.
- **Lemma E (§4).** If a measure-preserving action has exactly equivariant finite models, every finitely generated
  subgroup of its orbit full group is LEF. This covers profinite actions, Bernoulli shifts of LEF groups, and the dual
  actions of the note's groups through their linear finite models. So full groups give soficity beyond LEF only through
  *inexact* models of the action.
- **Statement check (§2).** Open problem 6.1, read at source, asks exactly for a finitely presented sofic Kazhdan group
  that is not residually finite. The rev4 wording "A sofic example would also answer Open problem 6.1" (decision 79,
  a-U9) is right.
- **Where a positive answer must come from (§5), and next targets (§6).**

## 1. Conventions

- **Marked groups.** `(G,S)` with `S` a finite ordered generating set; the topology is agreement of balls. LEF groups
  form a closed set, closed under subgroups and finite direct products.
- **Openness of (T).** Kazhdan groups form an open subset of the space of marked groups (Shalom;
  `fpbs-shalom-property-t-is-open`).
- **Standard facts:**
  - quotients and finite-index subgroups of Kazhdan groups are Kazhdan;
  - a countable amenable Kazhdan group is finite;
  - property (T) implies Serre's property FA (Watatani 1982), so a Kazhdan subgroup of the fundamental group of a graph
    of groups lies in a conjugate of a vertex group.

## 2. Alekseev–Thom at source

`arXiv:2608.05362v1`, `main_final.tex`, fetched on MSI 2026-09-13; lines 1705–1732 verbatim:

> Let's review some of the known examples: First, the second author constructed a Kazhdan group which is locally
> embeddable into finite groups, hence sofic, but not residually finite \cite{ThomHyperlinear}. Since a discrete
> Kazhdan group is finitely generated, this gives a finitely generated sofic Kazhdan group which is not residually
> finite. It is not finitely presented: every finitely presented LEF group is residually finite, because the finite
> presentation turns sufficiently good local embeddings into genuine finite homomorphisms. Second, de Cornulier
> constructed finitely presentable non-Hopfian Kazhdan groups \cite{deCornulier}. Since finitely generated residually
> finite groups are Hopfian, these groups are not residually finite. Related examples are known to be hyperlinear by
> work of the second author \cite{ThomHyperlinear}, but they are not known to be sofic. Third, Kar and Nikolov
> constructed finitely presented sofic groups which are not residually finite \cite{KarNikolov}. These examples do
> not have Kazhdan's property.

> \begin{openproblem} Are there examples of finitely presented sofic groups with Kazhdan's property~\((T)\) that are
> not residually finite? \end{openproblem}

**Deligne's lattice.** The preimage `Γ~` of `Sp_2n(Z)`, `n ≥ 2`, in the universal cover
(`deligne-universal-cover-lattice-is-non-rf-kazhdan`) is finitely presented, Kazhdan and not residually finite. It is a
central `Z`-extension of a residually finite group, and soficity is not known to pass through amenable-by-sofic
extensions. So `Γ~` answers 6.1 only if it is proved sofic, and `deligne-triple-cover-is-sofic` is open on main.

**Warning for any lane:** the permanence theorems cover sofic-by-amenable extensions, not amenable-by-sofic ones.

## 3. Theorem K

### 3.1 The class

Put `𝒫_0` = amenable groups ∪ LEF groups. Given `𝒫_α`, let `𝒫_(α+1)` consist of `𝒫_α` together with every group obtained
by one of:
- **(O1)** a subgroup of a member;
- **(O2)** a directed union of members;
- **(O3)** a finite direct product of members;
- **(O4)** `G` with a normal subgroup `N ∈ 𝒫_α` and `G/N` amenable;
- **(O5)** the fundamental group of a graph of groups with vertex groups in `𝒫_α`, for any edge groups;
- **(O6)** the limit, in the space of marked groups, of finitely generated members.

Take unions at limit ordinals, and let `𝒫 = ⋃_α 𝒫_α`.

**What 𝒫 contains.** The permanence theorems below are recalled, not re-read by this lane.
- sofic-by-amenable extensions, by (O4) (Elek–Szabó 2006);
- amalgams and HNN extensions over amenable subgroups, by (O5) (Elek–Szabó 2011, Păunescu 2011, Dykema–Kerr–Pichot 2014);
- graph products, as iterated amalgams (Ciobanu–Holt–Rees 2014);
- wreath products with amenable top group: `⊕_X A` is a directed union of finite products, then (O4);
- LEA groups, by (O6).

With amenable edge groups every member is sofic. (O5) with non-amenable edge groups is allowed only because the proof
never uses the edge groups.

### 3.2 Statement

**Theorem K.** Every finitely generated Kazhdan group that is a subgroup of a member of 𝒫 is LEF.

### 3.3 Proof

Write `P(α)`: every finitely generated Kazhdan subgroup of a member of `𝒫_α` is LEF. Induct on `α`. Limit ordinals are
immediate. The induction follows `lea-permanence-closure-fp-kazhdan-rf-proof`, with LEF in place of residual finiteness
and openness of (T) in the limit step.

**`α = 0`.** A Kazhdan subgroup of an amenable group is amenable and Kazhdan, so finite. A subgroup of a LEF group is LEF.

**Step `α → α+1`.** Let `G` be a finitely generated Kazhdan group with `G ≤ H`, where `H` comes from `𝒫_α` by one
operation.
- **(O1)** `H ≤ H′ ∈ 𝒫_α`, so `G ≤ H′`, and `P(α)` applies.
- **(O2)** `G` is finitely generated, so it lies in one member of the union.
- **(O3)** `H = H_1 × … × H_m`. Each projection `p_i(G)` is a finitely generated Kazhdan subgroup of `H_i`, so it is LEF.
  So `G ≤ ∏ p_i(G)` is LEF.
- **(O4)** `N ⊲ H`, `N ∈ 𝒫_α`, `H/N` amenable.
  - `K = G ∩ N` is normal in `G`, and `G/K` embeds in `H/N`, so it is amenable and Kazhdan, hence finite.
  - Then `K` has finite index in `G`, so `K` is finitely generated and Kazhdan, and `K ≤ N`. By `P(α)`, `K` is LEF.
  - **Finite extensions of LEF groups are LEF.** `G` embeds in `K ≀ (G/K) = K^(G/K) ⋊ (G/K)` (Kaloujnine–Krasner). If `φ`
    is a partial embedding of a ball of `K` into a finite group `F`, then `(k_q)σ ↦ (φ(k_q))σ` is a partial embedding of
    the corresponding ball of `K ≀ (G/K)` into `F ≀ (G/K)`. The permutation of coordinates commutes with applying `φ`
    coordinatewise.
- **(O5)** `G` has property FA, so it fixes a vertex of the Bass–Serre tree. So `G` lies in a conjugate of a vertex
  group, which is in `𝒫_α`.
- **(O6)** `H = lim (H_k, S_k)` with `H_k ∈ 𝒫_α` finitely generated.
  - Write the generators of `G` as words `w_1, …, w_m` in `S`, and put `G_k = ⟨w_i(S_k)⟩ ≤ H_k`.
  - Balls of `G` in the marking `(w_i)` are read off from balls of `H` of bounded radius, so
    `(G_k, (w_i(S_k))) → (G, (w_i))`.
  - `G` is Kazhdan, and Kazhdan marked groups form an open set, so `G_k` is Kazhdan for all large `k`.
  - By `P(α)` these `G_k` are LEF. LEF is closed in the space of marked groups, so `G` is LEF. ∎

### 3.4 Consequences

1. **Finitely presented case.** An infinite finitely presented Kazhdan group in 𝒫 is residually finite, since finitely
   presented LEF groups are. This recovers `lea-permanence-closure-fp-kazhdan-groups-are-residually-finite`. So positive
   answers to Open problem 6.1 lie outside 𝒫. The examples of §2 fit:
   - Thom's LEF non-RF Kazhdan group is in `𝒫_0` and is not finitely presented;
   - Kar–Nikolov's examples are not Kazhdan;
   - de Cornulier's groups and Deligne's lattice are finitely presented, Kazhdan and not residually finite, so they are
     outside 𝒫.
2. **Simple hosts.** An infinite finitely generated simple Kazhdan group in 𝒫 is LEF. For a non-LEF finitely generated
   sofic input (for example `BS(2,3)`), every simple Kazhdan sofic host is non-LEF, so it lies outside 𝒫. A positive
   answer needs a **seed of soficity that is not a permanence operation**. The finitely presented case does not give
   this: an infinite simple LEF group is never finitely presented.
3. **The lamplighter hosts.** For infinite finitely generated `Δ`, `G_Δ = EL_3(LC(2^Δ,F_2) ⋊ (Z/2 ≀ Δ))` is simple and
   Kazhdan, and it is LEF when `Δ` is LEF. Conversely, `G_Δ` LEF forces `[Δ,Δ]` LEF, since `[Δ,Δ] ≤ [Λ,Λ] ≤ G_Δ` with
   `Λ = Z/2 ≀ Δ` (`perfect-groups-embed-in-crossed-product-elementary-groups`). Whether it forces `Δ` LEF is not
   established. So for `Δ` with `[Δ,Δ]` not LEF, for instance `Δ = C(Γ)` with `Γ` sofic and not LEF
   (`groups-embed-in-derived-subgroup-of-half-line-overgroup`), no permanence argument makes `G_Δ` sofic.
   (Corrected by sk-verify-26, 2026-09-14: this item said "LEF iff `Δ` is LEF", which has no proof on main.)
4. **Scope.** 𝒫 omits orbit full groups of sofic equivalence relations (Elek, arXiv:1211.0621), groups made sofic by new
   approximations, and amenable-by-sofic extensions. §4 and §5 treat these.

## 4. Lemma E: exactly modelled actions only give LEF full groups

**Setting.**
- `Λ` is a countable group acting essentially freely by measure-preserving automorphisms of `(X, μ)`.
- `𝒜` is a countable `Λ`-invariant algebra of measurable sets.
- `W_𝒜(Λ ↷ X)` is the group of Borel bijections `g` with `g(x) = c_g(x)·x`, for some `c_g : X → Λ` of finite range whose
  level sets lie in `𝒜`.

**Exact models.** For every finite symmetric `F ∋ e` in `Λ`, finite subalgebra `𝒜_0 ⊆ 𝒜` and `ε > 0`, there are:
- a finite set `E` and `σ : F·F → Sym(E)` with `σ(λλ′) = σ(λ)σ(λ′)` for `λ, λ′ ∈ F`, and `|Fix σ(λ)| ≤ ε|E|` for
  `λ ∈ F ∖ {e}`;
- a Boolean algebra homomorphism `β` from the algebra generated by `F·𝒜_0` to the subsets of `E`, with
  `β(λA) = σ(λ)β(A)` whenever both sides are defined, and `| |β(A)|/|E| − μ(A) | < ε` for `A ∈ 𝒜_0`.

**Lemma E.** If `Λ ↷ X` has exact models, then every finitely generated subgroup `Γ ≤ W_𝒜(Λ ↷ X)` with
`μ{x : gx ≠ x} > 0` for all `g ≠ 1` is LEF.

*Proof.* Fix a radius `r` and let `B = B_(2r)(Γ)`.
- **The finite data.** By `c_(gh)(x) = c_g(hx)·c_h(x)`, the level sets of `c_g` for `g ∈ B` lie in a finite algebra
  `𝒜_0 ⊆ 𝒜`, generated by translates of the level sets of the generators' cocycles by the finite set `F` of cocycle
  values on `B`.
- **The model.** Take exact models for `(F, 𝒜_0, ε)` and put `ĝ(v) = σ(λ)v` for `v ∈ β{c_g = λ}`.
- **`ĝ` is a permutation.** The sets `{c_g = λ}` partition `X`, and so do the images `λ{c_g = λ}`. `β` is Boolean and
  equivariant, so the sets `β{c_g = λ}` and `σ(λ)β{c_g = λ}` both partition `E`.
- **Exact multiplicativity.** Let `v ∈ β({c_h = λ_2} ∩ λ_2^(-1){c_g = λ_1})`. Then `ĥv = σ(λ_2)v ∈ β{c_g = λ_1}`, so
  `ĝĥv = σ(λ_1λ_2)v`. On `{c_h = λ_2} ∩ λ_2^(-1){c_g = λ_1}` the cocycle of `gh` is `λ_1λ_2`, so `\widehat{gh}v` agrees.
  These sets partition `X`, so `ĝĥ = \widehat{gh}` for `g, h ∈ B_r(Γ)`.
- **Injectivity.** For `g ≠ 1` in `B`, essential freeness gives `μ{c_g ≠ e} = μ{gx ≠ x} > 0`. Off `⋃_λ Fix σ(λ)`, the
  model `ĝ` moves every point of `β{c_g ≠ e}`. There are at least `(μ{c_g ≠ e} − ε − |F|ε)|E| > 0` such points for small
  `ε`. So `ĝ ≠ 1`, and by exactness `ĝ ≠ ĥ` for `g ≠ h` in `B_r(Γ)`.
- So `g ↦ ĝ` is an injective partial homomorphism of `B_r(Γ)` into `Sym(E)`, and `Γ` is LEF. ∎

**Instances with exact models.**
- **(i) Profinite actions** of residually finite groups on `lim Λ/Λ_k`: take `E = Λ/Λ_k`.
- **(ii) Bernoulli shifts `A^Λ` of LEF groups.**
  - Take `ι : B_R(Λ) → Q` an injective partial homomorphism into a finite group, `E = A^Q × Q`, and
    `λ·(c,q) = (c, q ι(λ)^(-1))`.
  - The cylinder `{x : x|_W = p}` goes to `{(c,q) : c(q ι(h)) = p(h) for h ∈ W}`.
  - Equivariance and the Boolean identities are exact on the ball, and the counts are exact because `h ↦ qι(h)` is
    injective on `W`.
- **(iii) The note's groups acting on Pontryagin duals.**
  - `G_X` acts by Haar-preserving automorphisms on the dual `K` of `LC(X × {1,2,3}, F_2)`. The finite models
    `SL_(3N)(F_2)` act exactly on `F_2^(3N)`.
  - Sets defined by finitely many characters are modelled exactly, with counts `2^(−dim)`.
  - Essential freeness holds because `g − 1` has infinite rank for `g ≠ 1`.

**Consequence.** Orbit full groups give soficity beyond LEF only through actions whose finite models are approximately,
not exactly, equivariant. For Kazhdan subgroups, `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf` removes
amenable acting groups. The live full-group seeds are non-amenable, non-LEF sofic `Λ` with sofic orbit relations, for
instance Bernoulli shifts of `BS(2,3) × SL_3(Z)` (sofic, not LEF, not treeable).

## 5. Where a positive answer must come from

| mechanism | status for a non-LEF simple Kazhdan host | node or section |
|---|---|---|
| algebraic finite models (linear, affine, projective) | exact, so LEF | `gap-sofic-approximations-are-local-embeddings` |
| permanence operations from amenable and LEF groups | LEF | Theorem K |
| amenable local embeddings | LEF (openness of (T)) | Theorem K, (O6) |
| orbit full groups, amenable acting group | RF | `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf` |
| orbit full groups, exactly modelled action | LEF | Lemma E |
| sofic embedding with ergodic centralizer | LEF | `kazhdan-ergodic-sofic-centralizer-forces-lef` |
| orbit full group of a non-amenable sofic relation with inexact models | **alive** | §6 T1 |
| new sofic approximations of `EL_n(R)`, `R` simple non-matricial | **alive**; must avoid gap targets; for IRS-rigid hosts a nontrivial almost action suffices | `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial` |
| amenable-by-sofic extensions | not known to preserve soficity | `deligne-triple-cover-is-sofic` (open) |

## 6. Next targets

- **T1: Kazhdan groups of piecewise translations of non-amenable sofic actions.** Is there an infinite simple Kazhdan
  group of bounded piecewise translations of a free measure-preserving action of a sofic group `Λ` with sofic orbit
  relation, which is not LEF? By Elek (arXiv:1211.0621) such a group is sofic, and by Lemma E the models of the action
  must be inexact.
  - Obstruction to test first: if `R_Λ` is treeable, the orbit relation of an essentially free action of the Kazhdan
    subgroup is treeable, which Adams–Spatzier exclude for infinite orbits. The non-free case is not checked.
  - The linear hosts `G_Δ` act by automorphisms of compact groups, not by piecewise translations with finite range. So
    T1 needs permutational Kazhdan groups.
- **T2: property (T) for alternating full groups.** Nekrashevych's `A(𝒢)`, for a minimal expansive groupoid with an
  invariant measure, is finitely generated and simple.
  - For amenable acting groups it is not Kazhdan (amenable orbit full group node).
  - For non-amenable sofic acting groups, whether `A(𝒢)` can be Kazhdan is not settled here. A Kazhdan instance with a
    sofic relation would give a sofic non-LEF simple Kazhdan group.
- **T3: IRS test for `G_Δ`.** If character rigidity extends from `G_X` (`subshift-elementary-groups-are-character-rigid`)
  to the lamplighter hosts, soficity of `G_Δ` needs only a nontrivial almost action. By the gap theorem that almost
  action must have alternating constituents.

## 7. Checked at source, and not

- **Read at source on MSI:** Alekseev–Thom arXiv:2608.05362v1, lines 1690–1745 (§5 examples, §6 open problems).
- **Recalled, not re-read:** Watatani (FA), the permanence theorems of §3.1, Shalom (openness, imported on main),
  Kaloujnine–Krasner, Elek 2012 on full groups, Adams–Spatzier.
- **Credit.**
  - The finitely presented case and the induction pattern are in `lea-permanence-closure-fp-kazhdan-groups-are-residually-finite`
    (sk-fp-sofic-host, landed the same day), which quotes Thom (arXiv:0810.2180) for the base case.
  - Theorem K adds only the finitely generated form with LEF as the conclusion, and iterated marked limits.
  - Bounded novelty check: a grep of main, and Alekseev–Thom §5.
