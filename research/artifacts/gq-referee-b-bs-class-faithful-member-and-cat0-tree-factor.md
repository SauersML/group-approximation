# gq-referee-b: BLIW Theorem 11.1 in type-(A) form, arithmetic faithful members, CAT(0) with a tree factor (citation and scope lens)

Nodes as landed at 61db7e38a (lane bh-cat0):
- `bs-class-with-faithful-member-lies-in-type-a-class` (+ `bs-class-faithful-member-type-a-proof`);
- `arithmetic-nsp-lattices-have-faithful-bs-members` (+ `arithmetic-nsp-faithful-bs-member-proof`);
- `cat0-groups-with-a-tree-factor-lie-in-type-a-class` (+ `cat0-tree-factor-type-a-proof`).

Referee a passed all three (proof-gap lens). Here, sources are read at source and hypotheses are matched against their
uses.

BLIW is read in the arXiv PDF, arXiv:2408.05673v2 (24 Jan 2025), pp. 2, 18–27. I used the PDF rather than the MSI text
extract. A machine summary of the HTML version misquoted Lemma 10.1, so every statement below comes from the page
images.

**Verdict: PASS for all three.**
- The type-(A) reading of BLIW Theorem 11.1 is right. It is exactly what their Remark 12.7 asserts for `G = F_k`, and
  their proof of Theorem 11.1 uses nothing special about `F_k`.
- The scopes of the two normal subgroup theorem nodes match their uses.
- Strong approximation is pinned. Cocompactness of the definite quaternion group is not (W3).
- Foertsch–Lytchak is pinned. Bridson–Haefliger III.Γ.1.1 is not re-read (W4).

## 1. `bs-class-with-faithful-member-lies-in-type-a-class`

**Definition, p. 24 (§11).** "Given a group `G` we denote by `BS_G` the class of groups consisting of all (finite)
graphs of groups with the property that all edge and vertex groups are abstractly commensurable with `G` and all edge
group inclusions in vertex groups have finite index." This matches the node's Setting. ✓

**Theorem 11.1, p. 24.** "Let `G` be a group of type `F_n` for `n ≥ 2`. Assume that there is a non-trivial group
`H ∈ BS_G` such that `H` acts faithfully on its Bass–Serre tree. Then every `K ∈ BS_G` embeds in a simple group of
type `F_n`."
- The introduction's Theorem C (p. 2) states it with "finitely presented", which is the case `n = 2`. The node's
  hypothesis "`G` finitely presented" is that case. ✓

**The gluing, pp. 24.** The proof ends: "`H_Γ ≤ L_Δ` is a subgraph of groups whose fundamental group acts faithfully
on its associated Bass–Serre tree. Thus, it follows from Lemma 10.1 that `L` acts faithfully on its Bass–Serre tree."
This is quoted correctly in the route.

**Lemma 10.1, p. 21.** It has one hypothesis the route does not state: "assume that `H_Λ ≤ G_Γ` is a subgraph of
groups so that for every edge `e ∈ E(Λ)` we have `H_e = G_e`. ... If `H` acts faithfully on `T_Λ`, then `G` acts
faithfully on `T_Γ`."
- In the gluing, `H_Γ` enters `L_Δ` with its own vertex and edge labels unchanged. So `H_e = G_e` holds, and the
  lemma applies. ✓
- The route's "elementary check", `N ≤ B ≤ H` together with the `H`-invariant subtree, is Lemma 10.1's own proof.
  That proof likewise uses `H_e = G_e`, to identify the subtree `H`-equivariantly with the Bass–Serre tree of `H`. It
  is worth stating (W1).

**The type-(A) reading.**
- The actor is the rigid permutation group `RP_(L̂)(T̂)`:
  - Theorem 10.5 (p. 23) embeds `L` into it via Theorem 9.1 and Lemma 10.2 (p. 22).
  - Proposition 9.2 (p. 19): for every finite `B`, `RP(T, B)` is of type `F_n`.
  - Lemma 8.3 (p. 19): "the `RP_G(Γ)`-action on `V(Γ)` is oligomorphic".
- So the actor is of type `F_n` with `n ≥ 2`, acts oligomorphically, and its finite-set stabilizers are of type `F_n`.
- BLIW's Remark 12.7 (p. 27): "Our proof of Theorem 12.5 shows that for every group in `BS_(F_k)` the permutational
  Boone–Higman Conjecture holds, that is, every such group embeds in a finitely presented group that admits an action
  of type (A) on a countable set in the sense of Zaremsky [Zar24a, Conjecture 5.1]."
- Their proof of Theorem 12.5 (p. 27) is Theorem 11.1 applied with one faithful member, a Burger–Mozes group. So the
  permutational conclusion comes from the proof of 11.1 and 10.5, and it transfers to every `G` with a faithful
  member.
- The node records this as a reading of their proof, with no priority claimed. That is accurate. ✓

**"Known faithful members."**
- Theorem 12.1 (p. 24): "Let `G` be a torsion-free strongly scale-invariant group of type `F_n` for `n ≥ 2`." Its proof
  (p. 25) shows the HNN extension along `f` is faithful. The Heisenberg example is §12.4 (p. 26). ✓
- Theorem 12.5 and Remark 12.7, for `F_k`. ✓

## 2. `arithmetic-nsp-lattices-have-faithful-bs-members`

**Scope of `higher-rank-lattice-normal-subgroups-central-or-finite-index`, instance 1.**
- The node's general statement covers irreducible lattices in higher-rank semisimple Lie groups. Its "Form used in
  this repository" paragraph is written for `Sp_2n(Z)` only.
- For `G ≤ SL_n(Z)`, `n ≥ 3`, the needed facts are standard: `SL_n(R)` is connected and simple of real rank
  `n − 1 ≥ 2`, and `SL_n(Z)` is a lattice, irreducible because `SL_n(R)` is simple. The consumer should state them, as
  that node does for `Sp` (W2).
- (N) is a property of the abstract group `G`, so the choice `L = PGL_n(R)` for (C) is harmless. ✓

**Scope of `bader-shalom-normal-subgroup-theorem`, instance 2.** That node's hypotheses are:
- each `G_i` non-discrete, compactly generated, locally compact and just-non-compact, with no nontrivial abelian normal
  subgroup;
- `Γ` a cocompact lattice in `G_1 × G_2` with dense projections;
- for `n = 2`, no further hypothesis.

The route supplies each one:
- `G_i` = closure of `pr_i(G)`, which is open, since it contains `PSL_2(Q_p)`, and has finite index in `PGL_2(Q_p)`.
  So it is compactly generated.
- `G_i` is non-discrete: the stabilizer of a vertex of the other tree is infinite and embeds in a compact vertex
  stabilizer.
- `G_i` is just-non-compact with no abelian normal subgroups, by the simplicity of `PSL_2(Q_p)` and its trivial
  centralizer.
- `G` is cocompact in `G_1 × G_2`: this is an open subgroup of `L` containing `G`, so `(G_1 × G_2)/G` is closed in the
  compact `L/G`. The route does not say this (W2).
- Projections are dense by definition. ✓

**Strong approximation, pinned.** Rapinchuk, *On strong approximation for algebraic groups*, arXiv:1207.4425,
Theorem 2.3, p. 12: "Let `G` be a connected absolutely almost simple algebraic group over a global field `K`, and let
`S` be a finite set of places of `K`. Then `G` has strong approximation with respect to `S` (i.e., `G(K)` is dense in
`G(A_S)`) if and only if (1) `G` is simply connected; (2) `G_S := ∏_(v∈S) G(K_v)` is noncompact."
- Apply it with `G = SL_1(D)`, which is simply connected, and `S = {∞, q}`. `G_S = SU(2) × SL_2(Q_q)` is noncompact.
- Intersect with the open subgroup `SL_2(Q_p) × ∏_(v∉{∞,p,q}) SL_1(O_v)`. By the p. 7 description of `G(O(S))`, this
  gives the route's density of `SL_1(O[1/pq])` in `SL_2(Q_p)`. ✓
- The route's "with respect to `{q}`" should read `S = {∞, q}`, since `SL_1(D)(R)` is compact (W2).

**Cocompactness of the definite quaternion S-arithmetic group.** Not pinned (W3). The standard source is the
compactness criterion for S-arithmetic subgroups of groups anisotropic over `Q` (Borel; Platonov–Rapinchuk, Thm 5.7),
which I did not read. `D` is a division algebra, so `PD^×` is `Q`-anisotropic, and the compact archimedean factor may
be dropped.

The other steps are correct as written:
- (C), via Zariski density;
- the choice of `c`, hyperbolic at a split `r ∉ {p, q}`, with `G` elliptic there;
- the Lemma: `K ≤ G_1`, `cKc^(−1) = K`, a countable closed normalizer is discrete by Baire, and so `c^m ∈ K`.

**An implicit hypothesis.** The consumer `bs-class-with-faithful-member-lies-in-type-a-class` needs `G` finitely
presented. This holds for both instances: `SL_n(Z)` and its finite-index subgroups, and `Λ` as a CAT(0) group on
`T_p × T_q`. The instance list does not say so (W2).

## 3. `cat0-groups-with-a-tree-factor-lie-in-type-a-class`

- **Foertsch–Lytchak, pinned.** arXiv:math/0605419, Theorem 1.1, p. 2: "Let `X` be a geodesic metric space of finite
  affine rank. Then `X` admits a unique decomposition as a direct product `X = Y_0 × Y_1 × ... × Y_n`, where `Y_0` is a
  Euclidean space ... and the `Y_i` ... are irreducible metric spaces not isometric to the real line nor to a point",
  unique up to a permutation of fibres.
  - `E^n × T` has affine rank at most `n + 1`.
  - A tree with a vertex of degree `≥ 3` is irreducible and not `R`. A nontrivial product would contain a flat square,
    which a tree does not.
  - So every isometry maps `E^n`-fibres to `E^n`-fibres and `T`-fibres to `T`-fibres, and hence splits. This is the
    route's "product preservation". ✓
- **Bieberbach**, and the finite-by-`Z^n` argument: correct as written. ✓
- **BLIW, instance (a).**
  - Theorem 12.3 (p. 25): "For all `k ≥ 1` every group in `BS_(Z^k)` embeds in a simple group of type `F_∞`".
  - Its proof uses `(2Z)^k` via Theorem 12.1, as the route says.
  - Corollary 12.4 (p. 26) is the Leary–Minasyan statement, quoted correctly. ✓
- **The BLIW quote in `arithmetic-nsp-...`**, p. 2: "the only obstruction for applying Theorem C that we are currently
  aware of is that any G satisfying its hypotheses must be residually finite". Verbatim. ✓
- **Priority.** BLIW §12 (pp. 24–27) treats strongly scale-invariant groups, BS groups, Leary–Minasyan groups, higher
  nilpotent groups, free-by-cyclic groups via Burger–Mozes, and Euclidean triangle Artin groups. It does not treat
  arithmetic lattices or `E^n × T` lattices beyond the HNN extensions of `Z^n`. So the nodes' instances are not in
  BLIW. I searched no later literature.

## Warnings

- **W1.** `bs-class-faithful-member-type-a-proof`, Step 1: state that `H_Γ` enters `L_Δ` with its edge groups
  unchanged, `H_e = G_e`. That is the hypothesis of BLIW Lemma 10.1 (p. 21), and the "elementary check" also needs it.
- **W2.** `arithmetic-nsp-faithful-bs-member-proof` needs four additions:
  - the `SL_n` lattice and rank facts for the NST node;
  - cocompactness of `G` in `G_1 × G_2`;
  - strong approximation with `S = {∞, q}`, pinned to Rapinchuk Thm 2.3;
  - the finite presentation of both instances.
- **W3.** Cocompactness of `O[1/pq]^× / Z[1/pq]^×` is unpinned. Keep it in the trust surface, with the
  compactness-criterion reference.
- **W4.** Bridson–Haefliger III.Γ.1.1 (CAT(0) implies finitely presented) and Serre §I.5.4 are standard and were not
  re-read.
