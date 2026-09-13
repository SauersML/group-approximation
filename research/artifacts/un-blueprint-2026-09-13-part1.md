# UN blueprint, part 1: one approximation ladder behind the non-MF paper and the Pestov 9.1 answer

Lane `un-architect`, 2026-09-13. This is the architecture of the UN program. Its rungs were landed in
parallel by the UN lanes, listed in §7. Everything new in this landing is **unreviewed**.

## 0. Thesis

The non-MF paper and the Pestov 9.1 answer are the two ends of one ladder. Over a simple ring, the
matricial approximation type of the Kazhdan elementary groups mirrors the matricial type of the ring.

- **non-MF paper** (`non_mf_groups_exist.tex`, Thm l.918, Cor l.1016): if the coefficient ring is simple and
  not directly finite, every homomorphism from `EL_n(R)` to an MF group is trivial.
- **Pestov 9.1** (`research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`): if the
  coefficient ring embeds in an algebraic ultraproduct of matrix algebras, then `EL_3(R)/Z` is LEF.
- **The mirror pair.** `EL_3(LC(X,F_q) ⋊ Z)/Z` is infinite, simple, Kazhdan and LEF. `EL_N(LC(∂F_d,k) ⋊ F_d)/Z`
  is infinite, simple, Kazhdan and has no MF quotient (`boundary-action-elementary-simple-kazhdan-not-mf`,
  un-paradox). The construction is the same; only the dynamics changes, from measure-carrying to
  paradoxical.

**The ladder** (`R` simple unital; the right-hand column is for finitely generated `R`):

```text
ring rung                                   group rung
exactly matricial (∏_ω M_d(F_k))       <=>?  EL_N(R) LEF for all N                  (L)
unital rank model over k (centre k)    <=>?  EL_N(R)/scalars k-linear sofic, all N    (Σ)
stably finite  <=>  [R] not paradoxical <=>? EL_N(R) operator MF for all N            (M)
```

The Cairn root is `kazhdan-elementary-approximation-type-mirrors-ring-type`. The right-to-left arrows are
established; the left-to-right arrows are the open converses.

## 1. The two theorems, as used (sources on main)

- **Full complementary idempotents** (tex l.918), verbatim hypothesis: "Let $R$ be a countable unital
  associative ring. Suppose that $s,t\in R$ satisfy $ts=1,\ R(1-st)R=R$". Conclusion: "For every $n\ge2$,
  every homomorphism from $\EL_n(R)$ to an MF group is trivial." Node: `full-defect-ring-non-mf-at-rank-two`.
- **Simple infinite rings** (tex l.1016): "If $R$ is a countable simple unital ring that is not directly
  finite, then every homomorphism from $\EL_n(R)$ to an MF group is trivial for every $n\ge2$."
- **Mechanism** (tex l.478, l.646, l.703): one-sided Kazhdan transport plus normal Kazhdan subgroups.
- **Unit groups** (tex l.1218): purely infinite simple `R` gives `Rad_MF(GL_n R) = [GL_n R, GL_n R]` and
  quotient `K_1(R)` (`purely-infinite-unit-group-max-mf-quotient-is-k1`).
- **Traces** (tex l.1349): not MF implies the canonical trace is not quasidiagonal.
- **Pestov answer**, Theorem A:
  - (A1) EJZ Theorem 1.1 (`elementary-groups-over-fg-rings-have-property-t`);
  - (A2) periodic return-word models (`minimal-subshift-algebra-is-simple-lef-ring`);
  - (A3) normal subgroups central or everything. Root: `infinite-simple-kazhdan-hyperlinear-group`.

## 2. Dictionary D0: both coefficient rings are Steinberg algebras

**2.1 Leavitt.** Clark–Sims, arXiv:1311.3701, Example 3.2, read from the TeX source on MSI: "Every Leavitt
path algebra is a Steinberg algebra. To see this, let $E$ be an arbitrary directed graph, $G_E$ the groupoid
of Example~\ref{ex:graphgroupoid} and $R$ a commutative unital ring. We show that the Leavitt path algebra
$L_R(E)$ is isomorphic to $A_R(G_E)$."
- `L_k(1,2)` is the Leavitt path algebra of the rose with two petals, and `G_(R_2)` is the Cuntz groupoid.
- The number was counted from the source's theorem counter; Clark–Edie-Michell cite it the same way.
- Node: `leavitt-path-algebras-are-steinberg-algebras`.

**2.2 Crossed products.** `A_k(X ⋊ Γ) ≅ LC(X,k) ⋊ Γ` for any commutative unital `k`, via
`f u_γ |-> ((γ,x) |-> f(γx))`. The convolution check is in
`crossed-products-are-transformation-steinberg-algebras-proof`. For `Γ = Z` acting by the shift this is the
Pestov ring.

**2.3 Simplicity.**
- Steinberg arXiv:1408.6014 Cor 3.6, and Clark–Edie-Michell arXiv:1403.4684 Cor 4.6: `A_k(𝒢)` is simple iff
  `𝒢` is effective and minimal (`k` a field).
- Node (un-simplicity): `steinberg-algebra-simple-iff-minimal-effective`.
- Uniform simplicity of the groups (un-simplicity): `steinberg-elementary-groups-are-simple-mod-centre`.
  Every normal subgroup of `EL_n(A_k(𝒢))`, `n >= 3`, is central or everything, when `𝒢` is Hausdorff, ample,
  minimal and effective with compact infinite unit space.
- **Consequence.** Simplicity and property (T) hold uniformly across the ladder, so the approximation type
  is decided by the type of the unit alone.

## 3. Ring rungs and calibration

**Definitions.**
- *Exactly matricial:* a unital embedding into `prod_omega M_(d_k)(F_k)` over fields.
- *LEF ring:* finite windows embed exactly in finite rings (`lef-simple-rings-are-not-finitely-presented`).
- *Unital rank model:* a unital homomorphism into `prod_omega M_(n_i)(k)/d_omega`
  (`rank-modelled-simple-rings-give-linear-sofic-projective-el`).
- *Paradoxical unit:* `(n+1)[R] <= n[R]` in `V(R)` for some `n`.

**Arrows.**
- **Exactly matricial ⇒ LEF ring.** `exactly-matricial-rings-are-lef-rings`: one good coordinate, then a
  finite quotient of the finitely generated entry ring.
- **LEF over a finite field ⇒ rank model.** Regular representations of the finite models; injectivity
  comes from simplicity.
- **Rank model ⇒ stably finite.** `rk(1 − ab) = rk(1 − ba)` coordinatewise; injectivity from simplicity.
- **Stably finite ⟺ unit not paradoxical ⟺ a normalised state on `V(R)`.**
  `simple-ring-stably-finite-iff-unit-not-paradoxical` (un-middle, KMP Tarski import).

**Calibration table.**

| ring | stably finite | rank model | exactly matricial / LEF |
|---|---|---|---|
| `L_(F_2)(1,2)` | no | no (`leavitt-algebra-has-no-unital-rank-model`) | no |
| `LC(X,F_q) ⋊ Z`, X infinite minimal subshift | yes | yes | yes (`minimal-subshift-algebra-is-simple-lef-ring`) |
| `LC(X,k) ⋊ Γ`, minimal topologically free residually finite action | yes | yes | yes (`residually-finite-actions-give-matricial-crossed-products`, un-measure) |
| `LC(Ω,F_q) ⋊ Z^2`, free minimal SFT | yes | yes (`free-minimal-crossed-products-are-simple-with-rank-models`) | iff covariant quantum tilings at every scale (`matricial-z2-sft-crossed-products-give-quantum-tilings`, un-measure) |
| fp infinite simple algebra with rank model (existence open) | yes | yes | no (`exactly-matricial-rings-are-lef-rings` with `lef-simple-rings-are-not-finitely-presented`) |

**The measure dictionary** (un-measure):
- **Necessity:** a matricial model of `A_k(𝒢)` gives a Sylvester rank function and a `𝒢`-invariant
  probability measure (`matricial-steinberg-algebras-have-invariant-measures`).
- **Free-group equivalence:** for `F_r`-actions, invariant measure ⟺ residually finite ⟺ matricial ⟺ rank
  function (`free-group-crossed-product-matricial-iff-invariant-measure`).

**Non-simple warnings.**
- `Z[L^x]` is stably finite and has non-MF `EL_n` (`stably-finite-group-ring-with-non-mf-elementary-groups`).
- Greenfeld's finitely generated stably finite algebra is not linear sofic
  (`stably-finite-algebras-need-not-be-linear-sofic`).

## 4. Established transfers: ring rung ⇒ group rung

- **(L⇐)** `exactly-matricial-rings-have-lef-general-linear-groups` (un-converse; Malcev).
  - Over a finite field with centre `k`, the scalar quotient `S_N` is LEF as well, by Pestov artifact §3.3
    applied coordinatewise.
- **(Σ⇐)** `rank-modelled-simple-rings-give-linear-sofic-projective-el`.
- **(M⇒), from the paradox side:**
  - `stably-infinite-ring-elementary-groups-have-no-mf-quotient` (un-paradox): if `2n[1] <= n[1]`, then
    every MF homomorphism from `EL_N(R)`, `N >= 2n`, is trivial;
  - `paradoxical-ring-el-n-full-mf-radical-from-twice-level` (un-middle);
  - `mf-elementary-groups-force-stably-finite-simple-rings` (un-converse): a nontrivial MF quotient of
    `EL_N(R)` forces `M_m(R)` directly finite for `m <= N/2`.
- **Groupoid form of (M⇒)** (un-paradox, un-middle):
  - `no-invariant-measure-steinberg-elementary-no-mf-quotient`;
  - `measure-free-ample-groupoid-el-n-full-mf-radical`: no invariant probability measure gives full MF
    radical from rank `2n`. So measure-free Boldrini–Prasad actions are paradoxical at group level; they are
    not a middle.
- **Families** (un-paradox): `paradoxical-steinberg-families-kazhdan-no-mf-quotient` (boundary actions,
  self-similar germ algebras).
- **LEF Kazhdan families** (un-measure): Toeplitz crossed products of free groups.
- **The trace face** (un-traces):
  - Amenable and QD traces are blind to paradox versus measure: for `EL_n(R)`, amenability of the canonical
    trace is equivalent to residual finiteness of `R` (`elementary-group-trace-amenable-iff-ring-residually-finite`).
  - Corona traces see the difference (`corona-traces-separate-paradox-from-measure-for-el-n`).
  - So any trace rung of the ladder must be stated with corona traces.

## 5. Candidate theorems (the open part)

**ROOT** `kazhdan-elementary-approximation-type-mirrors-ring-type`: (L), (Σ), (M) of §0 as equivalences.
Route: `kazhdan-approximation-ladder-from-three-converses`.

**FLAGSHIP** `free-group-cantor-elementary-group-lef-iff-invariant-measure` (open; assembled from
established, unreviewed nodes, and the route is added after review).
- **Setting.** `F_r` acts minimally and topologically freely on the Cantor set, and `LC(X,F_q) ⋊ F_r` is
  finitely generated.
- **Claim.** `S_N = EL_N/Z` is infinite, simple and Kazhdan, and it is LEF for all `N` iff an invariant
  probability measure exists. With no invariant measure there is no nontrivial MF quotient from rank `2n`.
- **What it unifies.** Pestov 9.1 and the non-MF obstruction become the two sides of one dynamical dichotomy
  inside one family of groups.
- **Open band.** `3 <= N < 2n`.
- **Firewall.** Beyond free groups, measure ⇒ towers contains char-`p` Kaplansky.

**Open converses.**
- (L⇒) `lef-el-groups-force-exactly-matricial-simple-ring`;
- (Σ⇒) `linear-sofic-el-groups-force-rank-model`;
- (M⇐) `stably-finite-simple-rings-have-mf-elementary-groups` (un-converse). Stronger variant:
  `stably-mf-elementary-groups-force-matricial-rings`.

**The middle** (a new object in any case):
- `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group`: a finitely generated infinite simple
  rank-modelled algebra over a finite field, with some `EL_N(R)` not LEF.
- Conditional route `non-lef-kazhdan-el-group-from-fp-rank-modelled-simple-algebra`.
- Together with (M⇐), it would give MF-but-not-LEF Kazhdan groups of simple rings.
- Other middle sources:
  - quantum-rigid `Z^2` SFTs (measure without towers);
  - the small-rank band `3 <= N < 2p(R)` (`el-n-mf-quotient-below-twice-paradoxical-level-exists`).

**Firewalls** (recorded in the root's Attempts):
- F1: simplicity is essential;
- F2: centre in (Σ);
- F3: "every N" in (M);
- F4: measure-side stable finiteness contains char-`p` Kaplansky
  (`measure-side-stable-finiteness-contains-char-p-kaplansky`);
- F5: characteristic 0 is allowed in (L) and (M), but the Weyl algebra is not finitely generated;
- F6: plain soficity is off the ladder.

## 6. Protocol

- Lanes propose new rungs to `un-architect` with: id, exact statement, which root half it discharges, and
  its firewall.
- Proposed next moves:
  - **(L⇒)** on subshift rings, where the ring rungs collapse (`subshift-ring-lef-iff-word-edges-lie-on-cycles`);
  - **(M⇐)** on crossed products of residually finite actions, where towers exist, avoiding F4;
  - **the middle** via quantum-rigid `Z^2` SFTs, together with `fp-simple-algebra-over-finite-field-with-rank-model`.

## 7. Landed by the UN lanes (as of ~14:35 CDT, 2026-09-13; all unreviewed unless marked)

- **un-prior-art 538afe1ed4:** Rainone–Sims type dichotomy; purely infinite Steinberg algebras; residually
  finite actions have LEF full groups; the Greenfeld import; the continuous-factor embedding of Cantor `Z`
  crossed products.
- **un-paradox 895c311052, 4253950d2e:** stably infinite ⇒ no MF quotient; the measure-free groupoid form;
  paradoxical families; the boundary-action mirror; the Kaplansky firewall.
- **un-simplicity 6c58d38ebb:** Steinberg simplicity import; local annihilation; scalar centre; uniform
  simplicity of `EL_n(A_k(𝒢))/Z`.
- **un-converse 417904a22b:** exactly matricial ⇒ LEF `GL_N`; MF `EL_N` ⇒ stably finite; Weyl algebra
  exactly matricial; the open (M⇐) and matricial questions.
- **un-middle 4db95cef51:** paradoxical level; stably finite ⟺ not paradoxical; the measure-free groupoid;
  the small-rank band.
- **un-traces 102def4e00:** Kazhdan traces; trace amenable ⟺ ring residually finite; corona traces.
- **un-measure 3f486a4805:** matricial crossed products of residually finite actions; invariant-measure
  necessity; the `F_r` equivalence; `Z^2` SFT quantum tilings.
- **un-calibration 8d27ba78e6:** Weyl over `Q` is a LEF ring but not matricial over `Q`; group rings (rank
  model and Kazhdan, but not LEF); odometer (LEF, no (T)); the 16-ring table in
  `un-calibration-table-2026-09-13-part{1,2}.md`.
- **un-k1-homology 5c83d35b84:** the unit-group face.
  - Under (PI) local compressibility, the maximal MF quotient of `GL_n(A_k(𝒢))` is `K_1`.
  - For exactly matricial algebras the MF radical is trivial.
  - For irreducible SFT Leavitt algebras there is an explicit formula, read through Matui's groupoid homology.
  - The general low-degree homology statement is open.
- **un-architect (this landing):**
  - root and route;
  - D0 nodes (Leavitt citation, crossed-product proof);
  - `exactly-matricial-rings-are-lef-rings`;
  - the open converses (L⇒), (Σ⇒);
  - the middle claim and its route;
  - the flagship;
  - canonical reconciliation of the duplicate pairs. The canonical nodes are
    `stably-infinite-ring-elementary-groups-have-no-mf-quotient` and
    `no-invariant-measure-steinberg-elementary-no-mf-quotient`; the un-middle counterparts carry
    `distinct_from` notes.
