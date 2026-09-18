# Katsura–Exel–Pardo hosts for BS(1,2): sources and checks (lane gq-affq, 2026-09-18)

Target (coordinator; critic's U3 in `research/artifacts/gq-gq-critic-pass-3.md` §4): does a finitely presented
Katsura–Exel–Pardo (KEP) groupoid group contain `BS(1,2)`, or give a height-2 renormalization? Answer landed as
`odometer-2v-is-fp-simple-and-contains-bs12` (both referees PASS: bbada3b68, 72a3c51ff). This note records the
source statements (TeX e-prints fetched on MSI, copies in `$GQ/src/kep/`), the checks against the landed obstruction
nodes, the priority check, and the two follow-up items (Q ⋊ ⟨2⟩, and bs12 proper).

**Framing.** Boone–Higman for `BS(1,2)`, and for every Baumslag–Solitar group, is known (BBMZ arXiv:2306.16356v3,
footnote 8; `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`). No novelty is claimed there. What is new is
the host: Brin's `2V` extended by one odometer, a KEP / higher-rank-graph full group directly over `2V`. It matters
for `bs12-embeds-in-brin-thompson-2v` and for `aff-q-embeds-in-fp-simple-group`.

## 1. Sources, verbatim

**Exel–Pardo, arXiv:1409.1107** (`exel-pardo-1409.1107.tex`). Katsura triples, l.577–590: for `m ∈ Z` and an
edge `e_{i,j,n}`, take the "Euclidean division of `mB_{i,j}+n` by `A_{i,j}`, say `mB_{i,j}+n=\hat k A_{i,j} + \hat n`
with `0 ≤ \hat n < A_{i,j}`. We then put `σ_m(e_{i,j,n}) := e_{i,j,\hat n}`", with cocycle
"`φ(m, e_{i,j,n}):= \hat k`". For `A = (2)`, `B = (1)`, `m = 1` this is the binary odometer:
`a·e_0 = e_1` with restriction `1`, and `a·e_1 = e_0` with restriction `a`. The pseudo-freeness, Hausdorff and
minimality theorems of Exel–Pardo are already quoted in `research/artifacts/un-boundary-families-2026-09-13-part2.md`
§1.1 ("family O" is this odometer groupoid).

**X. Li, arXiv:2110.04505v2**, *Left regular representations of Garside categories II. Finiteness properties of
topological full groups* (`li-garside-II-2110.04505v2.tex`).
- Condition (F), l.1454: "We say that condition (F) holds if for all `v ∈ C^0`, `a, b ∈ C^*(v,v)` and
  `U = X(v;e) ∈ 𝔛`, `[a,U] = [b,U]` in `C` implies `a=b`." l.1456: "Note that (F) holds if, for instance, `C` is
  right cancellative."
- Theorem thm:k-graphs, l.2124–2125 (`P = Z_{≥0}^k`, `C` finite, same assumptions as Theorem thm:deg): "Suppose
  that for all `v ∈ C^0` and `1 ≤ j ≤ k`, we have `# v d^{-1}(ε_j) v ≥ 2`. Let `X ⊆ Ω_∞` be a closed invariant
  subspace … Then `F((I_l ⋉ X)_Y^Y)` is of type `F_∞`."
- Remark rem:ZS-Stab, l.2362ff: "If we even have `C^* = C^0`, then `D^*(\tilde v, \tilde v) = St(G,v)`."
- Example ex:ZS, l.2371–2380, case (III): "If `P = Z_{≥0}^k` … for all `v ∈ C^0` and `1 ≤ j ≤ k`, we have
  `# v d^{-1}(ε_j) v ≥ 2`, and if `X ⊆ Ω_∞` is a closed invariant subspace, then for all natural numbers `n`,
  `Q_D(\tilde *, \tilde *)` is of type `F_n` if `D^*(w,w)` is of type `F_n` for all `w ∈ D^0`." The standing
  requirements of the example are: `C` cancellative with a degree map; `d(g.a) = d(a)`; `P` right cancellative;
  "`C` satisfies the same assumptions as for Theorem thm:deg, and condition (F) holds". Li adds (l.2380): "(III)
  also covers … self-similar actions on higher rank graphs as in [LY, ABRW]", and for Katsura algebras
  (`G = Z` on a graph) "condition (F) is not needed in this case".

**H. Matui, arXiv:1210.5800v3**, *Topological full groups of one-sided shifts of finite type*
(`matui-1210.5800.tex`).
- Standing assumption of the subsection (l.1183): "`G` an essentially principal étale groupoid whose unit space is
  a Cantor set".
- Definition pi, l.1194: "A clopen set `A ⊂ G^{(0)}` is said to be properly infinite if there exist compact open
  `G`-sets `U,V ⊂ G` such that `s(U)=s(V)=A`, `r(U)∪r(V) ⊂ A` and `r(U)∩r(V)=∅`. We say that `G` is purely
  infinite if every clopen set `A ⊂ G^{(0)}` is properly infinite."
- Theorem simple2, l.1466: "Suppose that `G` is purely infinite and minimal. Then any non-trivial subgroup of
  `[[G]]` normalized by the commutator subgroup `D([[G]])` contains `D([[G]])`. In particular, `D([[G]])` is simple."

## 2. The host

`Λ` is the one-vertex 2-graph with two edges of each colour, so its category is `F_2^+ × F_2^+` and
`Ω_∞ = C × C`. `Z = ⟨a⟩` acts by the Katsura odometer on colour-1 edges, and on colour-2 edges by fixing each edge
with restriction `a`. On `Ω_∞` this is `τ × id`. `D = Λ ⋈ Z`, and `2V_τ := F(I_l(D) ⋉ Ω_∞)`. Checks of Li (III):
- two edges of each colour at the vertex: yes;
- degree-preserving action: yes;
- (F): `D` is right cancellative because the action is pseudo-free (proof route, step A), so l.1456 applies;
- `D^*(w,w) = St(Z, v) = Z` (rem:ZS-Stab, `Λ^* = Λ^0`), which is of type `F_∞`;
- `X = Ω_∞`: yes.

## 3. Tests against the landed obstructions

- **Easy obstruction** (a minimal odometer is never conjugate to its non-minimal square).
  - In the 1D Katsura groupoid, the relation `φ(a^2, e_0) = a`, i.e. `β τ^2 β^{-1} = τ` for the prefix-deletion
    bisection `β: C(0) → C`, is only a partial conjugacy. No element of `F(G_τ)` conjugates `τ` to `τ^2`.
  - In `2V_τ` the conjugated element is `s = τ × id`. It is not minimal: its minimal sets are the fibres
    `C × {y}`, a Cantor set of them. The minimal sets of `s^2` are the half-fibres `C(j) × {y}`, and the baker map
    is a bijection between the two families.
  - So the BS-behaviour lives in a non-global bisection of the Katsura groupoid, and the free colour turns it
    into a global conjugacy.
- **Return times** (`renormalization-return-times-tend-to-zero-adically`, item 3): `τ^n x → x` iff `n → 0` in
  `Z_2`, so `τ` passes, as any genuine odometer must.
- **Odd branching** (`crossing-move-hierarchies-have-odd-branching`): does not apply. `τ`'s carries are done in
  one step by the group element, not by a head walking with bounded junctions. This confirms the critic's
  item (c): that node bounds one-head bounded-junction machines only.
- **`germ-extensions-omit-standard-gl-n-q`**: not relevant here. `2V_τ` is not asked to contain `GL_n(Q)`.

## 4. What is not claimed

- `BS(1,2) ≤ nV` (`bs12-embeds-in-brin-thompson-2v`) is not settled. If `2V_τ` embeds in some `nV`, it would be.
- Whether `BS(1,2)` embeds in the 1D group `F(G_τ) = V_2(⟨τ⟩)` (of type `F_∞` by Li's Katsura remark) is not
  decided. The natural element, "`τ` on each of infinitely many cones", has infinitely many pieces.
- No copy of `Q ⋊ ⟨2⟩` is claimed. The root tower `Q_τ` of `s` meets `u^{-1}⟨s⟩u` in `⟨s_1⟩`, where
  `s_1 = u^{-1}su`, but `u` is not shown to normalize `Q_τ`. Heuristic: making the odd-radix roots compatible with
  `u` requires doubling a mixed-radix fraction, which is not a bounded prefix operation.

## 5. Priority check (bounded)

- The three TeX sources (Exel–Pardo 1409.1107, Li 2110.04505v2, Matui 1210.5800v3) contain no occurrence of
  "Baumslag", "Solitar", "BS(1", "odometer", "adding machine" or "2-adic" (grep, 2026-09-18).
- Web search found Valente–Yang, arXiv:2405.07062 (v2, 2025-04-24). Abstract, verbatim: "we initiate the study of
  higher rank Baumslag-Solitar semigroups and their related C*-algebras. We focus on two extreme, but interesting,
  classes - one is related to products of odometers …". It concerns semigroups, C*-algebras and von Neumann
  algebras, and states no group embedding.
- That the odometer's Zappa–Szép monoid is the Baumslag–Solitar monoid is classical.
- Not searched: MathSciNet, and the body of Li–Yang *Self-similar k-graph C*-algebras*. No priority is claimed.

## 6. Item 1: `Q ⋊ ⟨2⟩` (node `affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q`)

- *Model.* Read `X = C × C` as `{0,1}^Z`. Then `Q_2` acts by addition with upward carries, and `u` is `×2`. So
  `Q ⋊ ⟨2⟩` acts naturally. In `2V_τ` this action gives exactly `Z[1/2] ⋊ ⟨2⟩ = BS(1,2)`: odd roots of `s` would be
  `+1/q` on colour 1, and those are not pieces of the odometer groupoid.
- *Reach.* Replace `⟨τ⟩` by the affine self-similar group `G_N = Z[1/N] ⋊ ⟨p | N⟩` on `Z_2`. Then
  `Z[1/2N] ⋊ ⟨2⟩ ≤ 2V_{G_N}`. That group is not finitely generated, and `2V_{G_N}` is simple and is `F_n`
  whenever `G_N` is. For `N = 3`, `G_3 = BS(1,3)` is `F_∞`, so `2V_{BS(1,3)}` is an `F_∞` simple group containing
  `Z[1/6] ⋊ ⟨2⟩`, `BS(1,2)`, `BS(1,3)` and `2V ⊇ Q`.
- *Limit.* For finitely generated `H ≤ Aff(Q)` acting on `Z_2`, the colour-1 pieces of `2V_H` lie in `Aff(Z[1/N'])`,
  so `x ↦ x + 1/q` is missing for `q ∤ 2N'`. The natural `Q ⋊ ⟨2⟩` is in no such host. This is the mechanism of
  `finite-state-mobius-pieces-see-finitely-many-primes`.
- *Prime-mixing checks.*
  - Torus amalgams (item 20): escaped. This is not an amalgam; the finite-prime-set phenomenon reappears as the
    limit instead.
  - Adelic finite support: escaped, since the host is not coordinatewise.
  - p-adic power maps (item 8): not triggered, since only one dilation is used.
- *Open.* Wild copies, for example on the mixed-radix root tower `Q_τ`. Heuristic against it: the doubling would
  have to multiply a most-significant-first mixed-radix fraction by `2`, which carries from the far end. Also open:
  non-affine finitely generated coefficient groups containing `Z_(2)`.

## 7. Item 2: `bs12` proper (one attempt; recorded as an Attempt on `bs12-embeds-in-brin-thompson-2v`)

- *Lemma (lane argument).*
  - A brick-local homeomorphism of `C^k` onto itself is an element of `kV`: a finite union of brick prefix
    replacements whose images partition. So brick-local conjugation preserves `kV`.
  - `τ × id^{k-1} ∉ kV`: on every brick `C(1^L) × …` it acts as `1^L w ↦ 0^L τ(w)`, which is never canonical, because
    `τ(w) ≠ w`.
  - Hence, by `brin-thompson-first-return-maps-lie-in-kv`, **no first-return map with bounded return times of any
    `W ∈ kV` is brick-locally conjugate to `τ × id^{k-1}`**.
  - With unbounded return times the first-return map is not in `kV` at all.
- *Consequence.* The free-colour and first-return route cannot import the odometer itself into `nV`. A witness for
  `BS(1,2) ≤ nV` must use a non-equicontinuous base whose odometer is only a factor, as SMART's induced map `U` has
  the `Z_3` factor for `BS(1,3)`. That is lane gq-nv-obstruct's binary-hierarchy problem.
- Whether `2V_τ` embeds abstractly in some `nV` is open. It would imply `bs12`, since `BS(1,2) ≤ 2V_τ`, and no
  spatial route to it is known.
