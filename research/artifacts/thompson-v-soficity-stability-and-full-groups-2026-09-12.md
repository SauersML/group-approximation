# Thompson V: soficity as permutation stability, and where full-group soficity theorems stop

Lane `thompson-v-soficity`, 2026-09-12. This note does not decide whether `V = G_(2,1)` is
sofic. It records the verified literature status, proves that nonsoficity of `V` is the same
property as each of Bradford's four permutation-stability properties, and shows that the one
published soficity theorem for full groups of groupoids that is not a LEF theorem cannot reach
`V`.

## 1. Status, from the sources

- **Bradford**, *Local permutation stability*, arXiv:2211.15249v2 (4 Sep 2024). Pages 1–12 and
  24–30 were read from the PDF. Page 4:
  > the topological full groups of Z-actions studied in Theorem 1.8 have close relatives which
  > are not known to be sofic. For instance Thompson's group V is the topological full group of
  > the action of a finitely generated group (namely of V itself). We should note that, since V
  > is finitely presented, it is locally stable iff it is stable (see Lemma 2.14 below).
  > Nevertheless, given the structural similarities between V and the groups Γ′ arising in
  > Theorem 1.8, our results can be seen as evidence that V is stable. If this were the case,
  > then V would be non-sofic.

  Page 1: "the only groups known to be stable have also long been known to be sofic".
- **Salo**, arXiv:2103.15505 (abstract): settling soficity of mapping class groups of mixing SFTs
  "in either direction would solve an open problem in geometric group theory", because `V` embeds
  there. This is already recorded in `hyperlinear-fp-infinite-simple-group`.
- **arXiv API searches**, 2026-09-12: `abs:sofic AND abs:Thompson`; `abs:sofic AND (groupoid OR
  "full group")`; `(hyperlinear OR "permutation stable") AND abs:Thompson`. None of the hits
  claims that `V` is sofic or that it is not. This is a search, not a complete literature
  verification.

## 2. Theorem 1: nonsoficity of V is permutation stability

**Definitions** (Bradford, Definitions 1.1–1.3 and Remark 1.4). Let `phi_n : Gamma -> Sym(k_n)`
be maps, and let `d` be the normalized Hamming distance.
- `(phi_n)` is an *almost-homomorphism* if `d(phi_n(g)phi_n(h), phi_n(gh)) -> 0` for all `g, h`.
- It is *separating* if `d(phi_n(g), id) -> 1` for every `g != e`.
- `Gamma` is *stable* if every almost-homomorphism is pointwise close to a sequence of
  homomorphisms `psi_n`.
- It is *weakly stable* if the same holds for separating almost-homomorphisms.
- It is *locally stable*, or *weakly locally stable*, if `psi_n` may be taken to be partial
  homomorphisms: for each `g, h` there is `N` with `psi_n(gh) = psi_n(g)psi_n(h)` for `n >= N`.

**Theorem 1.** For Thompson's group `V` the following are equivalent:
(1) `V` is not sofic; (2) stable; (3) weakly stable; (4) locally stable; (5) weakly locally stable.

**Proof.** Bradford's Remark 1.5 gives `(2) => (3)`, `(2) => (4)`, `(3) => (5)` and `(4) => (5)`.

**`(5) => (1)`.** A sofic, weakly locally stable group is LEF (Bradford, Lemma 2.15, immediate
from the definitions). `V` is not LEF (`thompson-v-not-lef`).

**`(1) => (2)`.** Let `(phi_n)` be an almost-homomorphism of `V`, and fix a nonprincipal
ultrafilter `omega`. Put `chi(g) = lim_omega |Fix(phi_n(g))| / k_n`. Write `sigma_i = phi_n(g_i)`.

(a) **`chi(e) = 1`.** From `phi_n(e)^2 ~ phi_n(e)` we get `phi_n(e) ~ id`.

(b) **`chi` is a class function.** Bi-invariance of `d` and the almost-homomorphism property give
`phi_n(h g h^-1) ~ phi_n(h) phi_n(g) phi_n(h)^-1`, which has as many fixed points as `phi_n(g)`.

(c) **`chi` is positive definite.** For `g_1, ..., g_r` and `c` in `C^r`, the counting identity
```text
sum_(i,j) c_i conj(c_j) |Fix(sigma_j^-1 sigma_i)| = sum_(x,y) | sum_i c_i [sigma_i x = y] |^2 >= 0
```
holds for permutations. `|Fix(phi_n(g_j^-1 g_i))|` and `|Fix(sigma_j^-1 sigma_i)|` differ by at
most `k_n d(phi_n(g_j^-1 g_i), sigma_j^-1 sigma_i)`, which is `o(k_n)`. So the matrix
`[chi(g_j^-1 g_i)]` is a limit of positive semidefinite matrices.

**Rigidity and amplification.** `chi` is a character, so by `thompson-v-character-simplex`
(Dudko--Medynets, Corollary 3.6(2)) it equals `t tau_reg + (1-t) tau_triv` for one
`t = t_omega` in `[0,1]`. Suppose some `t_omega > 0`. For `m >= 1`, let `phi_n^(m)(g)` act
coordinatewise on `[k_n]^m`.
- The defect grows at most by a factor `m`, by a union bound over coordinates.
- Fixed-point fractions are raised to the power `m`, so every `g != e` moves a proportion
  `1 - (1 - t_omega)^m` along `omega`.

Choosing `m` large and diagonalizing over finite subsets of `V` gives a separating
almost-homomorphism, so `V` is sofic.

**Conclusion.** Under (1), `t_omega = 0` for every `omega`. Then `lim_omega d(phi_n(g), id) = 0`
for all `omega`, so `d(phi_n(g), id) -> 0`, and the trivial homomorphisms `psi_n` witness
stability. QED.

**Remarks.**
- `(2) => (1)` also follows from the general principle `sofic-stable-implies-residually-finite`
  (Glebsky--Rivera), since `V` is not residually finite. Only `(1) => (2)` uses character rigidity.
- The same proof applies to any finitely generated group that is not LEF and whose extreme
  characters are only `tau_reg` and `tau_triv`.

**What this says.**
- **Bradford's heuristic.** His "evidence that V is stable" is, by Theorem 1, evidence for
  nonsoficity itself, not for a separate property that happens to imply it.
- **Negative direction.** A proof that `V` is not sofic must show that every almost-homomorphism
  of a finitely presented group with no finite quotients is close to the trivial one. The stable
  groups Bradford lists (Section 2.4: finite, free, polycyclic-by-finite, `BS(1,n)`, Grigorchuk
  and Gupta--Sidki groups, some wreath products) are all sofic. His IRS criterion (Theorem 1.7) is
  for amenable groups, and `V` is not amenable.
- **Positive direction.** One almost-homomorphism in which one element `g != e` keeps moving a
  non-vanishing proportion of points already makes `V` sofic. This is the one-word form of
  `thompson-v-not-sofic`.

## 3. Theorem 2: the Cuntz groupoid has no Følner sequence

**Setting.** Let `X = {0,1}^N`, and let `G_2 = {(x, m-n, y) : sigma^m x = sigma^n y}` be the
Deaconu--Renault groupoid of the one-sided 2-shift, the Cuntz groupoid.
- It is étale, ample, Hausdorff and second countable, with compact unit space `X`.
- It is minimal, because tail classes are dense.
- A prefix replacement `g = (alpha_i -> beta_i)` in `V` gives the compact open bisection
  `B_g = {(g x, |beta_i| - |alpha_i|, x) : x in alpha_i X}`, whose source and range are both `X`.
  Its natural homeomorphism is `g`. So `V <= [[G_2]]`, which is the only inclusion used below.

**Ma's hypotheses** (arXiv:2110.11548v1; pages 1–14 and 27–31 were read from the PDF).
- **Standing assumption** (p. 9): σ-compact, locally compact, Hausdorff, étale, ample, compact
  unit space.
- **Definition 3.8.** The left outer `K`-boundary of `A` is `(KA) \ A`. The left `K`-boundary
  `d_K A` is its union with the inner boundary.
- **Definition 3.9.** A finite nonempty `F` is `(K, epsilon)`-Følner if `|d_K F| / |F| <= epsilon`.
- **Definition 3.10(1).** `G` is fiberwise amenable if for every compact `K` and `epsilon > 0`
  there is a `(K, epsilon)`-Følner set.
- **Definition 4.12.** A sequence of normal Følner sets `S_n` is a Følner sequence if
  `|K S_n u \ S_n u| / |S_n u| -> 0` for every compact `K` and every unit `u`.
- **Theorem 7.5.** "Let G be a second countable minimal groupoid that admits a Følner sequence.
  Then [[G]] is sofic."
- **Corollary D(1).** Fiberwise amenable, minimal, and some unit with trivial isotropy imply that
  `[[G]]` is sofic.
- **Proof of Theorem 7.5.** The approximations are permutations of the finite range sets
  `P_n = r(T_n u_n)`, obtained by restricting the action of `[[G]]` to them.

**Lemma 3.1** (`thompson-v-cantor-orbits-have-no-folner-sets`). Let `S` be a finite generating set
of `V`. There is `c_S > 0` with `max_(s in S) |sF symmetric-difference F| >= c_S |F|` for every
finite nonempty point set `F` in `X`.

**Lemma 3.2** (multiplicities). Let `m : X -> N` have finite support and put
`(s.m)(x) = m(s^-1 x)`. Then `max_s ||s.m - m||_1 >= (c_S / |S|) ||m||_1`.

*Proof.* Put `F_j = {m >= j}`. These sets are nested, and `{s.m >= j} = s F_j`. Pointwise,
`|s.m - m| = sum_j |1_(sF_j) - 1_(F_j)|`, so `||s.m - m||_1 = sum_j |s F_j sym-diff F_j|`. Hence
`sum_s ||s.m - m||_1 >= sum_j max_s |s F_j sym-diff F_j| >= c_S sum_j |F_j| = c_S ||m||_1`, and
the maximum over `s` is at least the average. QED.

**Theorem 2.** Let `K` be compact with `B_s <= K` for all `s in S`. Then
`|KF \ F| >= (c_S / 2|S|) |F|` for every finite `F <= G_2`. So `G_2` is not fiberwise amenable
and admits no Følner sequence. Theorem 7.5 and Corollary D(1) of Ma therefore do not apply to
`G_2`, and cannot certify that `V` is sofic.

*Proof.* Put `F_u = F ∩ G_u` for units `u`.
1. **Fibres split the boundary.** `K F_u <= G_u`, so `|KF \ F| = sum_u |K F_u \ F_u|`.
2. **Left multiplication.** `B_s` has source `X`, so `gamma -> B_s gamma` is injective on `G_u`,
   with `r(B_s gamma) = s(r(gamma))`. So `|B_s F_u| = |F_u|`.
3. **Pushforward.** Let `m_u = r_*(counting measure on F_u)`. This handles nontrivial isotropy,
   where `r` is not injective on `G_u`. Then `r_*(counting on B_s F_u) = s.m_u`, and
   `||s.m_u - m_u||_1 <= |B_s F_u sym-diff F_u| = 2|B_s F_u \ F_u| <= 2|K F_u \ F_u|`.
4. **Conclusion.** Lemma 3.2 gives `|K F_u \ F_u| >= (c_S / 2|S|) |F_u|`. Summing over `u`
   proves the bound. Normal Følner sets contain `G^(0)`, so `S_n u` is nonempty, and the ratio in
   Definition 4.12 stays at least `c_S / 2|S|`. QED.

**Corollary 3.3** (almost-equivariant coordinate maps). Let `Omega` be finite, `sigma_s` in
`Sym(Omega)` for `s in S`, and `phi : Omega -> X` any map. Put
`delta_s = |{w : phi(sigma_s w) != s phi(w)}| / |Omega|`. Then `max_s delta_s >= c_S / 2|S|`,
whatever relations the `sigma_s` satisfy.

*Proof.* Let `m = phi_*(counting)`. Since `sigma_s` is a bijection, `(phi o sigma_s)_* counting`
equals `m`. The map `s o phi` pushes counting to `s.m`, and the two maps differ on
`delta_s |Omega|` points, so `||s.m - m||_1 <= 2 delta_s |Omega|`. Lemma 3.2 finishes. QED.

So a model of `V` that tracks a Cantor address for each point, with any multiplicity or any
finite internal state, keeps a fixed proportion of boundary. This extends the injective
truncation of Lemma 3.1 and the tracial cylinder count recorded in `thompson-v-hyperlinear`.

**Other published full-group theorems.**
- **Elek**, arXiv:1211.0621: the full group of a sofic p.m.p. equivalence relation is sofic.
  `V` preserves no probability measure on `X` (halving), so the Cantor system supplies no such
  relation. Any other p.m.p. action would have to be produced first.
- **Grigorchuk--Medynets** (short proof in Elek, arXiv:1211.0621), and **Ma**, arXiv:2209.00580v4
  (abstract: minimal topologically free residually finite actions). These give LEF full groups.
  A LEF group has only LEF subgroups, and `V` is not LEF, so `V` lies in none of them.

## 4. What is left

- **Soficity.** It needs models with no almost-equivariant coordinate map to `X` (Corollary 3.3):
  genuinely non-spatial approximations of a finitely presented simple group that is not LEF. No
  construction is known.
- **Nonsoficity.** It is permutation stability of `V` (Theorem 1). `V` has the Haagerup property,
  so no Kazhdan-based argument applies, and there is no IRS or amenability criterion. No stability
  technique for a nonamenable group without finite quotients is recorded.
