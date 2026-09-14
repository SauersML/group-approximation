# sk-cstar-simple-2: which C*-simplicity criteria can decide G_X (part 1, 2026-09-13)

Lane sk-cstar-simple-2 (roster H, wave 10). Target: the open claim `subshift-elementary-groups-are-cstar-simple`.
sk-cstar-simple owns the confined-subgroup route (test subgroups, idempotent displacement). This lane tests the other
sufficient criteria from the literature and records which of them can work.

## 0. Summary
1. **Per-element Powers averaging is exactly unique trace** (Haagerup, Theorem B); simplicity needs simultaneous averaging
   (Theorem C(v)). Unique trace is already known for `G_X`, so single-element averaging arguments add nothing.
2. **Theorem 1 (new, proved in §3).** For every infinite minimal subshift `X`, finite field `F_q` and `n ≥ 2`, the cut
   stabilizer `S_y ≤ EL_n(LC(X,F_q) ⋊ Z)` is an infinite, locally finite, normalish subgroup.
3. **Corollaries (§4).**
   - The Breuillard–Kalantar–Kennedy–Ozawa criterion "no amenable normalish subgroup" cannot prove C*-simplicity of `G_X`.
     Nor can property (CS), which `G_X` fails.
   - All ℓ²-Betti numbers of `G_X` vanish, and `H_b^k(G_X, E) = 0` for every mixing coefficient module `E` and every `k`
     (BKKO, via Bader–Furman–Sauer).
4. **Contrast.** sk-cstar-simple proved that `S_y` is not confined. So `S_y` is large for finite intersections of conjugates
   and small in the Chabauty topology. C*-simplicity of `G_X` has to be decided through Kennedy's criterion, not through
   BKKO's.
5. **Part 2 (planned).** A Powers partition for finite sets, built from row-sheared orbit dynamics, or a topologically free
   boundary action.

## 1. Sources read at source
All from arXiv e-print TeX, fetched and extracted on MSI under `/scratch.global/sauer354/sk/sk-cstar-simple-2/`. Journal
numbering was not opened.

### U. Haagerup, *A new look at C*-simplicity and the unique trace property of a group*, arXiv:1509.05880 (`main.tex`)
Theorem `thm:B` (l.435–444), verbatim up to macros:
> Let $G$ be a group. The following are equivalent:
> (i) $C^*_\lambda(G)$ has a unique tracial state,
> (ii) $G$ admits a faithful boundary action,
> (iii) $\ra(G) = \{e\}$,
> (iv) for all $t \in G \setminus \{e\}$ and all $\ep>0$, there exist $s_1, s_2, \dots, s_n \in G$ such that
> $\| \frac{1}{n} \sum_{k=1}^n \lambda(s_kts_k^{-1}) \| < \ep.$

Theorem `thm:C` (l.450–462), item (v), verbatim up to macros:
> (i) $C^*_\lambda(G)$ is simple, [...]
> (v) for all $t_1, t_2, \dots, t_m \in G \setminus \{e\}$ and all $\ep>0$, there exist $s_1, s_2, \dots, s_n \in G$ such that
> $\| \frac{1}{n} \sum_{k=1}^n \lambda(s_kt_js_k^{-1}) \| < \ep,$ for $j=1,2, \dots, m$,

### E. Breuillard, M. Kalantar, M. Kennedy, N. Ozawa, *C*-simplicity and the unique trace property for discrete groups*, arXiv:1410.2518 (`main.tex`)
Definition (l.604–605):
> Let $G$ be a group. A subgroup $H \le G$ is said to be {\em normalish} if for every $n \geq 1$ and $t_1,\ldots,t_n \in G$
> the intersection $\cap_i t_i H t_i^{-1}$ is infinite.

Theorem `thm:not-c-star-simple-implies-normalish` (l.610):
> A discrete group $G$ with no non-trivial finite normal subgroups and no amenable normalish subgroups is C*-simple.

Proposition `betti` (l.626–628), introduced as "the following special case of \cite{BFS2013}*{Theorem 1.3}":
> Let $G$ be a discrete group. If $G$ contains an amenable normalish subgroup, then $\beta_n^{(2)} = 0$ for every $n \geq 0$.

Mixing modules (l.644–645):
> The dual Banach $G$-module $E$ is said to be {\em mixing} if the stabilizer subgroup $G_x = \{ s \in G \mid sx = x \}$ is
> finite for every $x \in E \setminus \{0\}$. Examples of such $G$-modules include $\ell^p(G)$ for $1\le p < \infty$.

Proposition `thm:trivial-bdd-cohomology` (l.647–649):
> Let $G$ be a discrete group, and let $(\pi,E)$ be a coefficient $G$-module with $E$ mixing. If $G$ contains an amenable
> normalish subgroup, then $H_b^n(G,E)$ is trivial for every $n \geq 0$ and every mixing dual Banach $G$-module.

Property (CS), definition (l.939), and the proposition after it (l.942–946):
> We say a discrete group $G$ has property (CS) if the following statement holds: For every weakly regular unitary
> representation $\pi\colon G\to\IB(\cH)$, there exists an SOT-neighborhood $U$ of the identity in $\IB(\cH)$ such that
> $\pi^{-1}(U) \subset R_a(G)$.

> Every discrete group $G$ with property (CS) and trivial amenable radical is C*-simple. [Proof:] We will prove that (CS)
> implies the absence of amenable normalish subgroups. [...]

The converse remark (l.948): `BS(m,n)` is C*-simple, while `⟨a⟩` is amenable, normalish and commensurated.

Journal data (recalled, not checked): Publ. Math. IHÉS 126 (2017), 35–71, doi 10.1007/s10240-017-0091-2, the DOI as shown in
a search listing. Haagerup's paper appeared in the Abel Symposium 2015 volume (Springer, 2016).

## 2. Setting
- `X ⊆ A^Z` is an infinite minimal subshift with shift `T`, `F_q` a finite field, `R = LC(X,F_q) ⋊_T Z`, `n ≥ 2`,
  and `G = EL_n(R)`.
- Fix `y ∈ X`. The orbit module is `M = F_q^{(Z)} ⊗ F_q^n` with basis `δ_t ⊗ e_i`, and `π(fu^k)δ_t = f(T^{t+k}y)δ_{t+k}`.
  So `π(g)` for `g ∈ M_n(R)` acts entrywise.
- `π` is faithful on `M_n(R)`: the coefficients of `g − I` are locally constant and vanish on the dense orbit of `y`.
- `V^J = span{δ_t : t ∈ J} ⊗ F_q^n` for `J ⊆ Z`, with `V^{≥m} = V^{[m,∞)}` and `V^{<m} = V^{(−∞,m)}`.
- `S_y = {g ∈ G : π(g)V^{<0} = V^{<0}, π(g)V^{≥0} = V^{≥0}}`. This is the subgroup of
  `cut-stabilizer-subgroups-of-el3-are-not-confined`, there for `n = 3` and `q = 2`.
- The width of `g ∈ M_n(R)` is `w(g) = max{|k| : some entry of g has a nonzero u^k-coefficient}`. Then
  `π(g)V^{≥m} ⊆ V^{≥m−w(g)}` and `π(g)V^{<m} ⊆ V^{<m+w(g)}`.

## 3. Theorem 1 and proof
**Theorem 1.** `S_y` is infinite and locally finite, and it is normalish in `G`.

### Step 1: the cut ring is a directed union of finite matrix rings
Let `R_y = {r ∈ R : π(r)V^{<0} ⊆ V^{<0}, π(r)V^{≥0} ⊆ V^{≥0}}` (for `n = 1`). It is a unital subring, and
`S_y ⊆ GL_n(R_y)`: an element preserves both halves iff every entry does, and `g^{-1} ∈ S_y` as well.

For `r = Σ_{|k|≤w} f_k u^k` the entry `π(f_ku^k)` sends `δ_t` to `f_k(T^{t+k}y)δ_{t+k}`. It crosses the cut iff `t` and
`t+k` lie on different sides of `0`. So `r ∈ R_y` iff
- for `k > 0`, `f_k(T^jy) = 0` for `j = 0,…,k−1`;
- for `k < 0`, `f_k(T^jy) = 0` for `j = k,…,−1`.

Each `f_k` is locally constant, so there is a clopen `B ∋ y` with `f_k = 0` on `T^jB` for the same ranges of `j`.

Now take finitely many `r_1,…,r_m ∈ R_y`.
- Choose `B` as above for all their coefficients at once.
- Build the Kakutani–Rokhlin partition over `B`: `X` is minimal, so the return time to `B` is bounded. Refine the base into
  clopen pieces `W` so that every coefficient `f_k` is constant on every level `T^aW`, `0 ≤ a < h(W)`.
- Let `A` be the span of the matrix units `e_{T^aW}u^{a−b}` (`0 ≤ a,b < h(W)`). Then `A ≅ ⊕_W M_{h(W)}(F_q)` is a finite ring.

**Claim: every `r_i ∈ A`.** Write `f_ku^k = Σ e_{T^aW}u^k` over the levels where `f_k = 1` (over `F_q`, use the constant values).
- `e_{T^aW}u^k = u^ke_{T^{a−k}W}` is the matrix unit `e_{T^aW}u^{a−(a−k)}` as long as `0 ≤ a−k < h(W)`.
- For `k > 0` and `a < k`: the points `z` of the level satisfy `T^{−a}z ∈ B` with `0 ≤ a ≤ k−1`, so `z ∈ T^aB`. There `f_k = 0`.
- For `k < 0` and `a − k ≥ h(W)`: the forward orbit of `z` enters `B` at a time `j ∈ [1,|k|]`, so `z ∈ T^{−j}B`, with `−j` in
  `[k,−1]`. There `f_k = 0`.

So no level where `f_k ≠ 0` crosses, and `r_i ∈ A`. Hence `R_y` is a directed union of finite rings.
- Finitely many elements of `S_y`, together with their inverses, have all entries in one finite `A`, so they generate a
  subgroup of the finite group `GL_n(A)`. So `S_y` is locally finite.
- Conversely, `GL_n(A) ∩ G ≤ S_y` whenever `y ∈ B` (sk-cstar-simple).

### Step 2: normalish
Let `t_1,…,t_m ∈ G` and `W_0 = max_i max(w(t_i), w(t_i^{-1}))`. Put `J = [−W_0, W_0)`.

**Window lemma.** For every `i`:
- `π(t_i)V^{≥0} = W_i ⊕ V^{≥W_0}` and `π(t_i)V^{<0} = W'_i ⊕ V^{<−W_0}`, with `W_i, W'_i ⊆ V^J`.

*Proof.*
- `π(t_i)V^{≥0} ⊆ V^{≥−W_0} = V^J ⊕ V^{≥W_0}`.
- `V^{≥W_0} = π(t_i)π(t_i^{-1})V^{≥W_0} ⊆ π(t_i)V^{≥0}`.
- So any `v ∈ π(t_i)V^{≥0}` splits as `v_J + v_+` with `v_+ ∈ V^{≥W_0} ⊆ π(t_i)V^{≥0}`, hence `v_J ∈ π(t_i)V^{≥0}`.
- The other half is the same. ∎

**The intersection is infinite.**
- Let `Z` be a clopen neighbourhood of the finite set `{T^sy : s ∈ J}` with `X ∖ Z` nonempty. `X` has no isolated points, so
  `X ∖ Z` is an infinite clopen set.
- Let `K_Z = {l ∈ SL_n(LC(X,F_q)) : l ≡ I on Z}`. It is infinite, and `K_Z ≤ G`, since
  `SL_n(LC(X,F_q)) = LC(X, E_n(F_q))` is generated by `e_ij(f)`, `f ∈ LC(X,F_q)`.
- `π(l)` acts position by position, `δ_s ⊗ e_j ↦ Σ_i l_ij(T^sy) δ_s ⊗ e_i`. So it fixes `V^J` pointwise (since `T^sy ∈ Z`
  for `s ∈ J`) and preserves `V^{≥W_0}` and `V^{<−W_0}`.
- By the window lemma, `π(l)` preserves `π(t_i)V^{≥0}` and `π(t_i)V^{<0}`. So `t_i^{-1}lt_i ∈ S_y`, i.e. `l ∈ t_iS_yt_i^{-1}`
  for every `i`.
- So `⋂_i t_iS_yt_i^{-1} ⊇ K_Z` is infinite. `S_y` itself is infinite by the case `m = 1`, `t_1 = e`. ∎

The same argument works in `EL_n(R)/Z(EL_n(R))`: the centre is finite, and the image of `K_Z` stays infinite.

## 4. Corollaries
### 4.1 Vanishing
For `G_X = EL_3(LC(X,F_2) ⋊ Z)` (and every `EL_n(LC(X,F_q)⋊Z)` modulo its centre), Theorem 1 gives an amenable normalish
subgroup. By BKKO Proposition `betti` (Bader–Furman–Sauer) and Proposition `thm:trivial-bdd-cohomology`:
- `β_k^{(2)}(G_X) = 0` for every `k ≥ 0`;
- `H_b^k(G_X, E) = 0` for every `k ≥ 0` and every mixing coefficient module `E`, e.g. `E = ℓ^p(G_X)`, `1 ≤ p < ∞`.

### 4.2 Property (CS) fails, and BKKO's criterion is silent
- **The derivation, as in BKKO l.945.** `H = S_y` is amenable, so `π = λ_{G/H}` is weakly regular.
  - Let `U = {T : ‖(T − I)ξ_j‖ < ε}` with `ξ_j` supported on finitely many cosets `s_1H,…,s_pH`.
  - `U` contains `⋂_i s_iHs_i^{-1}`, which is infinite. General `ξ_j` are approximated within `ε/3`.
  - So `π^{-1}(U)` is infinite, while `R_a(G_X) = {e}`. So `G_X` fails (CS).
- **The criterion.** Theorem `thm:not-c-star-simple-implies-normalish` needs no amenable normalish subgroup, and `S_y` is one.
  So that criterion cannot decide `G_X`. This is no evidence against C*-simplicity: `BS(m,n)` is C*-simple with an amenable
  normalish subgroup (BKKO l.948).

### 4.3 Route map for the open node
| criterion | applies to `G_X`? | reason |
|---|---|---|
| unique trace (BKKO Thm 4.1) | yes, known | trivial amenable radical |
| per-element averaging (Haagerup Thm B(iv)) | yes | equivalent to unique trace; no new content |
| simultaneous averaging (Haagerup Thm C(v)) | open | this is C*-simplicity |
| no amenable normalish subgroup (BKKO) | NO | Theorem 1 |
| property (CS) (BKKO §8) | NO | Theorem 1, §4.2 |
| linear-group argument (BKKO `thm:linear-groups-non-amenability-normalish`) | NO | `G_X` is not linear (f.g., infinite, simple, so not residually finite), and Theorem 1 |
| rigid stabilizers of a micro-supported action (Le Boudec–Matte Bon) | not known | no micro-supported action known (open node, Attempt 1) |
| Kennedy: no amenable confined subgroup | open | sk-cstar-simple's route |
| free boundary action (BKKO/Kalantar–Kennedy) | open | part 2 of this lane |

## 5. Model tests
- **Finite `X`.** If `X` were a finite orbit, `Z` could be all of `X` and `K_Z` trivial. The proof uses infinitude and no
  isolated points, as it should.
- **Linear groups.** BKKO prove that amenable subgroups of linear groups with trivial radical are not normalish. That is
  consistent: `G_X` is not linear.
- **Fibonacci subshift.** It satisfies every hypothesis.
- **Not confined, yet normalish.** `S_y` is normalish (Theorem 1) and not confined (sk-cstar-simple). There is no conflict:
  normalish concerns finite intersections of conjugates; confinement concerns finite sets meeting all conjugates.

## 6. Plan for part 2
- **Simultaneous Powers averaging on a G-set with amenable stabilizers.**
  - `Ω = G/S_y` has locally finite stabilizers, so `‖λ_G(x)‖ ≤ ‖λ_{G/S_y}(x)‖` for `x ∈ C[G]`, since `λ_G ≺ λ_{G/H}` for
    amenable `H`.
  - A Powers partition for finite `F ⊆ G ∖ {e}` on `Ω` (`fD ∩ D = ∅` and `N` disjoint translates of the complement) would
    give simultaneous averaging.
  - The difficulty: transvections with small support fix many cuts.
- **A topologically free boundary action.** Candidates: closures of `G·V^{≥0}` in `Sub(M)`, with the row shears
  `diag(u^{N_1},u^{N_2},u^{N_3})` as contracting elements.
- **Ping-pong for conjugates.** For finite `P ⊆ G ∖ {e}`, find `g_1,g_2,g_3` such that every choice of `p_i ∈ P` makes
  `⟨g_i^{-1}p_ig_i⟩` non-amenable. Then no amenable subgroup is confined, and Kennedy's criterion applies.
