# The l2 Morse inequality, the relation gap, and a lamplighter failure of fixed-list attainment

Written 2026-09-17 by swarm worker `swarm-0917-w5-fp-cycle-tail`. This is a written deduction over established
nodes and standard trace conventions. Nobody has refereed it or checked it formally. It continues
`bernoulli-morse-collapse-criterion.md` (the "collapse note"), whose notation is used throughout.

## 0. Summary

- **Theorem C (l2 Morse inequality).** For every finite list `R` of trivial words and every Morse matching `M`,
  `mu(M) <= rho(R) := dim_R cl im d2^R`, where `d2^R` is the cellular boundary of the `R`-cells in the Cayley graphing
  `Phi_S`. Equivalently, the unmatched cells have density at least `dim_R ker d2^R`.
- **Decomposition.** `m(R) = gap(R) + A(R)`, with the *relation gap* `gap(R) = z(Phi_S) - rho(R) >= 0` and the
  *attainment defect* `A(R) = rho(R) - sup_M mu(M) >= 0`. The gap along the full lists `P_L` is the cycle tail
  `tau_L(Phi_S)`, which tends to `0`. So
  `lim_L m(P_L) = lim_L A(P_L)`: the open premise `fpbs-morse-deficit-vanishes-for-full-presentations` is purely an
  attainment statement for the l2 bound.
- **Theorem D (lamplighter).** For `Gamma = Z/2 wr Z`, `S = {a, t}`, every finite list `R` has
  `m(R) >= gap(R) >= 2^-(K(R)+1) > 0`, where `K(R)` is the least `K` with `R` in the normal closure of
  `R_K = {a^2, [a, t^k a t^-k] : 1 <= k <= K}`. Yet `C_sub(S) = 1 = C(b) = 1 + beta_1`.
  So Target and (Q3) hold while (Q1) and (Q2) fail. Fixed-list Morse attainment is not a universal strategy: it dies
  at Theorem C on any group whose relation gap is positive for every finite list.
- Theorem C also recovers Proposition C of the collapse note (the proper-power ceiling) and the Remark after Theorem A
  (unmatched density at least `beta_2`), for arbitrary finite lists.

## 1. Modules and conventions

Imported conventions, exactly as used by `fpbs-graphing-cost-betti-cycle-dimension-identity` (Section 2 of
`cost-cycle-structure.md`, sources [G02, L, B, S] there):

- For a Borel set `E` of edges of `Phi_S` (edges are pairs `(x, s)` in `X x S`, as in the collapse note), `C_1(E)` is
  the Hilbert `R_b`-module of orbitwise square-summable chains supported on `E`. Its dimension is `nu(E)`. In
  particular `dim C_1(Phi_S) = |S|`, and `C_1(E)` and `C_1(E^c)` are complementary submodules.
- The vertex module `C_0` has dimension `1`. The cell module `C_2^R`, with one basis vector per cell `(x, r)`, is
  `|R|` copies of `C_0`, of dimension `|R|`.
- Dimension is additive on orthogonal decompositions, monotone on submodules, continuous along increasing closed
  spans, and the closed image of a bounded module map has dimension at most that of its domain.
- *Trace of a translation operator.* A bounded operator on `C_0` (or on copies of it) given on every orbit by the
  same finite formula `xi -> sum_j c_j xi(g_j^-1 . )`, with fixed `g_j` in `Gamma`, is a module map. Its trace is
  `sum_j c_j mu{x : g_j.x = x}`, which by freeness is the coefficient of `g_j = 1`. The dimension of the image of a
  module projection is its trace.

All operators below are of this finite-formula kind: they act on every orbit by the same finite combination of
translations by fixed group elements, so they are bounded module maps. On each orbit, via the identification of the
collapse note (Section 1, "Convention"), `Phi_S` is the Cayley multigraph `Cay(Gamma, S)` with edges `Gamma x S`,
and formulas can be written in group notation. We do so.

**Boundary operators.**

- `d1 : C_1(Phi_S) -> C_0`, `e_(g,s) -> delta_(gs) - delta_g`.
- `d2^R : C_2^R -> C_1(Phi_S)` sends a cell to the signed chain of its boundary path. The coefficient of an edge is
  the number of forward minus backward traversals.
- `d1 d2^R = 0`. Write `Z_R := cl im d2^R` and `rho(R) := dim Z_R`.
- `ker d1` has dimension `|S| - 1` (proof of the identity: `d1` has dense image because orbits are infinite).
- The closed span of all finite cycles is `Z := cl ∪_L Z_(P_L)`, of dimension `z(Phi_S) = |S| - 1 - beta_1^(2)(Gamma)`.
  Indeed a closed path of length at most `L` reads a trivial word of length at most `L`, so `Z_(P_L)` is exactly the
  closed span of cycles of length at most `L`, and `rho(P_L) = z_L(Phi_S)`.

**Normal closure.** For a trivial word `w`, let `chain(w)` be the chain of the path reading `w` from the base point.
If `w = prod_j u_j r_j^(+-1) u_j^-1` freely, the segments `u_j` and `u_j^-1` cancel, and `chain(w)` is a signed sum
of translates of chains of the `r_j`. Hence `Z_R` depends only on the normal closure `N_R` in `F_S`, and
`N_R ⊆ N_R'` implies `Z_R ⊆ Z_R'`.

## 2. Theorem C: the l2 Morse inequality

**Theorem C.** Let `R` be a finite list of trivial words and `M` a Morse matching for `R` ((M1)–(M3) of the collapse
note). Then

```text
mu(M) <= rho(R) = dim_R cl im d2^R,     equivalently     |R| - mu(M) >= dim_R ker d2^R.
```

**Proof.**

1. *The removed-edge module.* `E_M` is Borel and `nu(E_M) = mu(M)` (proof of Theorem A(b) in the collapse note). So
   `dim C_1(E_M) = mu(M)`. Let `P` be the orthogonal projection of `C_1(Phi_S)` onto `C_1(E_M)`. It is multiplication
   by the indicator of `E_M`, a module map.
2. *Dense range.* Put `T = P d2^R : C_2^R -> C_1(E_M)`. We show `T` has dense range. Let `eta` be in `C_1(E_M)` and
   orthogonal to the range of `T`. Since `P eta = eta`, this says `(d2^R)^* eta = 0`. For a cell `c`,
   `((d2^R)^* eta)(c)` is the sum over the traversals of `bd(c)` of `+-eta(edge)`, with sign `+1` for forward
   traversals.
   - Let `h(e)` be the height of the recovery tree `T(e)` of a removed edge `e`. By (M3) and König's lemma (proof of
     Theorem A(a)) it is finite for `nu`-a.e. `e`. It is Borel, because each depth of the tree is defined by finitely
     many Borel partial maps.
   - Fix `e = M(c)`. By (M1), `e` is traversed exactly once by `bd(c)`, so its coefficient is `+-1`, and
     `0 = +-eta(e) + (sum over the other traversals of +-eta(e'))`.
     Every other traversed edge `e'` either lies outside `E_M`, where `eta(e') = 0`, or is a child of `e`, with
     `h(e') < h(e)`.
   - By induction on `n`, `eta = 0` a.e. on `{h <= n}`. The step uses that `M^-1` and the child maps are finite unions
     of Borel partial translations by fixed group elements, so they carry null sets to null sets. Hence for a.e. edge
     `e` of height `n`, `eta` vanishes on every child of `e`, and the displayed equation gives `eta(e) = 0`.
   - So `eta = 0`.
3. *Counting.* `cl im T = cl P(Z_R)` is the closed image of the module map `P` restricted to `Z_R`. So
   `mu(M) = dim C_1(E_M) = dim cl im T <= dim Z_R = rho(R)`.
4. The second form is additivity: `|R| = dim C_2^R = dim ker d2^R + dim cl im d2^R`. QED.

**Remark.** The proof uses (M1) and (M3) for the height induction, and (M2) through `nu(E_M) = mu(M)`. It never uses
that `Phi_S \ E_M` generates. Theorem C is the l2 shadow of Theorem A: Theorem A converts matched mass into cost, and
Theorem C caps matched mass by the rank of the relator boundary.

## 3. Consequences

**3.1 The decomposition of the deficit.** Define

```text
gap(R) := z(Phi_S) - rho(R) = dim(ker d1 ⊖ Z_R) - beta_1^(2)(Gamma),
A(R)   := rho(R) - sup_M mu(M).
```

- `gap(R) >= 0` because `Z_R ⊆ Z`, and `A(R) >= 0` by Theorem C. So `m(R) = gap(R) + A(R)`, a sum of two
  nonnegative terms.
- `gap` is nonincreasing in the normal closure `N_R` (Section 1).
- `gap(P_L) = z - z_L = tau_L(Phi_S)`. This tends to `0` as `L -> infinity`, by the fixed-graphing statement of
  `fpbs-graphing-cost-betti-cycle-dimension-identity`, or directly by continuity of dimension along the increasing
  closed spans `Z_(P_L)`.
- Therefore `lim_L m(P_L) = lim_L A(P_L)`. Both limits exist, because `m(P_L)` is nonincreasing (Theorem B of the
  collapse note) and `gap(P_L) -> 0`.
- Combined with Theorem B(ii), `C_sub(S) - 1 - beta_1^(2)(Gamma) = lim_L A(P_L)`. So the premise
  `fpbs-morse-deficit-vanishes-for-full-presentations` holds iff well-founded Borel matchings asymptotically attain the
  l2 rank of the relator boundary.

**3.2 Finitely presented groups.** If `<S | R>` is a finite presentation, every trivial word lies in `N_R`. So
`Z_R = Z`, `gap(R) = 0` and `m(R) = A(R)`. For finite presentations there is no l2 obstruction, and (Q1) for `R` is
exactly `A(R) = 0`, a purely combinatorial question.

**3.3 Recovering the proper-power ceiling.** Let `R = {w^m}`, where `w` has order `m` and the path reading `w^m`
traverses each edge once.

- The `m` cells `(w^-j . x, w^m)` have the same boundary chain. So `d2^R = d2^R p`, where
  `p = (1/m) sum_(j<m)` (translation of cells by `w^j`) is a module projection of trace `1/m`.
- Hence `rho(R) <= 1/m`, and Theorem C gives `mu(M) <= 1/m`.
- Restricting a Morse matching for a larger list to the cells of type `w^m` gives a Morse matching, since (M3) only
  loses children. This recovers Proposition C of the collapse note.

**3.4 Recovering the unmatched-density bound.** The second form of Theorem C bounds the unmatched cells below by
`dim_R ker d2^R`, the measured second l2 homology of the 2-complex of `R`. For a finite presentation this is the
relation-level form of the Remark after Theorem A of the collapse note, and Theorem C extends it to every finite list.

## 4. Theorem D: the lamplighter

**Setting.** `Gamma = Z/2 wr Z = <a, t>`, `S = {a, t}`, with the multigraph convention of the collapse note (so the
involution `a` contributes two parallel edges per pair and `c(Phi_S) = 2`). Put `a_i = t^i a t^-i`. For `K >= 1` let
`R_K = {a^2} ∪ {[a, a_k] : 1 <= k <= K}`, where `[a, a_k]` is the word `a t^k a t^-k a t^k a t^-k`. Let
`A = <a_0, ..., a_K>` and `B = <a_1, ..., a_K>`, elementary abelian of orders `2^(K+1)` and `2^K`.

**Lemma 4.1 (every finite list is caught by some `R_K`).** Every word trivial in `Gamma` lies in `N_(R_K)` for some
`K`.

*Proof.* Let `G = <a, t | a^2, [a, a_k] (k >= 1)>` and `N_inf = ∪_K N_(R_K)`. In `G`, conjugating `[a_0, a_k]` by `t^i`
shows that all `a_i` commute and have order at most 2. So the normal closure `V` of `a` in `G` is the abelian group
generated by the `a_i`, a quotient of `⊕_Z Z/2`, and `G/V = Z`. The map `G -> Gamma` is injective on `V` (the `a_i`
are independent lamps in `Gamma`) and induces the identity on `Z`, so it is an isomorphism. Hence the trivial words
form `N_inf`, and a word in `N_inf` lies in one `N_(R_K)` because these normal subgroups increase. QED.

For a finite list `R`, let `K(R)` be the least such `K` for all words of `R` together.

**Theorem D.** For every finite list `R` of trivial words,

```text
m(R) >= gap(R) >= 2^-(K(R)+1) > 0.
```

On the other hand `C_sub(S) = 1 = C(b) = 1 + beta_1^(2)(Gamma)` and `lim_L m(P_L) = 0`. So for this group Target and
(Q3) hold while (Q1) and (Q2) fail.

**4.2 The quotient graph `Y`.** Fix `K = K(R)`.

- Let `p_A` on `C_0` be `delta_g -> (1/|A|) sum_(a' in A) delta_(g a')`, and `V_Y = im p_A`, the vectors constant on
  right `A`-cosets.
- Let `C_1^t` be the chains on `t`-edges, and `p_B` on `C_1^t` be `e_(g,t) -> (1/|B|) sum_(b in B) e_(gb,t)`. Let
  `E_Y = im p_B`.
- These are finite-formula module projections, with traces `1/|A| = 2^-(K+1)` and `1/|B| = 2^-K` (Section 1, by
  freeness). So `dim V_Y = 2^-(K+1)` and `dim E_Y = 2^-K`.
- Put `d^Y = p_A d1` restricted to `E_Y`, and define the chain map `phi_0 = p_A`, `phi_1 = p_B pi_t`, where `pi_t`
  kills the `a`-edges.
- *Chain map.* `p_A d1 e_(g,a) = p_A(delta_(ga) - delta_g) = 0 = d^Y phi_1 e_(g,a)`. For a `t`-edge,
  `p_A d1 p_B e_(g,t) = (1/|B|) sum_b p_A(delta_(gbt) - delta_(gb)) = p_A(delta_(gt) - delta_g)`, because
  `gbt A = gt (t^-1 b t) A = gt A`, where `t^-1 B t = <a_0, ..., a_(K-1)> ⊆ A`. So `phi_0 d1 = d^Y phi_1`. In
  particular `phi_1(ker d1) ⊆ ker d^Y`.

**4.3 `dim ker d^Y = 2^-(K+1)`.** Let `xi` be in `V_Y` with `(d^Y)^* xi = 0`. Pairing with `p_B e_(g,t)` and using the
computation above gives `xi(gt) = xi(g)` on every orbit. Also `xi(ga) = xi(g)`, since `a` is in `A`. So `xi` is
constant on each orbit, which is infinite, and `xi = 0`. Thus `d^Y` has dense range, and by additivity
`dim ker d^Y = 2^-K - 2^-(K+1) = 2^-(K+1)`.

**4.4 `phi_1` kills `Z_R`.** By Lemma 4.1 and Section 1, `Z_R ⊆ Z_(R_K)`, so it suffices to show
`phi_1 d2^(R_K) = 0`.

- `a^2` has no `t`-edges.
- For `[a, a_k]` from a base point `g`, the first half `a t^k a t^-k` crosses the `t`-edges `(g a t^i, t)` forward
  and `(g a a_k t^i, t)` backward, for `0 <= i < k`. Now `(g a t^i)^-1 (g a a_k t^i) = t^-i a_k t^i = a_(k-i)`, which
  lies in `B` since `1 <= k - i <= K`. So `p_B` identifies the two edges and the half is killed. The second half is
  the same computation from the base point `g a a_k`.

**4.5 `phi_1 : ker d1 -> ker d^Y` is onto.** We build a bounded module map `psi : ker d^Y -> ker d1` with
`phi_1 psi = id`.

- For each `a'` in `A` fix a word `W(a')` for `a'` (an involution) that is a product of the words `t^k a t^-k`,
  `0 <= k <= K`.
- Define `omega : C_0 -> C_1` by `omega(delta_g) = (1/|A|) sum_(a' in A) chain(path from g a' reading W(a'))`. The
  path ends at `g`, so `d1 omega(delta_g) = delta_g - p_A delta_g`. So `d1 omega = 1 - p_A`.
- `phi_1 omega = 0`: the path `t^k a t^-k` from `h` crosses `(h t^i, t)` forward and `(h a_k t^i, t)` backward, and
  `t^-i a_k t^i = a_(k-i)` is in `B` for `0 <= i < k <= K`. The `a`-letters are killed by `pi_t`.
- For `xi` in `ker d^Y` put `psi(xi) = xi - omega d1 xi`. Then `p_A d1 xi = d^Y xi = 0`, so
  `d1 psi(xi) = d1 xi - (1 - p_A) d1 xi = 0`, and `phi_1 psi(xi) = p_B xi = xi`.

**4.6 Counting.** Let `H_R = ker d1 ⊖ Z_R`. By 4.4, `phi_1(ker d1) = phi_1(H_R)`, and by 4.5 this contains
`ker d^Y`. The closed image of a module map has dimension at most that of its domain, so
`dim H_R >= dim ker d^Y = 2^-(K+1)`. Since `Gamma` is amenable, `C(b) = 1` (`fpbs-amen2-cost-inputs`), and
`beta_1^(2)(Gamma) <= C(b) - 1 = 0` (`fpbs-amen2-betti-cost-input`). So
`gap(R) = dim H_R - beta_1 >= 2^-(K+1)`, and Theorem C gives `m(R) >= gap(R)`.

**4.7 `C_sub(S) = 1`.** `R_b` is hyperfinite (Ornstein–Weiss, [GL] Thm 1.13, as imported in the complete route
`fpbs-amalgam-over-amenable-descends-fixed-price-proof`). Write `R_b = ∪_n R_n` with finite Borel subrelations
increasing.

- Let `S_n` be the relation whose classes are the connected components of the `Phi_S`-edges lying in `R_n`. These are
  finite, increasing, and their union is `R_b`: a `Phi_S`-path has finitely many edges, all in `R_n` for large `n`.
- Build Borel forests `F_1 ⊆ F_2 ⊆ ...` of `Phi_S`-edges: `F_(n+1)` adds, in a fixed Borel order, the edges of
  `Phi_S ∩ S_(n+1)` that join different components of the current forest. This is Borel because classes are
  finite, and `F_n` spans the classes of `S_n`.
- `F = ∪ F_n` is acyclic, since a cycle would lie in some `F_n`, and it generates `R_b`. It is a bounded-degree
  subgraphing of `Phi_S`, with `c(F) = lim c(F_n) = lim ∫ (1 - 1/|[x]_(S_n)|) dmu <= 1`.
- So `C_sub(S) <= 1`. Conversely `C_sub(S) >= C(b) >= 1`.

**4.8 Conclusion.** Theorem B(ii) of the collapse note gives `lim_L m(P_L) = C_sub(S) - 1 - beta_1 = 0`. For every
finite `R`, `m(R) >= 2^-(K(R)+1) > 0`. So (Q1) fails, and (Q2) fails because no finite `R` reaches the limit `0`.
Target holds because `C(b) = 1 = 1 + beta_1`, and (Q3) holds because `C_sub(S) = 1 = C(b)`. QED.

The finite combinatorics of 4.2, 4.4 and 4.5 (coset identifications, relator cancellation, correction paths, and the
failure of cancellation for `[a, a_(K+1)]`) are checked by
`experiments/fpbs-morse-l2-gap-2026-09-17/lamplighter_coset_cancellation.py`, which exits 0.

## 5. Scope, and what is not established

**What dies.** A proof of `fpbs-bernoulli-cycle-tail-compactness` through (Q1), a vanishing Morse deficit for one
finite list, cannot work uniformly over all finitely generated groups. The failing step is the mass bound of
Theorem C, and the invariant is the relation gap `gap(R)`. Every group with `gap(R) > 0` for all finite lists `R`
is out of reach, even when Target holds. The lamplighter is such a group. Any universal Morse route has to pass
through `lim_L A(P_L) = 0` over growing lists, which is the premise itself.

**What survives.**

- For finitely presented groups `gap = 0` at a presentation (3.2), and Theorem C imposes nothing beyond the
  attainment question `A(R) = 0`.
- The premise `fpbs-morse-deficit-vanishes-for-full-presentations` is untouched, and holds for the lamplighter. By 3.1
  it is equivalent to `lim_L A(P_L) = 0`.

**Remark, not established here (imports not audited).** For a Kazhdan group, Shalom's theorem gives a finite list
`R` such that `F_S / N_R` is Kazhdan. Then `H_R` is the reduced first l2 homology of the 2-complex of `R`, which is a
quotient of a simply connected complex for `F_S / N_R`. By Hodge duality it matches reduced `H^1(F_S/N_R; l2 Gamma)`,
and (T) kills that. So one expects `gap(R) = 0` for some finite `R`, and no relation-gap obstruction for Kazhdan
groups. This is recorded as a spark, not a claim.

**Not established.** Whether `A(R) = 0` for some finite presentation of any Kazhdan group or one-relator group with
torsion; whether some nonamenable group has `gap(R) > 0` for every finite `R` (a natural test is `Z/2 wr F_2`).
