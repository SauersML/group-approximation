# Adversarial audit of the orientation-lift pair (2026-09-18)

Agent `e2-w2-audit-ugc1`, wave `swarm-0917`. Targets:

* `orientation-lifts-sandwich-2to1-game-values` (ESTABLISHED, landed 2026-09-17, no referee)
* `rich-2to1-hard-at-completeness-one-half` (ESTABLISHED, landed 2026-09-17, no referee)

Three lenses were run: (1) first step that does not follow, (2) every import
against its own source with verbatim text, (3) calibration -- does the same
argument prove something false.

**Verdict: both survive.** No step is wrong. Three defects were found, all of
them in wording or in unstated hypotheses, none of them load-bearing for the
hardness statement. One genuinely new obstruction fell out of lens (2) and is
recorded in Section 4. The novelty of
`rich-2to1-hard-at-completeness-one-half` is lower than the node suggests: it is
a two-line composition of two statements that the Braverman--Khot--Minzer paper
makes itself (Section 3).

Sources were downloaded and read on 2026-09-18:

* KMS = Khot, Minzer, Safra, *Pseudorandom Sets in Grassmann Graph have
  Near-Perfect Expansion*, ECCC TR18-006 (Revision 2, 19 May 2018), FOCS 2018.
* DKKMS-1 = Dinur, Khot, Kindler, Minzer, Safra, *Towards a Proof of the 2-to-1
  Games Conjecture?*, ECCC TR16-198 (14 Dec 2016), STOC 2018.
* BKM = Braverman, Khot, Minzer, *On Rich 2-to-1 Games*, ITCS 2021
  (LIPIcs vol. 185, paper 27); full version ECCC TR19-141.

---

## 1. Lens 1: the mathematics

### 1.1 The orientation lift is well defined and `U_o` really is a unique game

`p_e : [2k] -> [k]` is exactly 2-to-1 and `o_e : [2k] -> {0,1}` is injective on
each fibre, so `a -> (p_e(a), o_e(a))` is injective from a set of size `2k` into
`[k] x {0,1}`, of size `2k`, hence bijective. **Checks out.** Note that it is the
lift, not any gadget, that makes the two alphabets equal: this is what lets the
BKM merge `Psi` (which needs a unique game with an *even* alphabet) be applied
to the output of a 2-to-1 hardness theorem whose right alphabet is `[k]`.

### 1.2 The sandwich `val(G)/2 <= val(U_o) <= val(G)`

Upper: forget the bit; a satisfied lift edge forces `p_e(L_u) = m_v`. Lower:
independent uniform bits `c_v`, each satisfied `G`-edge survives with
probability exactly `1/2`, so some choice attains `val_G/2`. **Checks out**, and
both ends are attained (the two parallel edges with opposite orientations give
the lower end). Nothing here uses linearity, weights, or the structure of `G`.

### 1.3 `Psi` and the bounds `val(U) <= val(Psi(U)) <= 2 val(U)`

Fix a left labelling `a` and let `p_v` be the law of `phi_(uv)(a(u))` over the
edge distribution at `v`. Then
`val_U(a) = E_v max_b p_v(b)` and
`val_(Psi(U))(a) = E_v E_sigma max_j p_v(sigma^(-1)(j))`. A fibre has two
elements so `max_j p_v(sigma^(-1)(j)) <= 2 max_b p_v(b)`, and taking
`j = sigma(argmax)` gives the reverse. Both inequalities hold pointwise in `a`,
so they survive the maximisation. **Checks out.** The counting
`|S_(2k,k)| = (2k)!/2^k` in the proof file is correct (it is the number of
2-to-1 *maps*, not of partitions; BKM Lemma A.5 uses the same denominator).

### 1.4 Polynomial time and the shape of the output

`k = k(eps)` is a constant, so `|S_(2k,k)|` is a constant, `Psi` blows the right
side up by a constant factor, and the lexicographic orientation is computable in
linear time. `Psi(U_o)` has left alphabet `[2k]`, right alphabet `[k]`, and every
edge map `sigma o phi` is exactly 2-to-1 because `phi` is a bijection.
**Checks out.**

### 1.5 The gap arithmetic

YES `val(G) >= 1 - eps/2` gives `val(Psi(U_o)) >= val(U_o) >= (1-eps/2)/2 >=
(1-eps)/2`. NO `val(G) <= eps/2` gives `val(Psi(U_o)) <= 2 val(U_o) <=
2 val(G) <= eps`. **Checks out.**

### 1.6 Defect D1 (wording, not load-bearing)

Item (3) of `orientation-lifts-sandwich-2to1-game-values` states

```text
val(U_o) = max_L sum_v max_b w_v(L, b),
```

with `w_v(L, b)` defined on the claim node as "the weight of edges `e = (u,v)`
that `L` satisfies in `G`, **with the best right label**, and whose branch is
`o_e(L_u) = b`". Read literally -- fix the `G`-optimal right label `m*` at `v`,
then split that mass by branch -- the identity is **false**; it can strictly
undercount. Explicit instance (`k = 2`, one right vertex `v`, three left
vertices, `p_e : {0,1} -> 0, {2,3} -> 1` on every edge):

| left vertex | weight | label | `p_e(L_u)` | branch |
|---|---|---|---|---|
| `u1` | `3/10` | `0` | `0` | `0` |
| `u2` | `3/10` | `1` | `0` | `1` |
| `u3` | `4/10` | `2` | `1` | `0` |

Here `val(G) = 3/5` with `m* = 0`; the literal formula returns `3/10`; the true
`max_(m,b)` is `2/5`, attained at `(m, b) = (1, 0)`. Replayed by
`experiments/audit-rich-2to1-one-half-2026-09-18/check_bipartization_and_branch_formula.py`,
part (B).

The **derivation file repairs the reading** -- "where `w_v(L,b)` uses the best
`m` for the branch. (Maximizing `m` inside `b` is the same as outside, since
both maxima are over pairs.)" -- and under `w_v(L,b) = max_m w_v(L,m,b)` the
identity is correct. So this is a claim-node phrasing bug, not a proof bug.

Two downstream sentences inherit it and are **wrong as written**:

* "So `U_o` loses exactly the minority branch mass at each right vertex"
  (sandwich node, item 3). In the instance above the lift loses `1/5`, while the
  minority branch mass at `m*` is `3/10`.
* "By item (3) of the sandwich, the lift loses exactly that minority mass"
  (`efficient-branch-selector-on-proved-2to1-instances`, "Can fail on its own").

Neither is used in a derivation. Item (3) does not enter
`rich-2to1-hard-at-completeness-one-half-proof` at all.

### 1.7 Defect D2 (quantifier, cosmetic)

The claim reads "For every `eps > 0`". The promise `[(1-eps)/2, eps]` is empty
unless `eps < 1/3`, so the statement is only meaningful for small `eps`. BKM's
own `Gap-Rich-2-to-1_n[1-eps, eps]` has the same convention. Harmless.

---

## 2. Lens 2: imports, quoted

### 2.1 Does `Psi(U_o)` produce RICH instances in the sense the conjecture requires?

BKM full version, Section 1.2, **Definition 1.5** and the paragraph before it,
verbatim:

> Let `Psi = (L u R, E, Sigma_L, Sigma_R, Phi)` be a 2-to-1-Game, with
> `|Sigma_L| = 2n` and `|Sigma_R| = n`. Fix a vertex `u in L`. Let
> `e = (u,v) in E` be an edge incident on `u` and let `pi_e` be the 2-to-1
> projection defining that constraint. The map defines a partition of `Sigma_L`
> as `Sigma_L = u_(rho in Sigma_R) pi_e^(-1)(rho)` into disjoint sets of size 2.
> Let us denote by `P(u)` the distribution over partitions of `Sigma_L` into
> sets of size 2, given by first sampling a **uniformly random edge**
> `e = (u,v)` incident on `u` and then outputting the partition of `Sigma_L` as
> above.
>
> **Definition 1.5.** An instance of Rich 2-to-1 Games is an instance of 2-to-1
> Games with the additional property that for every vertex `u in L`, the
> distribution `P(u)` is uniform over all partitions of `Sigma_L` into sets of
> size 2.

BKM **Definition 1.1**, verbatim: "A 2P1R Games instance
`Psi = (L u R, E, Sigma_L, Sigma_R, Phi)` consists of a **regular, bipartite**
graph `(L u R, E)`, ...".

Two hypotheses are therefore in BKM's definition that the audited nodes do not
mention: the graph is **regular**, and the edge at `u` is sampled **uniformly**,
not by weight. The audited claim writes "a weighted random incident edge ...
(BKM Definition 5, with edge weights read as multiplicities)".

**Defect D3 (unstated hypothesis), and why it is harmless here.** In `Psi(U_o)`
the merge map `sigma` is drawn independently of the edge, so conditioned on `u`
the induced partition is `phi_(uv)^(-1)` of a uniform partition, which is
uniform *for every* law on the neighbour `v`. Hence `P(u)` is exactly uniform
under any edge weighting, and in particular under the uniform law of the
multigraph obtained by reading rational weights as multiplicities. Regularity is
likewise inherited: `Psi` multiplies every left degree by `|S_(2k,k)|` and
leaves every right degree unchanged, so `Psi(U_o)` is biregular whenever `G` is,
and the DKKMS-1 games are 2P1R games in the sense of its Definition 1.1. So the
richness the reduction delivers **is** BKM Definition 1.5 richness. The nodes
should say this; as written they assert the weighted reading without arguing it.

### 2.2 Is `Psi` the BKM merge?

BKM full version, **Appendix B**, verbatim:

> Given a Unique Games instance `Phi = (L u R, E, Sigma, Phi)`, we construct a
> Rich 2-to-1 Games instance `Psi = (U u V, E', Sigma_U, Sigma_V, Psi)` as
> follows. First, note that we may assume that the size of the alphabet in
> `Phi`, namely `|Sigma|`, is even[3], and we assume `Sigma = [2k]` for
> `k in N` henceforth. To construct the instance `Psi`, let `U` be a copy of `L`
> and set `Sigma_U = Sigma`. Also, define `V = R x S_(2k,k)` (recall that
> `S_(2k,k)` is the set of all 2-to-1 mappings from `[2k]` to `[k]`) and
> `Sigma_V = [k]`; a label `j` of a vertex `(v,pi)` should be thought of as
> "one of the labels in `pi^(-1)(j)`" for `v`. The vertices `u in U` and
> `(v,pi) in V` are adjacent in `Psi` if `(u,v)` is an edge in `Phi`, and the
> constraint on them is given by
> `Psi(u,(v,pi)) = { (i,j) | exists sigma_v in pi^(-1)(j) such that
> (i,sigma_v) in Phi(u,v) }`. This completes the description of the reduction.
> The completeness of the reduction, as well as the fact that `Psi` is a Rich
> 2-to-1 Games instance, are both easy to see. For the soundness, given
> assignments `A : U -> Sigma_U` and `B : V -> Sigma_V` satisfying
> `delta`-fraction of the constraints in `Psi`, one can construct assignments
> `A', B'` for `Phi` satisfying at least `delta/2` fraction of the constraints,
> as follows: take `A' = A`, and for `B'` is the randomized assignment defined
> on each `v in V` by taking `pi in S_(2k,k)` uniformly, picking an element
> `sigma in pi^(-1)(B(v,pi))` uniformly and setting `B'(v) = sigma`.

For a unique game `Phi(u,v) = {(i, phi_(uv)(i))}` the constraint reduces to
`j = pi(phi_(uv)(i))`, i.e. to `sigma o phi` in the repository's notation. So
`Psi` in `sd-rich-and-unique-games-sos-gaps-interconvert` item (a) **is** BKM's
Appendix B reduction, its value bounds are BKM's own completeness remark and
BKM's soundness paragraph, and the even-alphabet padding used in consequence (b)
is BKM's footnote 3, verbatim: "Otherwise, we may construct a Unique Games
instance `Phi'` on the same graph whose alphabet is `Sigma x {0,1}`, and for
each edge `(u,v)`, the constraint `Phi'(u,v)` demands that the label
`(sigma_u, b_u)` of `u` and `(sigma_v, b_v)` of `v` satisfy
`(sigma_u, sigma_v) in Phi(u,v)` and `b_u = b_v`. It is easy to see that the
value of both instances is equal." **All three imports check out exactly.**

### 2.3 Step 1: is `Gap-2-to-1[2k](1-eps, eps)` really available?

This is the one import the route consumes that is *not* the headline theorem of
its source. `two-to-two-games-theorem` cites KMS Theorem 1.4
(`Gap 2-to-2[F_2^l](1-eps, eps)` NP-hard) and then adds, in prose, "As the
source's footnote 2 records, the linear constraints reinterpret as 2-to-1
constraints, so this also proves the 2-to-1 Games Conjecture with imperfect
completeness." The route file `two-to-two-games-theorem-citation` verifies
Definition 1.3, Theorem 1.4 and the abstract, but **does not verify footnote 2**,
even though footnote 2 is the sentence Step 1 actually consumes.

KMS footnote 2 (page 2), verbatim:

> Comments regarding the original formulation of this conjecture in [8]: (1) It
> was proposed with perfect completeness, i.e. stating that
> `Gap 2-to-2[F_2^l](1, eps)` is NP-hard. However, as far as this paper is
> considered, we view the issue of perfect versus imperfect completeness as
> being relatively minor. (2) It was proposed with more general constraints
> (rather than the special case with linear structure described herein) and with
> "2-to-1" constraints (rather than with "2-to-2" constraints described herein;
> the conjecture was referred to as the 2-to-1 Conjecture). Both these are
> non-issues however: the current and preceding works [12, 3, 4] now prove the
> conjecture with linear structure and the constraints are easily reinterpreted
> as being 2-to-1 constraints (hence proving the 2-to-1 Conjecture as well,
> which in any case is morally equivalent to the 2-to-2 Conjecture).

So the repository's paraphrase is faithful. But footnote 2 exhibits no
transformation, and Section 4 below shows that the obvious one loses the gap.
The statement Step 1 needs is instead available **directly**, with the exact
shape the route uses, from DKKMS-1. DKKMS-1 **Definition 1.2**, verbatim:

> **(d-to-1 Games)** Let `G = (A, B, E, Pi, Sigma_A, Sigma_B)` be a
> 2-Prover-1-Round game, and let `d >= 1` be an integer. A constraint
> `pi_uv in Pi` is said to be `d`-to-1 if there is a partition
> `S_1, ..., S_r` of `Sigma_A` into sets of size `d` and an ordering
> `b_1, ..., b_r` of `Sigma_B` such that `pi_uv = U_(i=1)^r S_i x {b_i}` (this
> also implies that `|Sigma_A| = dr`, `|Sigma_B| = r`). We say that
> `G = (A,B,E,Pi,Sigma_A,Sigma_B)` is a `d`-to-1 game if all constraints in `Pi`
> are `d`-to-1.

and DKKMS-1 **Theorem 1.2**, verbatim:

> Assume Hypothesis 3.6. Then for every constant `delta > 0`, for a sufficiently
> large constant `|Sigma_A|`, given a 2-to-1-Game
> `G = (A,B,E,Pi,Sigma_A,Sigma_B)` it is NP-hard to distinguish between:
> * YES case: there is a coloring satisfying `1 - delta` fraction of the
>   constraints of `G`. Moreover, one can remove a `delta` fraction of the
>   vertices and all of the constraints adjacent to them, such that this
>   coloring satisfies all of the remaining constraints.
> * NO case: no coloring satisfies more than `delta` fraction of the constraints
>   of `G`.

DKKMS-1's value is the edge fraction ("the maximum acceptance probability of the
verifier over all prover strategies is then the same as the maximum fraction of
the constraints that can be satisfied by a coloring"). With `d = 2` this is
*exactly* `Gap-2-to-1[2k](1-delta, delta)` on a bipartite game with
`|Sigma_A| = 2 |Sigma_B|` -- the shape Step 1 asserts. Hypothesis 3.6 is
discharged by KMS Theorem 1.8 ("It has already been shown in [12, 3, 4] (along
with an important contribution from Barak, Kothari, and Steurer [2]) that the
above Theorem 1.8 implies the 2-to-2 Games Conjecture!") together with footnote
2. A third, independent statement of the same fact is BKM's own opening
sentence: "Recently, a related conjecture called the 2-to-1 Games Conjecture has
been proved [16, 6, 5, 17]."

**Verdict on Step 1: the import is correct and is better anchored than the
repository records.** The right citation for the 2-to-1 form is DKKMS-1
Definition 1.2 + Theorem 1.2, with KMS Theorem 1.8 + footnote 2 discharging
Hypothesis 3.6 -- not KMS footnote 2 alone.

---

## 3. Novelty: the claim is a corollary the source states itself

BKM, ITCS version, Section 1.1, on the 2-to-1 Games Theorem: "... as a sequence
of papers [16, 6, 5, 17] (with additional contributions from [3, 15]), also
proving as a simple corollary that `Gap-Unique[1/2, eps]` is NP-hard (for every
`eps > 0` and for sufficiently large alphabet size)." And Theorem 1.8: "The
reduction from Unique Games to Rich 2-to-1 Games is straightforward, and is
given in Appendix B for completeness."

Composing those two published sentences gives, in two lines and with no
orientation lift:

```text
Gap-Unique[1/2, eps]  --BKM footnote 3-->  even alphabet, same value
                      --BKM Appendix B-->  Gap-Rich-2-to-1[1/2, 2 eps].
```

That is `rich-2to1-hard-at-completeness-one-half` with a *better* completeness
(`1/2` rather than `(1-eps)/2`). The claim node is honest -- "This is not a new
hardness phenomenon" -- but its route takes a longer path, through the 2-to-1
form of the 2-to-2 theorem and the orientation lift, and so inherits the
Section 2.3 import that the short path does not need. **Recommended repair:
record the short path as a second, import-only route**, so the claim no longer
depends on footnote 2 at all. That work is not done here (a worker may edit only
the frontmatter and `## Attempts` of its one target claim).

What is *not* redundant is the sandwich node's consequence (b), the
single-parameter reformulation. It is a genuine iff and it is not in BKM.

---

## 4. Lens 2 by-product: a precise obstruction (NEW)

Reading KMS footnote 2 as "there is a generic gap-preserving transformation of a
linear 2-to-2 game into a bipartite 2-to-1 game" is **false**, and quantitatively
so.

**Setting.** Let `U` be an instance of `2-to-2 Game[F_2^l]` (KMS Definition 1.3)
with constraints `T_c x_i + T'_c x_j in {b_c, b'_c}`, `b_c != b'_c`, of weight
`w_c`. Put `d_c = b_c + b'_c`, `H_c = {0, d_c}`, and let
`q_c : F_2^l -> F_2^l / H_c` be the quotient, which is exactly 2-to-1 onto a set
of size `2^(l-1)`. The constraint says exactly
`q_c(T_c x_i + b_c) = q_c(T'_c x_j)`. The only bipartization that keeps the
2-to-1 alphabet ratio `(2k, k)` with `k = 2^(l-1)` and puts one fresh right
vertex per constraint is

```text
B(U):  left  = variables,   Sigma_left  = F_2^l           (size 2k)
       right = constraints, Sigma_right = F_2^l / H_c      (size k)
       edges (x_i, c): a -> q_c(T_c a + b_c)   of weight w_c/2
             (x_j, c): a -> q_c(T'_c a)        of weight w_c/2
```

Every edge map is exactly 2-to-1, so `B(U)` is a 2-to-1 game in the sense of
DKKMS-1 Definition 1.2.

**Identity.** `val(B(U)) = (1 + OPT(U)) / 2`, exactly, for every `U`.

*Proof.* Fix a left assignment `A`. At the right vertex `c` the two edges demand
the classes `q_c(T_c A_i + b_c)` and `q_c(T'_c A_j)`. These are equal iff
`T_c A_i + T'_c A_j + b_c in H_c`, i.e. iff `c` is satisfied by `A`. So the best
right label gains `w_c` when `c` is satisfied and `w_c/2` when it is not, giving
`val_B(A) = (1 + val_A(U))/2`. The right side is determined by `A`, so
maximising over `A` gives the identity. `square`

**Consequence.** `B` maps `Gap 2-to-2[1-eps, eps]` to
`Gap 2-to-1[1 - eps/2, (1+eps)/2]`. The soundness is **above one half** for every
`eps`, so no choice of parameters recovers `Gap-2-to-1[1-eps, eps]`. The
constraints with `b_c = b'_c`, which KMS Definition 1.3 permits, are not 2-to-1
at all under this reading -- they are unique.

So the 2-to-1 form of the 2-to-2 Games Theorem cannot be obtained from a generic
per-constraint bipartization; it has to be taken from DKKMS-1 Theorem 1.2, whose
Grassmann game (`A`-vertices are `l`-spaces `L` with labels the functionals on
`L`, `B`-vertices are hyperplanes `L'` with labels the functionals on `L'`, the
constraint is restriction) is natively 2-to-1 with `|Sigma_A| = 2 |Sigma_B|`.

Replayed by
`experiments/audit-rich-2to1-one-half-2026-09-18/check_bipartization_and_branch_formula.py`,
part (A): 400 random instances over `F_2^l`, `l in {1,2,3}`, 0 failures, exact
rationals, with each edge map verified to be exactly 2-to-1.

**A remark worth keeping.** The same constant `1/2` appears twice, from opposite
sides. Going *down* the ladder, the orientation lift `2-to-1 -> UG` loses a
factor 2 in *completeness* (item (1) of the sandwich: the right bit is a free
coin). Going *up* the ladder, the per-constraint bipartization `2-to-2 -> 2-to-1`
loses to `1/2` in *soundness* (Section 4). Both losses are the same random bit,
read once as the lift's branch and once as the choice of which of a right
vertex's two edges to satisfy.

---

## 5. Lens 3: calibration -- does the argument prove anything false?

| Test | Outcome |
|---|---|
| Does it prove UG hardness directly? | Yes: `x -> U_o(R(x))` gives `Gap-UG[(1-eps)/2, eps]`. That is **exactly** `unique-games-hard-at-completeness-one-half`, itself KMS's own Appendix B corollary. The reduction lands **on** the known one-half wall, not past it. This is the strongest available calibration signal: an argument that proved too much would have crossed `1/2`. |
| Does it prove hardness above completeness `1/2`? | No. Item (1) gives only `val(U_o) >= val(G)/2` for an arbitrary orientation, and item (1)'s tightness example (two parallel edges with opposite orientations) shows the floor is attained. Beating it is exactly the open node `efficient-branch-selector-on-proved-2to1-instances`. |
| Does it prove perfect-completeness rich 2-to-1 hardness, contradicting `perfect-completeness-rich-2to1-tractable-skeletons-are-in-p`? | No, and the two are consistent for a sharp reason. That kill needs `val(R(x)) = 1` on YES inputs; here `val(Psi(U_o)) <= 2 val(G) ` but also `val(U_o) <= val(G) <= 1 - eps/2 < 1`, because 2-to-1 hardness is *inherently* imperfect-complete (DKKMS-1: "This is inherent in our construction due to the linearity in the overall reduction"). If any orientation gave `val(U_o) = 1` on a satisfiable `G`, `Psi(U_o)` would be satisfiable and the skeleton kill would apply. It never does. |
| Linear unique games in P? | Gaussian elimination solves *satisfiable* linear systems. Completeness here is `1/2`, so the promise is never satisfiability. Indeed `unique-games-hard-at-completeness-one-half` is itself a hardness statement about **linear** unique games at completeness `1/2`, already established in this graph and in KMS Appendix B. No contradiction. |
| Unique games on expanding constraint graphs (AKKSTV)? | That algorithm needs SDP value `1 - eta` with `eta << lambda`. At completeness `1/2`, `eta = 1/2` and the guarantee `1 - O((eta/lambda) log(lambda/eta))` is vacuous for every `lambda <= 1`. Also `Psi` blows each right vertex into `|S_(2k,k)|` twins with identical neighbourhoods, which does not improve expansion. No contradiction. |
| Entangled unique games (Kempe--Regev--Toner)? | KRT's algorithm separates entangled value `>= 1 - eps` from `<= delta` only when `6 eps + delta < 1`, i.e. near completeness 1. Neither audited claim asserts anything about entangled values, and the NO bound `val(Psi(U_o)) <= eps` is classical. No contradiction. |
| Does the same argument prove the Rich 2-to-1 Conjecture? | No: the completeness is `(1-eps)/2`, and consequence (b) is an iff that isolates the missing parameter rather than supplying it. |
| Is `Gap-Rich-2-to-1[(1-eps)/2, eps]` trivially in P, which would refute the claim under `P != NP`? | No. By `sd-rich-and-unique-games-sos-gaps-interconvert`, an algorithm on rich instances is an algorithm for `Gap-UG` at matched parameters, and `Gap-UG[(1-eps)/2, eps]` is NP-hard. |

---

## 6. Summary of findings

| id | defect | severity | effect on status |
|---|---|---|---|
| D1 | `orientation-lifts-sandwich-2to1-game-values` item (3): the claim node's wording of `w_v(L,b)` makes the stated identity false (counterexample in Section 1.6). The derivation file states the correct reading. Two informal sentences downstream ("loses exactly the minority branch mass") are wrong as written. | wording | none; item (3) is not used in any derivation |
| D2 | "For every `eps > 0`" should be "for every sufficiently small `eps`" (the promise is empty for `eps >= 1/3`). | cosmetic | none |
| D3 | BKM Definition 1.5 samples a **uniformly random** incident edge on a **regular** graph; the nodes assert a weighted reading without arguing it. The argument is easy (Section 2.1) and holds, because `sigma` is drawn independently of the edge. | unstated hypothesis | none; richness does hold in BKM's literal sense |
| D4 | `two-to-two-games-theorem-citation` verifies Definition 1.3, Theorem 1.4 and the abstract but not footnote 2, which is the sentence Step 1 consumes. Footnote 2 is quoted here and is faithfully paraphrased; the stronger anchor is DKKMS-1 Definition 1.2 + Theorem 1.2. | citation coverage | none; the import is correct |
| N1 | Novelty: `rich-2to1-hard-at-completeness-one-half` is a two-line composition of BKM's own `Gap-Unique[1/2, eps]` corollary with BKM Appendix B, at a better completeness. | novelty | none |
| **NEW** | Section 4: the generic per-constraint bipartization `2-to-2 -> 2-to-1` has value exactly `(1 + OPT)/2`, hence soundness above `1/2`; it can never deliver `Gap-2-to-1[1-eps, eps]`. | obstruction | kills one reading of KMS footnote 2 |

**Both audited claims keep ESTABLISHED.**
