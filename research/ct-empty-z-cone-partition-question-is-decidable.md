---
rg: 2
id: ct-empty-z-cone-partition-question-is-decidable
kind: claim
title: "Kourovka 21.74(a) in the one-prime host: for g in CT_∅(Z) ≅ V it is decidable whether g permutes a nontrivial partition of Z into residue classes with 2-power moduli; each flow component of the north-south dynamics lies in one class, so YES partitions use only prefix cones of finitely many computable cones, plus a torsion part that always splits"
distinct_from:
  ct-z-invariant-residue-partitions-are-not-conjugacy-invariant: that proves YES is r.e., holds at finite order and is not conjugacy-invariant (also in V); this decides the 2-power form of YES in V.
  ct-z-residue-partitions-cannot-carve-thin-invariant-sets: that is the carving lemma (indecomposable sets lie in one class); this applies it to the finitely many flow components of a V-element and turns it into a finite search.
  ct-z-residue-partition-certificates-live-on-s-adic-coordinates: that reduces certificates to the S-adic coordinates for any g in CT(Z); this solves the S-adic problem completely when S = {2}.
---

**ESTABLISHED** (lane proof; **Referee PASS** bh-ref-q11 2026-09-19 for the stated sub-case, with one precision). No priority claimed.
- **Scope.** The *2-power form* of Kourovka 21.74(a)(S. Kohl) for elements of `CT_∅(Z) ≅ V`.
  Equivalently: does `g ∈ V` permute a partition of the Cantor set into at least two cones?
- **Not covered.** Partitions using odd moduli, for the same `g` (see "What remains").
- **Imports, read at source.**
  - M. Gilabert Vio, arXiv:2412.08784v3, Corollary 2.4. It is built on Goffer–Lederle, Lemma 2.17
    (revealing pairs exist), and Salazar-Díaz.
  - Bleak–Bowman–Gordon–Graham–Hughes–Matucci–Sapir, arXiv:1107.0672, §4.1: revealing pairs,
    Lemmas 4.1–4.4, and the remark, after Brin §10.7, that revealing pairs can be found by an
    algorithm.

## Setting

- **The Cantor set.** `CT_∅(Z)` acts on `Ẑ_∅ = Z_2 = {0,1}^N` (2-adic digits, least significant
  first). The class `r(2^a)` is the cone of the `a`-digit word of `r`.
- **YES₂.** `g` permutes a partition of `Z` into at least two classes with 2-power moduli iff `ĝ`
  permutes the corresponding partition of `Z_2` into cones, since `Z` is dense. This is the
  convention of `ct-z-invariant-residue-partitions-are-not-conjugacy-invariant`.

**Decomposition** (Gilabert Vio, Cor. 2.4). There are `g`-invariant clopen sets
`Z_2 = U ⊔ V` with the following properties.
- **(U)** Some power of `g|_U` is an isometry. In `V` this power permutes the cones of `U` of a
  large fixed depth canonically, so `g|_U` has finite order.
- **(V)** `V` contains finitely many `g`-periodic points `Per = Per_rep ⊔ Per_att`.
  - For every `ε > 0` there is `N` with `g^k(V ∖ Per_rep^ε) ⊆ Per_att^ε` and
    `g^(−k)(V ∖ Per_att^ε) ⊆ Per_rep^ε` for all `k ≥ N`.
  - Each point of `Per_att` (resp. `Per_rep`) has a cone `∂T_u` that some power `g^n` contracts
    into itself (resp. whose image under it contains `∂T_u`), with a unique fixed point.

All of this is read off a revealing tree pair, and a revealing pair is found by enumerating tree
pairs for `g` and testing the (finite) revealing condition. The search terminates because a
revealing pair exists.

## Flow components

Let `M` be a common period of `Per`. Then `g^M` fixes every point of `Per`.
- **Limits.** By (V), every `x ∈ V ∖ Per` has a single `g^M`-limit `ω(x) ∈ Per_att` and a single
  `g^(−M)`-limit `α(x) ∈ Per_rep`. Indeed, once `g^(Mk)x` is in a contracting cone it stays there
  and converges.
- **The flow graph.** Its vertices are `Per`, and `α(x)` is joined to `ω(x)` for every `x`. Let
  `R_1, …, R_s` be the unions, over the components of this graph, of the points whose limits lie in
  that component, together with the component's periodic points.

**Lemma A.** The `R_j` are clopen, and they partition `V`. Each `R_j` is `g^M`-invariant, and for
every `t ≥ 1` its only `g^(Mt)`-invariant clopen subsets are `∅` and `R_j`.

*Proof.*
- **Open.** A basin `B(a) = {x : ω(x) = a}` is open, since it is a union of preimages of the
  contracting cone of `a`. A repeller `r` has a cone whose points, other than `r`, have
  `α = r`, so their `ω` lies in `r`'s component. So each `R_j` is open.
- **Clopen.** The `R_j` are finitely many disjoint open sets covering `V`, hence clopen.
- **Indecomposable.** Let `W ⊆ R_j` be clopen, nonempty and `g^(Mt)`-invariant, and take
  `x ∈ W`.
  - Some subsequence of `g^(Mtk)x` tends to `ω(x)`, and `W` is closed, so `ω(x) ∈ W`. Likewise
    `α(x) ∈ W`.
  - If an attractor `a` lies in `W`, then `W` contains a neighbourhood of `a`. Every `y ∈ B(a)`
    eventually enters it, so `y ∈ W` by invariance. The same holds backwards for repellers.
  - By connectivity of the component, `W = R_j`. ∎

**Computability.** `U`, `V`, `Per` and `M` come from the revealing pair. For each repeller `r`,
take the clopen fundamental domain `D_r = (cone of r) ∖ g^(−M)(cone of r)`. Iterate until
`g^(Mk)(D_r)` lies in the union of the attractor cones; (V) guarantees this happens. The cones that
the image meets are `r`'s neighbours. Growing the finite unions `⋃_{k ≤ K} g^(−Mk)(attractor cones)`
until they cover `V` gives each `R_j` as an explicit finite union of cones. Let `u_j` be the
longest common prefix of `R_j`, so that `[u_j]` is the smallest cone containing `R_j`.

## Theorem

`g` is YES₂ iff there is a family `𝒞` of pairwise disjoint cones, each of the form `[w]` with `w` a
prefix of some `u_j`, such that:
1. every `R_j` lies in a member of `𝒞`, and every member contains some `R_j`;
2. `g` maps every member of `𝒞` onto a member of `𝒞`;
3. `Q = Z_2 ∖ ⋃𝒞` is nonempty, or `|𝒞| ≥ 2`.

The candidate cones are finitely many, and images of cones under `g` are computable. **So YES₂ is
decidable for every `g ∈ CT_∅(Z)`.** If `V = ∅`, then `g` has finite order and is YES₂ (Theorem 2
of the non-conjugacy node).

## Proof

**⇒.** Let `g` permute the cone partition `𝒫`, and put `𝒞 = {C ∈ 𝒫 : C ∩ V ≠ ∅}`.
- By Lemma A and the carving lemma (`ct-z-residue-partitions-cannot-carve-thin-invariant-sets`,
  item 1, applied to `g^(M·|𝒫|!)`), each `R_j` lies in exactly one part.
- So every member of `𝒞` contains some `R_j`, hence contains `[u_j]`. A cone containing `[u_j]` is
  `[w]` for a prefix `w` of `u_j`. This gives 1.
- `g(V) = V`, so `g` permutes `𝒞`. This gives 2.
- If `Q = ∅`, then `𝒞 = 𝒫` has at least two members. This gives 3.

**⇐.**
- By 2, `g` permutes `𝒞`, since disjoint members have disjoint images. So `Q` is clopen and
  `g`-invariant, and by 1 it lies in `U`, where `g` has finite order `N`.
- Choose `d` so that `Q` is a union of depth-`d` cones and every `g^i` (`i < N`) is canonical on
  each of them.
- The common refinement of the partitions `g^i(depth-d cones of Q)` (`i < N`) consists of
  intersections of cones, which are cones. `g` permutes it, as in Theorem 2 of the non-conjugacy
  node.
- Together with `𝒞`, it is a permuted cone partition, with at least two parts by 3. ∎

## Checks against known cases

- **ψ** (`ct-z-north-south-element-has-no-finite-cycles`). One flow component, whose hull is all of
  `Z_2`. So the only candidate is `𝒞 = {Z_2}`, and the answer is NO, as proved there.
- **`h = ψ_{0(2)}ψ_{1(2)}`.** Two components, with hulls `[0]` and `[1]`. `𝒞 = {[0], [1]}` works:
  YES.
- **`g = chc`** (Theorem 5 of the non-conjugacy node). The components meet both `0(4)` and `1(4)`,
  i.e. the words `00` and `10`, so every `u_j` is empty. The only candidate is `Z_2`, `Q = ∅`, and
  the answer is NO, matching that theorem.

## What remains

- **Odd moduli for `g ∈ CT_∅(Z)`.** The literal 21.74(a) allows partitions with odd moduli.
  - By Theorem 2 of `ct-z-residue-partition-certificates-live-on-s-adic-coordinates`, such a
    partition splits at an odd prime `ℓ` only where the `K`-step blocks of `g` are trivial mod `ℓ`.
  - For a part whose 2-adic ball is all of `Z_2`, this means `g^K` acts as the identity mod `ℓ` on
    `Z`, which can happen (slopes in `4^Z`, translations `≡ 0 mod 3`).
  - Deciding this fibre case is open. Its necessary condition, "some `g^K ≡ id mod ℓ`", is
    explicit.
- **Two primes.** Open, and this is where 21.74(b),(c) are already undecidable.

## Lesson for general BH

**The coordinate layer of 21.74(a) is decidable where the dynamics has finitely many
indecomposable pieces with computable cone hulls.**
- With one prime, North–South dynamics supplies exactly this, and the hulls bound every
  admissible partition.
- The same one-base/two-base line then governs orbits (20.44), torsion and box structure.

**For host design.** Box-level structure is decided by the coarse component structure. That is
tame on one base, and in multi-base hosts it can hide Collatz-type or machine complexity.

## Referee (bh-ref-q11, 2026-09-19): PASS for the stated sub-case; one precision

**Against the source.** Kourovka Notebook, arXiv:1401.0300v46, 21st issue. Verbatim: "21.74. Is it algorithmically decidable whether a given element g ∈ CT(Z) (a) permutes a nontrivial partition of Z into residue classes? (b) has only finite cycles? (c) has no finite cycles? S. Kohl".
- The printed (a) allows every `g ∈ CT(Z)` and residue classes of any modulus.
- The node proves the sub-case with `g ∈ CT_∅(Z)` (17.60, `P = ∅`; `≅ V` by Kohl, J. Group Theory 20 (2017), Remark 1.4) and 2-power moduli.
- Title and Scope say exactly this. So 21.74(a) itself stays open, even for `g ∈ CT_∅(Z)`, because odd moduli are not covered.

**Checked.**
- **Lemma A.** Basins are unions of preimages of contracting cones. Repelling cones contain no other periodic point, since `g^(−nk)p = p` forces `p = r`. So the `R_j` are open, finitely many, disjoint and cover `V`, hence clopen.
- **Indecomposability.** `ω(x), α(x) ∈ W`, then whole basins lie in `W`, then connectivity.
- **⇒.** Lemma A with `t = |𝒫|!` already gives "each `R_j` lies in one part"; the carving lemma is not needed. A cone containing `R_j` is `[w]` with `w` a prefix of `u_j`.
- **⇐.** `Q ⊆ U` is `g`-invariant with `g|_Q` of finite order. The common refinement of the `g^i(depth-d cones of Q)` consists of cones and is permuted, and there are at least 2 parts by condition 3.
- **Consistency.** The three calibration cases (ψ, `h`, `chc`) agree with the nodes they cite.

**The finiteness bound.** Each member of `𝒞` contains some `R_j`, and each `R_j` lies in exactly one member. So `|𝒞| ≤ s`.
- The candidates are the `≤ Σ_j (|u_j| + 1)` prefix cones, hence at most `2^(Σ_j(|u_j|+1))` families.
- Conditions 1–3 are finite checks on explicit finite unions of cones, since images of cones under `g ∈ V` are computable.
- The revealing-pair search terminates because a revealing pair exists (BBGGHMS §4.1, after Brin).
- So the search is finite and effective.

**Precision (computability paragraph).** Repellers never enter the attractor cones, so the unions `⋃_{k≤K} g^(−Mk)(attractor cones)` never cover `V`.
- Cover `V` by those unions **together with the repelling cones**, which compactness allows for some `K`.
- Assign each piece to the component of its attractor or repeller.
- The `R_j`, and so the `u_j`, are then explicit.
