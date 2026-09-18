---
rg: 2
id: rips-segev-three-copy-no-zero-divisors-proof
kind: route
title: Coefficientwise, P_T Q_T' = P_T' Q_T is a rank-one tensor identity whenever the port supports of T and T' add injectively, so P_T is a multiple of Q_T and u = c w; this bounds clean active cosets by one per copy for every number of copies, and with the pairwise gluing lemma three copies have at most 12 active cosets, whose port cycle is a positive relation too short to hold in K
target: rips-segev-three-copy-configurations-carry-no-zero-divisors
requires: [rips-segev-two-copy-configurations-carry-no-zero-divisors, rips-segev-one-copy-configurations-carry-no-zero-divisors]
---

**Conventions.**
- [TC] is `rips-segev-two-copy-configurations-carry-no-zero-divisors-proof`, [OC] is
  `rips-segev-one-copy-configurations-carry-no-zero-divisors-proof`, [EE] is
  `rips-segev-witness-supports-carry-no-zero-divisors-proof`, [LG] is
  `rips-segev-core-large-gap-two-layer-elements-are-regular-proof`, and [FL] is
  `rips-segev-steenbock-few-line-a-supports-are-regular-proof`.
- Notation is that of [TC]: `F = <a> * <b>`, `K = F/<<R>>`, `Gr'_*(1/8)`, `gamma >= 42` ([FL]), copies
  `C = h g(Gamma)` with vertex sets `V_C`, distinguished positions `D_i = {0, I_1, I_2, O_1, O_2, C_i}` of line `i`,
  `In_i = {0, I_1, I_2, C_i}` and `Out_i = {0, O_1, O_2, C_i}`.
- For `alpha (u + w b) = 0` put `X = alpha u` and `Y = alpha w`, so `X(z b) = - Y(z)`.  For a left `<a>`-coset `T`
  with base point `z_T`, write `alpha_T = z_T f_T(a)`, `P_T = f_T u` and `Q_T = f_T w`.  Then
  `X(z_T a^p) = P_T(p)` and `Y(z_T a^p) = Q_T(p)`.  `T` is *active* if `f_T != 0`.
- The *port support* of `T` is `S_T = supp P_T ∪ supp Q_T`, a finite subset of `Z`.  Changing the base point
  translates `S_T` and multiplies `P_T`, `Q_T` by one monomial.

## 1. The rank-one lemma

**Lemma 1.**  Let `H` be a group, `a, b in H` of infinite order, with `k[<a>]` identified with `k[t^{±1}]`.  Let
`alpha in k[H]`, `u, w in k[<a>]`, with `alpha != 0`, `w != 0` and `alpha (u + w b) = 0`.  Then for any two active
cosets `T != T'`,
`(S_T - S_T) ∩ (S_T' - S_T') != {0}`.

*Proof.*  Suppose the intersection is `{0}`.
- *Nonvanishing.*  For active `T`, `Q_T = f_T w != 0` because `k[t^{±1}]` is a domain.  If `u = 0`, then
  `Y b = - X = 0`, so `Y = 0`.  But `Y = sum_T z_T f_T w` has nonzero pieces in distinct cosets, so this is
  impossible.  Hence `P_T = f_T u != 0` too.
- *Injectivity.*  If `x + y = x' + y'` with `x, x' in S_T` and `y, y' in S_T'`, then `x - x' = y' - y` lies in both
  difference sets.  So it is `0`, and `(x, y) = (x', y')`.  Thus `(x, y) -> x + y` is injective on `S_T × S_T'`.
- *Tensor identity.*  `P_T Q_T' = f_T f_T' u w = P_T' Q_T`.  All four factors are supported in `S_T` or `S_T'`.
  By injectivity, the coefficient of `t^{x+y}` on each side is a single product:
  `P_T(x) Q_T'(y) = Q_T(x) P_T'(y)` for all `x in S_T`, `y in S_T'`.
- *Rank one.*  Pick `y_0` with `Q_T'(y_0) != 0` and put `c = P_T'(y_0)/Q_T'(y_0)`.  Then `P_T = c Q_T`, so
  `f_T u = c f_T w`, and `u = c w` since `f_T != 0`.
- *Conclusion.*  Now `alpha (u + w b) = (alpha w)(c + b) = Y (c + b)`, so `Y b = - c Y`.  Thus
  `supp(Y) b = supp(Y)` is a finite nonempty set stable under right multiplication by `b`.  Since `b` has infinite
  order, this is impossible. ∎

**Corollary 2 (row-separated pairs).**  In the setting of [TC], let `T`, `T'` be active cosets whose port
supports lie in `D_i` and in `D_j` respectively, with `i != j` (in any copies, with their own base points).
Then `alpha = 0`.

*Proof.*  `phi` is injective, so `r_i != r_j`.  Say `r_i < r_j`.
- Every nonzero element of `D_j - D_j` has absolute value at least `min Dist_j^+ = 10^{5 r_j - 4}`.
- Every element of `D_i - D_i` has absolute value at most `C_i = 10^{5 r_i} <= 10^{5 r_j - 5}`.
- So the two difference sets meet only in `0`, and Lemma 1 applies. ∎

**Re-proof of [OC].**  In one copy, [OC] Lemma 2 puts the port support of line `i` in `D_i`, and [OC] Lemma 3
gives two distinct active lines.  Corollary 2 finishes, with no need for [OC] Lemma 6 or [OC] §4.

## 2. `N` copies: the clean cosets

Let `alpha in k[K]`, `alpha != 0`, `u, w in k[<a>]`, `w != 0`, with `alpha (u + w b) = 0` and
`supp X ∪ supp Y ⊆ V_1 ∪ ... ∪ V_N` for pairwise distinct copies `C_1, ..., C_N`.  As in [TC] §6:
- a *bridge* is a `b`-edge `z -> z b` with `z, z b in V_1 ∪ ... ∪ V_N` that is an edge of no copy;
- a coset is *dirty* if it meets two of the `V_m` or contains a bridge endpoint, and *clean* otherwise.

**Lemma 3 (ports).**
- (a) If `Y(z) != 0`, then `z -> z b` is an edge of some `C_m` or a bridge.  If `X(z) != 0`, the same holds for
  `z b^{-1} -> z`.
- (b) A bridge `z -> z b` has `z in V_m \ V_m'` and `z b in V_m' \ V_m` for some `m != m'`.  So it is a bridge for
  the pair `{C_m, C_m'}` in the sense of [TC] Corollary 2, and each pair of copies has at most one.
- (c) A clean active coset `T` meets exactly one copy `C_m`, in one line `i`.  With base point `h_m g(v_{i,0})` it
  has `supp Q_T ⊆ Out_i` and `supp P_T ⊆ In_i`, so `S_T ⊆ D_i`.

*Proof.*
- (a) This is [TC] Lemma 4: if `z, z b` lie in one `V_m`, [EE] 1(a)-(b) make `z -> z b` an edge of `C_m`.
- (b) If `z in V_m'` as well, then `z, z b in V_m'` and the edge lies in `C_m'`, by the proof of (a).  The same
  applies to `z b in V_m`.  [TC] Corollary 2 is a statement about one pair of copies, so it applies to
  `{C_m, C_m'}`.
- (c) `T` meets `supp Y ⊆ ∪ V_m`, and a clean coset meets only one `V_m`.  By [OC] §1, translated by `h_m`, the
  intersection is one line.  Let `Y(z) != 0` with `z in T`.  By (a), `z -> z b` is not a bridge (as `T` is clean),
  so it is an edge of a copy containing `z`, which is `C_m`.  Hence the position of `z` lies in `Out_i`.  The case
  of `X` is symmetric. ∎

**Proposition 4 (clean cosets, every `N`).**
- (i) Two clean active cosets have the same line index.  In particular, a copy has at most one clean active
  coset.
- (ii) Every port neighbour of a clean active coset is dirty.  Here a *port neighbour* of `T` is the coset of `z b`
  for `z in supp Q_T`, or of `z b^{-1}` for `z in supp P_T`.

*Proof.*
- (i) By Lemma 3(c) their port supports lie in `D_i` and `D_j` for their line indices.  If `i != j`, Corollary 2
  gives a contradiction.  Two distinct cosets meeting one copy meet it in distinct lines, which have distinct
  indices.
- (ii) Let `T` be clean active in `C_m`, on line `i`, and `z in supp Q_T`.  By Lemma 3(c), `z -> z b` is the edge
  of `C_m` from `v_{i,p}` to some `v_{k,p'}`, and `k != i` because `Phi` has no loops ([FL] Lemma A(c)).
  - The coset `T_k` of `z b` meets `C_m` in line `k`, and it is active because `X(z b) = - Y(z) != 0`.
  - If `T_k` were clean, it would be a second clean active coset of `C_m`, against (i).
  - The case `z in supp P_T` is the same with the edge into `z`. ∎

**Remark.**  Proposition 4(i) replaces [TC] Lemma 5 and the whole flank analysis of [TC] §3 and §6.  In
particular the *mixed-flank* configuration of [TC] §6 never has to be examined.  Two clean active lines in one
copy are already contradictory by the coefficient tensors alone, before any flanking line is looked at.

## 3. The dirty cosets and the port cycle

**Lemma 5 (dirty count).**  At most `3 N(N-1)/2` cosets are dirty.

*Proof.*  Every dirty coset meets two copies or contains a bridge endpoint.  Fix a pair `{C_m, C_m'}`.
- If the pair has a bridge, [TC] Corollary 2 says that no coset meets both copies and that the bridge is the only
  one.  So the pair contributes at most the 2 cosets of the bridge endpoints.
- Otherwise the cosets meeting both copies number at most 3 ([TC] Corollary 3), and the pair has no bridge.
- By Lemma 3(b), every bridge is the bridge of one pair.  Summing over pairs gives the bound. ∎

**Lemma 6 (port cycle).**  If at most `A` cosets are active, then `K` satisfies a relation
`W = b a^{n_0} b a^{n_1} ... b a^{n_{L-1}} = 1` with `1 <= L <= A`.  Its cyclic reduction is nontrivial in `F`
and has free-product length at most `2L`.

*Proof.*  This is the conclusion of [TC] §4.
- Every active `T` has some `z in supp Q_T`, and the coset of `z b` is active since `X(z b) = - Y(z) != 0`.
- So the digraph on active cosets with an edge `T -> T'` whenever such a `z` has `z b in T'` has all out-degrees
  at least 1.  It therefore has a directed cycle through `L <= A` distinct cosets.
- Witnesses `z_j in supp Q_{T_j}` with `z_j b in T_{j+1}` give `z_j b a^{n_j} = z_{j+1}`, indices mod `L`.
  Hence `W = 1` in `K`.
- The `b`-exponent sum of `W` is `L != 0`.  So `W` and its cyclic reduction are nontrivial in `F`, and cyclic
  reduction does not increase the syllable count `2L`. ∎

**Lemma 7 ([TC] Lemma 6).**  A cyclically reduced `W != 1` of `F` with `W = 1` in `K` has
`|W|_* > 5 gamma/8 - 1`.  For `gamma >= 42` this is `> 25.25`.

## 4. The three-copy theorem

**Theorem.**  For `N <= 3` there is no such configuration.  Equivalently, if `alpha (u + w b) = 0` with
`alpha, w != 0`, then `supp(alpha u) ∪ supp(alpha w)` lies in no union of three copies.

*Proof.*  Let `N = 3`; smaller `N` are special cases, by repeating a copy or by [TC].
- Every active coset meets `supp Y ⊆ V_1 ∪ V_2 ∪ V_3`, so it is clean or dirty.
- By Proposition 4(i) there are at most 3 clean active cosets, and by Lemma 5 at most 9 dirty ones.
- So at most 12 cosets are active.  Lemma 6 then gives a nontrivial cyclically reduced relation of free-product
  length `<= 24`.  But Lemma 7 requires length `> 25.25`, a contradiction. ∎

**In `k[G]`.**  The reduction of [TC] §4 ("In `k[G]`") applies verbatim.
- Split `alpha` over left `K`-cosets `sK`.  Each piece `alpha_s` satisfies `alpha_s (u + w b) = 0`, since
  `u + w b in k[K]`.
- Its supports lie in the union of the copies `h_m g(V) ⊆ h_m K` with `h_m K = sK`.
- Translate by `s^{-1}`: this is a configuration in `K` with at most 3 copies.

**Large girth, every `N`.**  For `N` copies, Proposition 4(i) and Lemma 5 bound the active cosets by
`N + 3N(N-1)/2`.  So the cycle of Lemma 6 has length at most `3N^2 - N`.
- Hence the `N`-copy theorem holds whenever `3 N^2 - N <= 5 gamma/8 - 1`.
- For Steenbock-type graphs over `Phi` of girth `g` we have `gamma >= g`, so `g >= (8/5)(3N^2 - N + 1)` suffices.
  Examples are `g >= 72` for `N = 4` and `g >= 112` for `N = 5`.
- Every fixed `N` is covered for large girth, but no single graph is covered for all `N`.

## 5. Toward `N >= 4`: the shell lemma

For `N >= 4` both counts above grow with `N`.  The following lemma is the Greendlinger-type step suggested in
[TC] §6.  It treats the copy of a shell face of the port cycle as a new copy `C_M`, which need not belong to the
covering `C_1, ..., C_N`.

Fix a directed cycle of the port digraph (Lemma 6), with cosets `T_j`, witnesses `z_j` and
`z_j b a^{n_j} = z_{j+1}`.  Let `pi` be the closed path in the Cayley graph of `K` that runs from `z_j` along the
`b`-edge to `z_j b`, and then along `a^{n_j}` inside `T_{j+1}` to `z_{j+1}`.  Its label `W` is a positive word in
`b`.  Its cyclic reduction `W'` only merges `b`'s where `n_j = 0`.  Take a minimal van Kampen diagram `D` for
`W'` in the standing reading of [LG] Lemma 3, whose faces lift to reduced cycles of `Gamma`.

**Lemma 8 (shell arc).**  There are a copy `C_M` and 11 pairwise distinct active cosets `U_1, ..., U_11` on the
cycle with the following property.  Each `U_t` meets `C_M` in a line `l_t`, the lines `l_t` are pairwise distinct,
and `U_t` has an arrival port `y_t` (`X(y_t) != 0`) at a position in `In_{l_t}` and a departure port `x_t`
(`Y(x_t) != 0`) at a position in `Out_{l_t}`.  Here positions are taken in `C_M`-coordinates.  The port edges at
`y_t` and `x_t` are edges of `C_M`.

*Proof.*
- *The face.*  By the proof of Lemma 7, `D` has a face `M` with a connected exterior arc `s` and
  `|omega(s)|_* > 5 gamma/8 >= 26.25`.  So `s` has at least 27 syllables.
  - The face `M` lifts to a reduced cycle `c_M` of `Gamma`, read from some vertex `v`.  If its start maps to `x`
    in the Cayley graph, then the image of `∂M` is `h_M g(c_M)`, with `h_M = x g(v)^{-1}`.  This is because `g`
    carries every labelled edge of `Gamma` to the corresponding edge of the Cayley graph ([EE] 1(a)).
  - Put `C_M = h_M g(Gamma)`.  The part of `pi` read along `s` is `h_M g(c_s)` for a backtrack-free subpath
    `c_s` of `c_M`.
- *The syllables.*  The normal form of `omega(s)` is a run of syllables of `W'` cut at both ends.  So at least 25
  consecutive syllables of `s` are full syllables of `W'`, alternating between `a`- and `b`-syllables.  They
  contain 12 consecutive `b`-syllables `beta_1, ..., beta_12` and the 11 `a`-syllables `a^{n_j} (n_j != 0)`
  between them.
- *The cosets.*  The `a`-syllable between `beta_t` and `beta_{t+1}` is the segment of `pi` inside one coset
  `U_t = T_{j+1}`, from `y_t = z_j b` to `x_t = z_{j+1}`.
  - The last `b`-edge of `beta_t` is the port edge `z_j -> z_j b`, and the first `b`-edge of `beta_{t+1}` is
    `z_{j+1} -> z_{j+1} b`.  Both are images of `b`-edges of `c_s`, hence edges of `C_M`.
  - The segment is the image of an `a`-segment of `c_s`, which lies on one line `l_t` of `Gamma`.  Its start is
    the target of a `b`-edge and its end is the source of one, which gives the positions `In` and `Out`.
  - `X(y_t) = - Y(z_j) != 0` and `Y(x_t) != 0` by the choice of witnesses.
- *Distinctness.*  The subpath of `c_s` from `beta_1` to `beta_12` has at most 24 `b`-edges.  Its projection is a
  non-backtracking walk in `Phi` ([FL] Lemma B) of length `<= 24 < 42 <= girth(Phi)`.  By [FL] Lemma C its vertices
  are pairwise distinct, and the lines `l_t` are vertices of it visited at different times.  Distinct lines of one
  copy lie in distinct cosets ([OC] §1), so the `U_t` are distinct. ∎

Call `U_t` *pure* if `S_{U_t} ⊆ D_{l_t}` in `C_M`-coordinates (base point `h_M g(v_{l_t,0})`), and *impure*
otherwise.

**Lemma 9 (shell lemma).**  At most one `U_t` is pure.  Every impure `U_t` carries a *link* between `C_M` and
some covering copy `C_m != C_M`.  A link here means one of two things: `U_t` meets `V_m`, or `U_t` contains the
`C_M`-endpoint of a bridge of the pair `{C_M, C_m}` in the sense of [TC] Corollary 2.  A single `C_m` carries
links in at most 3 of the `U_t`.  Hence at least 4 covering copies differ from `C_M`.

*Proof.*
- *Pure.*  Two pure `U_t`, `U_t'` have port supports in `D_{l_t}` and `D_{l_t'}` with `l_t != l_t'`.  Corollary 2
  gives a contradiction.
- *Impure.*  Take a port `z in U_t` outside `h_M g(v_{l_t, D_{l_t}})`, say `Y(z) != 0`; the case `X(z) != 0` is
  the same with `z b^{-1}`.  Both `z` and `z b` lie in the covering.
  - If `z notin V_M`, then `z in V_m` for a covering copy `C_m != C_M`, and `U_t` meets `V_m`.
  - If `z in V_M`, then `z` lies on `l_t` ([OC] §1) at a position outside `D_{l_t}`.  So no `b`-edge of `C_M`
    leaves `z`, and by [EE] 1(a)-(b) `z b notin V_M`.  Let `z b in V_m`, so `C_m != C_M`.  Either `z in V_m`, and
    `U_t` meets `V_m`.  Or `z in V_M \ V_m` and `z b in V_m \ V_M`, and `z -> z b` is a bridge of `{C_M, C_m}`.
- *At most 3 per copy.*  If `{C_M, C_m}` has a bridge, [TC] Corollary 2 makes it the only link.  Its
  `C_M`-endpoint lies in one coset.  Otherwise at most 3 cosets meet both copies ([TC] Corollary 3).
- *Count.*  At least 10 of the 11 cosets are impure, and 3 copies carry links in at most 9 of them. ∎

**Corollary 10 (`N = 4`).**  Suppose a counterexample lies in 4 copies.  Then for every directed port cycle and
every shell face `M` as in Lemma 8:
- (a) `C_M` is not one of the 4 covering copies;
- (b) each of the 11 cosets `U_t` is dirty for the covering.

*Proof.*
- (a) If `C_M` is a covering copy, only 3 covering copies differ from it, against Lemma 9.
- (b) Suppose `U_t` is clean for the covering, meeting only `C_m`.  By Lemma 3(a) the port edges at `y_t` and
  `x_t` are not bridges, so they are edges of `C_m`.  Then `y_t` and `x_t` lie on one line of `C_m` ([OC] §1).
  - So the word `b a^{n_j} b` with `n_j != 0` labels a path of `C_m` and a path of `C_M`, both starting at `z_j`.
  - By rigidity ([TC] Conventions) it labels at most one path of `Gamma`.  So both paths are images of one path
    starting at a vertex `v`, and `h_m g(v) = z_j = h_M g(v)`.
  - Hence `C_m = C_M`, against (a). ∎

**Large girth, linear in `N`.**  For graphs over `Phi` of girth `g`, with `gamma >= g`, the same argument gives
the following.  Put `m_0 = floor(5 gamma/8) + 1` and `B = min(floor((m_0 - 2)/2), floor((g - 1)/2))`.
- The shell arc then has `B - 1` distinct cosets, at least `B - 2` of them impure.  So the `N`-copy theorem holds
  whenever `3N < B - 2`.
- Since `B` is about `5g/16`, this is `N` up to about `5g/48`, against about `sqrt(5g/24)` for the count of §4.
- For `g = 42` it gives `N <= 3` again.

## 6. What remains, and why counting cannot finish

- *Exact residue for `N = 4`.*  After Corollary 10, a four-copy counterexample needs every shell copy of every
  port cycle to lie outside the covering.  Every such shell then passes through 11 consecutive cosets that are
  dirty for the covering.  By Lemma 5 the covering has at most 18 dirty cosets, so this is not yet contradictory.
- *Why counting stops.*  The shell lemma charges impure cosets to other copies at a rate of at most 3 per copy.
  The count of §4 charges all active cosets.  Both bounds grow with `N`.
  - Geometry alone does not bound the number of copies a port cycle crosses.  Every edge of the Cayley graph lies
    in some copy, so a relator cycle of `K` is covered by at most `|cycle|` copies, pairwise linked along it.
  - So an argument that only counts copies and links, and ignores coefficients away from one pair of cosets,
    cannot handle every `N` for a fixed `Gamma`.
- *The natural next statement.*  This is an **extremal-copy lemma**: among the copies of a minimal covering, some
  copy meets the union of the others in at most 3 links.  This is an analogue of the free faces of finite
  subcomplexes of `C'(1/6)` complexes.
  - In such a copy, Proposition 4 leaves at most one clean active coset.  Every port edge of `C_M` then runs
    between the at most 9 link cosets and that coset.
  - The rank-one lemma, applied to these cosets and the port edges they send outside, is the candidate for
    removing the copy from the covering.  This would give an induction on `N`.
- *Where the coefficients enter.*  Lemma 1 is the only coefficient input used here.  It needs one pair of active
  cosets with disjoint nonzero difference sets.  The dirty cosets of a counterexample must therefore pairwise
  share differences of their port supports, and the extremal-copy step will have to use that.

## 7. Checks

- *Rank-one lemma on the controls of [OC] and [TC].*  In the degenerate control of [OC] §4 (all lines on
  positions `0..5`), the difference sets of any two lines coincide.  So Lemma 1 does not apply, which matches the
  nullity-1 solution found there.
- *With separated rows.*  Corollary 2 applies to every pair of distinct lines, which matches the zero nullity of
  [OC] §5 and the 0 consistent systems of [TC] §5 on every separated two-copy model.
- *No flank lemma.*  The count in §4 uses only Proposition 4(i) and the pairwise gluing lemmas of [TC] §1.  So the
  three-copy theorem does not depend on any statement about mixed flanks.
