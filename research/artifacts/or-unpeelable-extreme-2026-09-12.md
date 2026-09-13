# Unpeelable Magnus extremes: basis invariance, descents, and the length-15 frontier

Lane `or-unpeelable-extreme`, 2026-09-12. Node
`unpeelable-extreme-one-relator-groups-sofic` (OPEN), route
`one-relator-sofic-via-torsion-free-two-generator-reduction`. Scripts are in
`research/artifacts/or-unpeelable-census-scripts-2026-09-12/` (`census.py`,
`census2.py`, `census3.py`, `malnormal.py`; run on MSI with python 3.11).

Nothing here closes the node. This artifact records one invariance lemma, three conditional
descents, a computer-certified census up to relator length 14, and the exact
first uncertified family.

## 0. Results

1. **Basis invariance (L1).** Fix a class `chi` in `H^1(G;Z)`. The top and bottom syllables of the
   Magnus rewriting do not depend on the zero-exponent basis: not their number, not their
   exponents, not their cyclic order. If `b_1(G) = 1`, the node's hypothesis can be
   checked in any one basis.
2. **Descents (L2-L4).** Three conditions each reduce soficity of `G` to soficity of a one-relator group
   with a strictly shorter relator: a common level gcd, cyclic coefficients at an
   extreme, and overlap rank one.
3. **Census theorem (computer-certified).** Every group `<a,t | w>` with
   `|w| <= 14` is sofic.
4. **First frontier.** At `|w| = 15` exactly 33 classes are uncertified. Up to
   symmetry, they are exactly the relators that are not partially positive and whose Magnus
   rewriting is `a_1^e a_0^(x_1) a_2^(x_2) a_0^(x_3) a_2^(x_4)`, with `e = +-1` and
   `{|x_1|,|x_3|} = {|x_2|,|x_4|} = {1,2}`. Three have partially positive
   automorphic images, which leaves 30. In all 33 the following hold:
   - `b_1 = 1`;
   - both extremes are unpeelable in every zero-exponent basis;
   - the Magnus piece `B_0 = F(x,y)` is free;
   - `F_- = <x,v>` and `F_+ = <v,y>` are proper malnormal subgroups of `B_0`, where
     `v = x^(x_1) y^(x_2) x^(x_3) y^(x_4)`.
5. **Known theorems.** None of the following applies to the 30:
   - torsion (Wise);
   - `pi(w) >= 3` (Linton);
   - free-by-cyclic with finitely generated fibre;
   - malnormal combination theorems;
   - amenable-edge permanence along the Magnus HNN extension;
   - L2-L4;
   - partial positivity within length `|w| + 4`.

## 1. Setting and certified leaves

Let `G = <a,t | w>`, where `w` is cyclically reduced and `t` has exponent sum zero. Put
`a_h = t^(-h) a t^h`. A cyclic permutation of `w` rewrites as a cyclic word
`W_0`: a cyclic sequence of syllables `(h_i, e_i)` with `e_i != 0` and
consecutive levels distinct. Let `m` and `n` be the lowest and highest levels,
and let `lambda_a` and `lambda_t` count the `a`- and `t`-letters of `w`, so that
`|W_0| = lambda_a`. Put `B_0 = <a_m,...,a_n | W_0>`, `F_- = <a_m,...,a_(n-1)>`
and `F_+ = <a_(m+1),...,a_n>`. The Freiheitssatz makes `F_-` and `F_+` free.
`G` is the HNN extension of `B_0` with `t^(-1) a_h t = a_(h+1)` identifying `F_-` with `F_+`. An extreme (the syllables at level
`n`, or at level `m`) is **peelable** if it is one syllable, or two syllables
of equal absolute exponent. Otherwise it is **unpeelable**.

A certificate is a finite tree whose leaves are established results:

| leaf | source | applies when |
|---|---|---|
| `Z`, `PRIMITIVE` | `G = Z` | `w` has length 1 or is primitive |
| `PEEL` | `peelable-extreme-one-relator-groups-are-sofic` | not a proper power, zero-exponent basis, a peelable extreme |
| `PP` | `partially-positive-one-relator-groups-are-sofic` | in some basis, a generator occurs with one sign only |
| `POWER` | Wise, *The Structure of Groups with a Quasiconvex Hierarchy* (2021), Thm 19.1 and Cor 19.2, as quoted in `one-relator-soficity-two-generator-equivalence-proof` | `w` is a proper power: virtually compact special, hence residually finite |

The internal nodes are the descents L2-L4 and group isomorphisms `w -> sigma(w)`,
`sigma in Aut(F_2)`: Nielsen moves to a zero-exponent basis, and Whitehead moves.

## 2. L1: basis invariance

**Lemma L1.** Let `(a,t)` and `(a',t')` be free bases of `F_2` in which `t`,
resp. `t'`, has exponent sum zero in `w` and which induce the same epimorphism
`chi : G -> Z` up to sign. Then the two Magnus rewritings have the same top and
bottom syllable data. This holds up to rotation, a global sign of the exponents, and exchange
of top with bottom. In particular one has a peelable extreme iff the other does.

*Proof.* Let `phi : F_2 -> Z` be `t -> 1, a -> 0`. After replacing `t'` by
`t'^(-1)`, which swaps top and bottom, the automorphism `sigma : a -> a', t -> t'`
satisfies `phi o sigma = phi`, and the relator in the new basis is `sigma^(-1)(w)`. On `H_1(F_2) = Z^2`,
`sigma` acts by the matrix `[[+-1, k], [0, 1]]`. The kernel of `Aut(F_2) -> GL_2(Z)` is `Inn(F_2)` (Nielsen).
So `sigma = c_g o tau`, with `tau(a) = a^(+-1)`, `tau(t) = t a^k` and `c_g` inner.
Now `c_g` rotates the cyclic word, and `a -> a^(-1)` negates all exponents. Put `t = t' a^(-k)`:
- a local maximum `t^(-1) a^e t` becomes `a^k t'^(-1) a^e t' a^(-k)`;
- a local minimum `t a^f t^(-1)` becomes `t' a^f t'^(-1)`;
- pass-through syllables become `a^(f+k)`, resp. `a^(f-k)`, at the same level;
- each interior letter of a `t`-run of length at least 2 adds a syllable `a^(-+k)` at a level strictly
  between the run's endpoints.

Syllables at levels strictly between `m` and `n` may appear, change or vanish. No `t'`-letter cancels:
each adjacent pair `t'^(-1) ... t'` or `t' ... t'^(-1)` encloses a local extremum `a^e` with `e != 0`.
So the heights are unchanged, and every local extremum keeps its exponent. Top and bottom
syllables are local extrema. QED

When `b_1(G) = 1`, `Hom(G,Z) = Z chi`, so every zero-exponent basis induces
`+-chi`. The node's hypothesis "for every basis" is then decided in one basis.

## 3. Descents

**L2 (level gcd).** Normalize so that `m = 0`, and suppose every level is divisible by `g >= 2`.
Then `w in F(a,s)` with `s = t^g`; write `w'` for `w` as a word in `a` and `s`. Then
`G = G_g *_(s = t^g) <t>` with `G_g = <a,s | w'>`, and `|w'| = lambda_a + lambda_t/g`. So `G` is sofic iff `G_g` is.

*Proof.* Every maximal `t`-run joins two `a`-syllables whose heights are multiples of `g`, so each run is `t^(jg)`.
Since `F(a,t) = F(a,s) *_(s=t^g) <t>` and `w` lies in a factor,
`G = <a,s | w'> *_(s=t^g) <t>`. The word `w'` involves `a`, so `s` has infinite order in `G_g`
(Freiheitssatz), and the amalgam is genuine. The amalgam is over `Z`, so it is sofic if `G_g` is
(amenable-edge permanence as used in `peelable-extreme-one-relator-groups-are-sofic`:
Elek-Szabo arXiv:1010.3424 Thm 1). Conversely, `G_g <= G`. QED

**L3 (cyclic coefficients at an extreme).** Write the cyclic word `W_0` as `y^(e_1) U_1 ... y^(e_r) U_r`
with `y = a_n` and `1 != U_i in F_-`. Suppose `U_i = c^(k_i)` for one `c in F_-`.
Put `P = y^(e_1) z^(k_1) ... y^(e_r) z^(k_r)` and `Q = <y,z | P>`. Then
`B_0 = F_- *_(c = z) Q`. This is an amenable envelope of `(B_0, F_-)` with one move
(`Y = F_-`, `E = <c>`, `X = Q`). So, by `amenable-envelope-magnus-piece-one-relator-sofic`,
`G` is sofic if `Q` is. Conversely `Q <= B_0 <= G`. Moreover
`|P| = sum |e_i| + sum |k_i| <= lambda_a < |w|`. The bottom extreme is symmetric, with `F_+`.

*Proof.* `F(a_m,...,a_n) = F_- * <y> = F_- *_(c=z) F(y,z)`, since `c` has
infinite order. After `z = c`, `W_0 = P` lies in the factor `F(y,z)`. So
`B_0 = F_- *_(c=z) F(y,z)/<<P>>`. `P` is cyclically reduced and involves `y`, so
`z` has infinite order in `Q`. QED

**L4 (overlap rank one).** After L2, suppose `n - m = g`. Then `G_g` is the HNN
extension of `B_0 = <a_m, a_n | W_0>` identifying `<a_m>` with `<a_n>`. Both are infinite cyclic
(Freiheitssatz). By amenable-edge HNN permanence (Ciobanu-Holt-Rees
arXiv:1212.2739 Prop 3.2), `G` is sofic iff `B_0` is, and `|W_0| = lambda_a < |w|`.

**Caveat on `magnus-staggered-chain-sofic`, Attempt 1.** That attempt calls the
sub-family `n - m <= 1` "already established". Its permanence argument needs
the vertex groups `B_i ≅ B_0` to be sofic. But `B_0 = <a_0, a_1 | W_0>` can be any
two-generator one-relator group: the cyclic reduction of `w = W(a, t^(-1) a t)` has Magnus piece
`W(a_0, a_1)` up to rotation. So soficity of `B_0` is an instance of the open question. The correct
statement on `n - m <= 1` is L4, a descent rather than a closure. This artifact does not edit that node.

## 4. Certificate search and soundness

`census.cert_word(w)` searches depth-first:
- Whitehead-minimize `w`; primitive gives leaf `PRIMITIVE`.
- Test `PP` before and after minimizing.
- Treat a proper power as a failure inside the recursion.
- Pass to a zero-exponent basis for the unique class `(q,-p)/gcd` when the exponent sums `(p,q)` are not
  both zero; otherwise try the classes with coordinates of absolute value at most 3.

`census.cert_seq` then tries `PEEL`, `PP`, `R1` (L2 and L4, recursing on
`W_0`) and `CYC-top`/`CYC-bot` (L3, recursing on `P`). Loops and blow-ups become **failures**, never successes. Three mechanisms do this: a depth cap of 8, a work
budget of 3000, and a memo of words in progress.

**Soundness.** Each internal step is an isomorphism or one of L2-L4, and each
implication "child sofic implies parent sofic" is proved in §3. Each leaf is an
established theorem. So a returned certificate proves soficity. The search is
incomplete: failure means only "not certified". No well-founded induction is
claimed. Basis changes lengthen relators, so minimal counterexamples are not
reachable by descent. Certificates are finite trees and need none.

## 5. Census

**Full census (`census3.py LMIN LMAX MAXPRINT`).** This covers every cyclically reduced `w` of length
`L`, up to rotation, reversal and the eight signed permutations of `{a,t}`.
All of these preserve the isomorphism type. Partially positive words are
skipped, since the `PP` node closes them. Each uncertified class then gets a breadth-first search over
Whitehead images of length `<= L + 4` (cap 20000 classes) for a partially
positive image.

| L | non-PP classes | PEEL | PEEL, b_1 = 2 | PP after moves | R1 g=1 | R1 g=2 | POWER | uncertified | after PP search |
|---|---|---|---|---|---|---|---|---|---|
| 4 | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| 5 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 6 | 5 | 3 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| 7 | 9 | 7 | 0 | 2 | 0 | 0 | 0 | 0 | 0 |
| 8 | 36 | 24 | 6 | 5 | 0 | 0 | 1 | 0 | 0 |
| 9 | 83 | 72 | 0 | 11 | 0 | 0 | 0 | 0 | 0 |
| 10 | 271 | 228 | 15 | 24 | 3 | 0 | 1 | 0 | 0 |
| 11 | 721 | 654 | 0 | 60 | 7 | 0 | 0 | 0 | 0 |
| 12 | 2192 | 1946 | 93 | 121 | 26 | 0 | 6 | 0 | 0 |
| 13 | 6139 | 5838 | 0 | 254 | 47 | 0 | 0 | 0 | 0 |
| 14 | 18079 | 16927 | 465 | 552 | 123 | 3 | 9 | 0 | 0 |
| 15 | 51616 | 50031 | 0 | 1315 | 229 | 7 | 1 | 33 | 30 |
| 16 | 150043 | 143393 | 3210 | 2658 | 495 | 21 | 36 | 230 | 211 |

Of the 230 uncertified classes at L = 16, 176 have an exponent sum equal to zero and 54 have both
exponent sums nonzero.

**Theorem (census).** Every two-generator one-relator group `<a,t | w>` with
`|w| <= 14` is sofic.

*Proof.* We may take `w` cyclically reduced and nonempty, since `G = F_2` otherwise. If no
generator occurs in `w` with exactly one sign, both generators occur with both signs, which takes
four letters. So every `w` with `|w| <= 3` is partially positive. For `4 <= L <= 14` the table
leaves no uncertified class. QED

**Magnus-sequence census (`census.py L`, `census2.py L 4 20000`).** These enumerate
exponent-sum-zero relators with both extremes unpeelable.

| L | classes | uncertified | after PP search | free piece (after PP search) | overlap rank (after PP search) |
|---|---|---|---|---|---|
| 14 | 140 | 0 | 0 | - | - |
| 15 | 290 | 33 | 30 | 30 | 2 |
| 16 | 788 | 176 | 163 | 44 | 2 |
| 17 | 2064 | 1043 | 1038 | 184 | 2 |
| 18 | 6016 | 3216 | 3196 | 332 | 2 (3170), 3 (26) |
| 19 | 17176 | 13174 | not run | not run | not run |
| 20 | 50651 | 35579 | not run | not run | not run |

Before the PP search the uncertified classes have 33, 48, 184 and 332 free pieces, and at L = 18
overlap ranks 2 (3190) and 3 (26). Extremes with three syllables first appear among the uncertified classes at L = 17 (31 classes with pattern `(1,1,1),(1,2)`).

## 6. The length-15 frontier

**Shape.** `census2.py 15 4 20000` reports that all 33 uncertified classes have the following properties:
- `g = 1` and overlap rank 2;
- two top and two bottom syllables, each pair with absolute exponents `{1,2}`;
- a middle letter occurring once.

Seven `a`-letters and eight `t`-letters then force the cyclic word
`a_1^e a_0^(x_1) a_2^(x_2) a_0^(x_3) a_2^(x_4)`, or its level reflection, with
`e = +-1` and `{|x_1|,|x_3|} = {|x_2|,|x_4|} = {1,2}`. Each uncertified class of `census3.py` has
this shape, after exchanging `a` and `t` if needed.

**Count.** The family has `2*2*8*8 = 256` sequences: the sign `e`, the arrangement
`0202` or `2020`, and the exponents. The symmetries act through the group of order 8
generated by three moves:
- `a -> a^(-1)`, which negates exponents;
- `t -> t^(-1)`, which reflects levels;
- reversal, which reverses the syllables and reflects levels.

Only the identity (256) and reversal (32) have fixed points. So there are `(256 + 32)/8 = 36` classes. The partially positive ones are those with
all exponents of one sign, and they form `(16 + 8)/8 = 3` classes. That leaves 33, matching the census count. So **the 33
uncertified classes are exactly the members of the family that are not partially positive.**

**Normal form.** Put `x = a_0`, `y = a_2` and `v = x^(x_1) y^(x_2) x^(x_3) y^(x_4)`. Then
`a_1 = v^(-e)`, `B_0 = F(x,y)`, `F_- = <x,v>`, `F_+ = <v,y>`, and

    G_v = <x, y, t | x^t = v^(-e),  (v^(-e))^t = y>,      x^t = t^(-1) x t.

For example, `AAttATATAttaaTT` rewrites as `a_0^(-2) a_(-2)^(-1) a_(-1)^(-1) a_0^(-1) a_(-2)^2`.
Shifted to levels 0..2 this gives `a_1 = a_2^(-1) a_0^2 a_2^(-2) a_0^(-1)`, and `H_1 = Z + Z/3`.
The scripts use the opposite convention `a_h = t^h a t^(-h)`, which reflects levels. Three classes have partially positive Whitehead images of length at most 19, for example
`AAttAATTAtatATT -> AttAttttAttAAtatA`, so they are sofic. `census3.py 15 15 MAXPRINT` prints the other 30 as `REST` lines.

**Properties of all 33.**
- `b_1 = 1`: the `a`-exponent sum `e + x_1 + x_2 + x_3 + x_4` is odd.
- Both extremes are unpeelable in every zero-exponent basis (L1).
- `F_-` and `F_+` are proper and malnormal in `B_0` (33 of 33). `malnormal.py 15 MAXPRINT` checks this by
  Stallings folding. Its criterion is that every off-diagonal component of the fibre product is a tree.
- `F_-` is not malnormal in `G_v`: `v^(-e) = a_1` lies in `F_- ∩ t^(-1) F_- t`,
  and `t ∉ F_-`.
- `ker chi` is not finitely generated. It is the directed union of the truncations
  `S_(N+1) = S_N *_F B_(N+1)`, and if it stabilized then `B_(N+1) = S_N ∩ B_(N+1) = F`, i.e. `F_- = B_0`.
  That is false: a basis containing `x` has the form `{x, x^i y^(+-1) x^j}`
  (Nielsen, as in L1), and `v` has three `y`-letters. Since `b_1 = 1`, no
  epimorphism `G_v -> Z` has a finitely generated kernel.

At L = 16, `malnormal.py 16 MAXPRINT` finds 128 uncertified classes with non-free pieces. The 48 with free
pieces again have proper malnormal `F_-` and `F_+` in `B_0`; 4 of them are partially positive and 44 remain.

## 7. Known theorems against the 30

| theorem | outcome |
|---|---|
| Wise: torsion implies virtually compact special | no: `w` is not a proper power |
| Linton: `pi(w) >= 3` implies virtually compact special | no: `w` is imprimitive in `F_2` itself, so `pi(w) <= 2` |
| free-by-cyclic with f.g. fibre, hence residually finite | no: `ker chi` is not f.g. and `b_1 = 1` |
| malnormal combination theorems (Hsu-Wise type) | hypothesis fails: `a_1 ∈ F_- ∩ F_+`, so the edge group is not malnormal in `G_v`; hyperbolicity is also unknown |
| amenable-edge permanence (Elek-Szabo, Collins-Dykema, Paunescu, CHR) | Magnus edge group is free of rank 2 |
| L2, L3, L4 | `g = 1`; top coefficients `a_0^(x_3)` and `a_1^e a_0^(x_1)` have no common root; overlap rank 2 |
| envelope wall of `amenable-envelope-magnus-piece-one-relator-sofic` | does not apply (`B_0` is free); see §8 |
| partial positivity, hence residually solvable | no image found within length 19 (cap 20000) |

## 8. Free Magnus pieces: the first nontrivial move of a relative splitting

**Lemma E.** Let `B = F(x,y)` and let `F_- <= B` be free of rank 2. Suppose `B`
splits nontrivially as a one-edge graph of groups, over a trivial or infinite cyclic edge
group, with `F_-` inside a vertex group `A`. Then the edge group is infinite
cyclic and `rank A = 2`. Either `B = A *_(<r^k>) <r>` with `k >= 2` (root
adjunction), or `B` is an HNN extension of `A` over `Z`. If `A = F_-` and `F_-` is malnormal
in `B`, neither case occurs.

*Proof.* Vertex groups are finitely generated free, and `chi(F_n) = 1 - n` is
additive over the graph of groups. `A` contains `F_2`, so `rank A >= 2`.
- Trivial edge: by Grushko the amalgam `A * B'` has `B' = 1`, and the HNN extension `A * Z` has
  `rank A = 1`. Both contradict nontriviality or `rank A >= 2`.
- Cyclic edge, amalgam: `(1 - rank A) + (1 - rank B') = -1`, so `B' = <r>` and `rank A = 2`. The edge
  group is `<r^k>`, and `k >= 2` because the splitting is nontrivial.
- Cyclic edge, HNN: `1 - rank A = -1`.

If `A = F_-` is malnormal: `r^k in A ∩ r A r^(-1)` with `r ∉ A`, resp. `c in A`
and `s^(-1) c s in A` for the stable letter `s ∉ A`. Either contradicts malnormality. QED

**Consequence for envelopes.** Amenable subgroups of `F_2` are trivial or infinite cyclic. Let
`B_0 -> B'` be an amenable envelope of `(B_0, F_-)` as in
`amenable-envelope-magnus-piece-one-relator-sofic`, built by moves
`F_- = V_0 <= V_1 <= ... <= V_k = B'`. Let `j` be least with `B_0 <= V_j`; then `j >= 1`, since
`F_- != B_0`.
- `B_0` acts on the Bass-Serre tree of the move `V_(j-1) -> V_j`, and `F_-` fixes the vertex `V_(j-1)`.
- If `B_0` fixed a vertex `u != V_(j-1)`, then `F_-` would fix an edge and lie in an amenable edge
  stabilizer, which is impossible. If `u = V_(j-1)`, then `B_0 <= V_(j-1)`, contradicting the choice of `j`.
- So `B_0` has no global fixed point, its edge stabilizers are amenable, and `F_-` is elliptic.
- `B_0` is finitely generated, so it has a minimal invariant subtree. Collapsing all but one edge orbit
  gives a nontrivial one-edge splitting as in Lemma E.

For the 30, `F_-` is malnormal in `B_0`, so the vertex group `A` containing `F_-` satisfies
`F_- ⊊ A ⊊ B_0` and `rank A = 2`. A proper finite-index subgroup of a rank-2 free group has rank at
least 3, so `F_-` has infinite index in `A`. The same holds for `F_+`. This does not exclude an
envelope. It says where one must start: at an infinite cyclic splitting of `F(x,y)` whose rank-2
vertex group properly contains `F_-`.

## 9. What remains open

- `unpeelable-extreme-one-relator-groups-sofic` and `one-relator-groups-sofic`.
- The 30 groups `G_v` at length 15. Each is an HNN extension of `F(x,y)` identifying the proper malnormal rank-2 subgroups
  `F_- = <x,v>` and `F_+ = <v,y>` by `x -> v^(-e)`, `v^(-e) -> y`, with `F_- ∩ F_+ != 1`. A proof for them needs either
  a cyclic splitting of `F(x,y)` with vertex group `F_- ⊊ A`, or an argument over non-amenable edges.
- At L = 16: 211 classes remain after the PP search. Non-free pieces appear, and so do exponent-sum-nonzero
  survivors. Overlap rank 3 appears at L = 18.
