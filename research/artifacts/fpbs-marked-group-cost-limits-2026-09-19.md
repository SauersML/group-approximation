# Bernoulli cost on the space of marked groups (swarm-0917-w19, 2026-09-19)

Written derivations for four graph nodes:

- `fpbs-bernoulli-cost-usc-on-marked-groups`
- `fpbs-bernoulli-cost-jumps-a-unit-along-fp-covers`
- `fpbs-cost-betti-fg-iff-fp-and-length-canonical-cost-lsc`
- `fpbs-cycle-tail-compactness-via-length-canonical-covers`

## 0. Setup

- `F = F(S)` is free on the finite set `S`, with `|S| = k`.
- A marked group is `G = F/N`. `G_n -> G` in `G_k` means that for every word `w`, eventually `w in N_n` iff `w in N`.
  Equivalently, for every `R`, eventually `N_n cap B_R = N cap B_R`, where `B_R` is the ball of radius `R` in `F`.
- `b_G` is the Bernoulli shift `G` acting on `([0,1]^G, Leb^G)` by `(g x)_h = x_(g^-1 h)`.
- `C(b_G)` is the cost of its orbit relation. For finite `G` this is `1 - 1/|G|`. For infinite `G` the shift is
  essentially free and `C(b_G) >= 1`.
- `beta_1(G)` is the first L2 Betti number.
- Imported facts:
  - (Gab-LB) Gaboriau: `C(b_G) >= 1 + beta_1(G)` for infinite `G`.
  - (Pichot) Pichot, Comment. Math. Helv. 81 (2006), 643-652: if `G_n -> G` in `G_k`, then
    `limsup beta_1(G_n) <= beta_1(G)`.
  - (Gab-AM) Gaboriau, Invent. Math. 139 (2000), IV.15 and IV.22. Take a free pmp action of `G1 *_A G2`, or of an
    HNN extension `B *_A`, with `A` infinite amenable. Then the cost is at most `C(G1) + C(G2) - 1`, respectively
    `C(B) + 1 - 1 = C(B)`, where each factor carries its restricted action. Free products (`A = 1`) are additive:
    `C(G1 * G2) = C(G1) + C(G2)`.
  - (Amen) Ornstein-Weiss: every free pmp action of an infinite amenable group has cost `1`.

## 1. Lemma A: Bernoulli cost is upper semicontinuous on marked groups

**Lemma A.** If `G_n -> G` in `G_k`, then `limsup_n C(b_(G_n)) <= C(b_G)`. This includes finite `G_n`, where the
cost is `1 - 1/|G_n|`.

**Certificates.** A certificate `Z` is the following finite data:

- a finite set `W` of words (the window);
- a finite partition `J` of `[0,1]` into intervals;
- finitely many pieces `(P_i, u_i)`, `i <= m`, where `u_i` is a word and `P_i` is a set of `J`-patterns on `W`;
- a radius `rho`.

For a marked group `G = F/N`, the certificate is realised on `b_G` as follows.

- `A_i(G) = {x : the J-pattern of (x_w)_(w in W) lies in P_i}`. Here `x_w` means the coordinate at the image of `w`.
  If two words of `W` have the same image, a pattern that gives them different cells is simply empty.
- `Phi_0(G)` is the graphing with pieces `x -> u_i x` on `A_i(G)`.
- `E_s(G)` is the set of `x` joined to `s x` by a `Phi_0(G)`-path of at most `rho` steps.
- `Phi_Z(G) = Phi_0(G)` together with the pieces `x -> s x` on the complement of `E_s(G)`, for `s in S`.

**Step 1: `Phi_Z(G)` generates `R_(b_G)`, and its cost is local.** Every point `x` is `Phi_Z`-joined to `s x` for
every `s`, so `Phi_Z(G)` generates. Its cost is

    c_Z(G) = sum_i mu(A_i(G)) + sum_s (1 - mu(E_s(G))).

Every set involved is a finite Boolean combination of two kinds of condition:

- conditions `x_v in I` with `I in J`, where `v = u^-1 w` for `w in W` and `u` a product of at most `rho` letters
  `u_i^(+-1)`;
- word identities `u = s` in `G`.

A path step `y -> u_i^(+-1) y` is allowed iff `y in A_i` (for the `+` direction) or `u_i^-1 y in A_i` (for the `-`
direction). With `y = u x`, this is a pattern condition on `x` at the coordinates `u^-1 W` or `u^-1 u_i W`.

Let `V` be the finite set of words appearing. Under `Leb^G`, the coordinates at distinct elements of `G` are
independent and uniform. So the measure of such a combination depends only on two things: the partition of `V` by
equality in `G`, and the truth values of the finitely many identities `u = s`. Both are decided by `N cap B_(R(Z))`,
where `R(Z) = 2 max_(v in V) |v| + 2`. Hence `c_Z(G) = c_Z(G')` whenever `N cap B_(R(Z)) = N' cap B_(R(Z))`.

**Step 2: certificates compute the cost.** Claim: `C(b_G) = inf_Z c_Z(G)`. The inequality `>=` is Step 1, since
every `Phi_Z(G)` is a generating graphing. For `<=`, fix `eps > 0` and a generating graphing `Psi` with cost below
`C(b_G) + eps`.

1. Each piece of `Psi` is a partial isomorphism inside the orbit relation. Split it by the first `g` in a fixed
   enumeration of `G` with `phi(x) = g x`. This writes `Psi` as a countable family of pieces `(B_j, g_j)` with the
   same total measure.
2. Almost every `x` is `Psi`-joined to `s x`. By countable additivity, choose `m` and `rho` such that for every `s`,
   the set `E_s^0` of `x` joined to `s x` in at most `rho` steps using only pieces `j <= m` has measure
   `> 1 - eps/k`.
3. Fix words `u_j` representing `g_j`. Let `D` be the set of products of at most `rho` letters `u_j^(+-1)`, for
   `j <= m`.
4. Cylinder sets are dense in the measure algebra of `Leb^G`. So choose cylinder sets `A_j`, `j <= m`, with a common
   finite window `W` and a common interval partition `J`, such that `mu(A_j Delta B_j) < delta`.
5. The set `E_s` built from the `A_j` differs from `E_s^0` only on `union_(d in D, j <= m) d^-1 (A_j Delta B_j)`.
   That set has measure at most `2 |D| m delta`.
6. The resulting certificate therefore has

       c_Z(G) <= C(b_G) + eps + m delta + k (eps/k + 2 |D| m delta).

   This is below `C(b_G) + 3 eps` once `delta` is small enough.

**Step 3: proof of Lemma A.** Given `eps > 0`, choose a certificate `Z` with `c_Z(G) < C(b_G) + eps`. For large `n`,
`N_n cap B_(R(Z)) = N cap B_(R(Z))`. By Steps 1 and 2 applied to `G_n`,

    C(b_(G_n)) <= c_Z(G_n) = c_Z(G) < C(b_G) + eps.

For finite `G_n` the cost of the orbit relation is `1 - 1/|G_n|`, and the same bound applies. QED.

**Remark.** This is the cost counterpart of Pichot's `beta_1` semicontinuity. It is probably folklore; the
derivation above is self-contained. The certificate also has finitely many pieces, so it is a bounded-degree
graphing. By Step 2, bounded-degree finite-window near-minimizers always exist.

## 2. Theorem B: a unit jump of Bernoulli cost along finitely presented covers

Notation: `x^y = y x y^-1` and `[x,y] = x y x^-1 y^-1`.

**The limit group.** Write `a_i = t^i a t^-i`. Baumslag's presentation is

    Z wr Z = < a, t | [a, a_k] (k >= 1) >.

Put

    H = (Z wr Z) * Z = < a, t, c | [a, a_k] (k >= 1) >,

marked by `(a, t, c)`.

- `beta_1(H) = 0 + 0 + 1 - 0 - 0 = 1` by the free product formula.
- `C(b_H) = 1 + 1 = 2` by (Gab-AM) additivity and (Amen). In fact `H` has fixed price `2`.

**The covers.** For `R >= 1` put

- `r_R = [a, a_(R+1)]`;
- `A_R = < a, t | [a, a_k] (1 <= k <= R) >`;
- `E_R = < a, t, c | [a, a_k] (1 <= k <= R), [r_R, c] >`.

**(B1) `E_R` is finitely presented and `E_R -> H` in `G_3`.** Every relator of `E_R` is trivial in `H`: `r_R` is
trivial in `Z wr Z`. So `E_R` surjects onto `H` preserving the marking, and `N_(E_R) <= N_H`. Conversely, any
`w in N_H` is a product of finitely many conjugates of relators `[a, a_k]` with `k <= K`. So `w in N_(E_R)` for
`R >= K`.

**(B2) `A_R` is an HNN extension.** Let `B = Z^(R+1) = < a_0, ..., a_R >`. Let `B_- = < a_0, ..., a_(R-1) >` and
`B_+ = < a_1, ..., a_R >`, and let `theta : B_- -> B_+` be `a_i -> a_(i+1)`.

The HNN group `B *_theta` has generators `a_0, ..., a_R, t` and relations

- `[a_i, a_j] = 1`;
- `t a_i t^-1 = a_(i+1)` for `i < R`.

Eliminating `a_i = t^i a_0 t^-i` turns `[a_i, a_j]` into `t^i [a_0, a_(j-i)] t^-i`. So the relation set is equivalent
to `[a_0, a_k]` for `1 <= k <= R`, and `B *_theta = A_R`.

**(B3) `r_R` has infinite order in `A_R`.** In `A_R`, `a_(R+1) = t a_R t^-1` with `a_R` not in `B_-`. So

    r_R = a_0 . t a_R t^-1 . a_0^-1 . t a_R^-1 t^-1.

Check for a Britton pinch at each place a `t` meets a `t^-1`:

- `t a_R^(+-1) t^-1` would need `a_R in B_-`. It is not.
- `t^-1 a_0^-1 t` would need `a_0 in B_+`. It is not.
- The cyclic junction `t^-1 . a_0 . t` would need `a_0 in B_+`. It is not.

So `r_R` is cyclically reduced of `t`-length `4`. By Britton's lemma every power `r_R^n` with `n != 0` is reduced of
`t`-length `4|n|`, hence nontrivial.

**(B4) Splitting of `E_R`.** Since `< r_R > = Z` in `A_R`,

    E_R = A_R *_(< r_R > = < r >) (< r > x < c >) = A_R *_Z Z^2.

**(B5) Cost and Betti number of `E_R`.**

- Take any free pmp action of `A_R`. Its restriction to `B` has cost `1` (Amen). The HNN bound of (Gab-AM) over the
  infinite amenable `B_-` then gives cost at most `1`.
- Now take the Bernoulli shift of `E_R`. Its restrictions to `A_R` and `Z^2` both have cost at most `1`. The amalgam
  bound of (Gab-AM) over the infinite amenable `Z` gives `C(b_(E_R)) <= 1 + 1 - 1 = 1`.
- `E_R` is infinite, so `C(b_(E_R)) = 1`.
- By (Gab-LB), `beta_1(E_R) = 0`. The same holds for `A_R`.

**Theorem B.** The finitely presented groups `E_R` converge to `H` in `G_3`. Along this sequence
`C(b_(E_R)) = 1` and `beta_1(E_R) = 0`, while `C(b_H) = 2` and `beta_1(H) = 1`. Every `E_R` satisfies the cost-Betti
equality, and so does `H`.

So Bernoulli cost and `beta_1` both jump up by exactly one unit in the limit. Neither is lower semicontinuous along
finitely presented covers. Lemma A and Pichot hold with strict inequality.

**What this rules out.** Consider any argument of the following form:

1. take finitely presented covers `G_n -> G` of a finitely generated group;
2. apply the cost-Betti equality to each `G_n`;
3. pass to the limit.

Step 3 needs `C(b_G) <= liminf C(b_(G_n))`. The sequence `E_R` shows this is false for general covers, even when the
cost-Betti equality holds at every term and at the limit. The same holds for any enumeration-dependent choice of
covers that is allowed to produce the `E_R`.

**Corollary B'.** Let `rho_R` be the largest `R'` with `N_(E_R) cap B_(R') = N_H cap B_(R')`, so `rho_R -> infinity`.
Every certificate `Z` in the sense of Section 1 with `c_Z(E_R) < 2` has `R(Z) > rho_R`. Otherwise `Z` would realise on
`b_H` with `c_Z(H) < 2 = C(b_H)`, contradicting Step 1.

So the fixed-price-one certificates of `E_R` necessarily read the defining relator `[r_R, c]`, a word of length about
`8R`. No cost bound built from windows of scale below `rho_R` can see that `E_R` has cost `1`.

## 3. Length-canonical covers and the decomposition

**Definition.** For `G = F/N`, put `G^_R = F / << N cap B_R >>`. This is a finitely presented marked group with
`G^_R -> G` in `G_k`: the two groups have the same trivial words of length at most `R`. It surjects onto `G`, so it is
infinite whenever `G` is. It depends only on `G` and the marking, not on any enumeration.

**(C0) The length-canonical covers of `H` do not jump.** Let `w` be a word in `a, t, c` of length at most `R` that is
trivial in `H = (Z wr Z) * Z`. By the normal form theorem, after free reduction some maximal syllable of `w` is
trivial in its factor.

- If it is a `c`-syllable, it is freely trivial.
- If it is an `(a,t)`-syllable, it is a subword of length at most `R` trivial in `Z wr Z`, so it lies in
  `N_(ZwrZ) cap B_R`.

Delete that syllable and induct. So `N_H cap B_R` lies in `<< N_(ZwrZ) cap B_R >>`, and

    H^_R = (Z wr Z)^_R * Z.

Hence `beta_1(H^_R) = beta_1((ZwrZ)^_R) + 1 >= 1`. Both free factors are infinite, so free-product additivity (Gab-AM) gives `C(b_(H^_R)) >= 1 + 1 = 2`. With Lemma A and
Pichot, both tend to their values at `H`. The jump of Theorem B comes from the relator `[r_R, c]`, which has length
about `8R` but is used at level `R`. Length-canonical covers never do that.

**Theorem C.** Consider the following statements.

- `T_fp`: `C(b_G) = 1 + beta_1(G)` for every infinite finitely presented `G`.
- `SEL_len(G)`: `C(b_G) <= liminf_R C(b_(G^_R))`. By Lemma A this is equivalent to `C(b_(G^_R)) -> C(b_G)`.
- `BA_len(G)`: `beta_1(G^_R) -> beta_1(G)`. By Pichot this is equivalent to `beta_1(G) <= liminf beta_1(G^_R)`.
- `CB`: `C(b_G) = 1 + beta_1(G)` for every infinite finitely generated `G`. By
  `fpbs-graphing-cost-betti-cycle-dimension-identity`, this is equivalent to `fpbs-bernoulli-cycle-tail-compactness`.

Then the following hold.

(i) `T_fp` and `SEL_len` for all infinite f.g. `G` together imply `CB`.

(ii) `CB` implies that `SEL_len(G)` and `BA_len(G)` are equivalent for every `G`.

(iii) Hence `CB` and `BA_len` (for all `G`) together are equivalent to `T_fp` and `SEL_len` (for all `G`).

*Proof.*

(i) Let `G` be infinite and finitely generated. Each `G^_R` is infinite and finitely presented. Then

    C(b_G) <= liminf_R C(b_(G^_R))            (SEL_len)
            = 1 + liminf_R beta_1(G^_R)        (T_fp)
           <= 1 + limsup_R beta_1(G^_R)
           <= 1 + beta_1(G)                    (Pichot).

The reverse inequality is (Gab-LB).

(ii) Under `CB`, `C(b_(G^_R)) = 1 + beta_1(G^_R)` and `C(b_G) = 1 + beta_1(G)`. So the two liminf inequalities are
the same statement.

(iii) For the forward direction, `CB` gives `T_fp`, and (ii) turns `BA_len` into `SEL_len`. For the converse, (i)
gives `CB`, and then (ii) gives `BA_len`. QED.

**Independence.** The three open inputs can each fail on their own.

- `T_fp` is the cost-Betti question restricted to finitely presented groups. Nothing here touches it.
- `SEL_len` is a statement about cost along one explicit sequence of covers. Theorem B shows the analogous statement
  for arbitrary covers is false.
- `BA_len` is a pure L2 statement with no cost content. By Theorem B it is false for arbitrary covers (`E_R -> H`).
  Its length-canonical form is untested.

Under `CB`, `BA_len(G)` and `SEL_len(G)` are the same statement. So a counterexample to `BA_len` at `G` is a
counterexample either to `CB` or to `SEL_len` at `G`.

**Why the moment method does not settle `BA_len` (heuristic, not used).** The spectral measure of the combinatorial Laplacian of the
2-complex of `G^_R` has moments `tr(Delta^m)` that agree with those of `G` only for `m` up to about `R / R_rel`.
Here `R_rel` is the length of the relator 2-cells, which is up to `R`. So the first `m` moments involve words of
length about `m R`, far beyond the agreement ball `B_R`. Pichot's semicontinuity only uses the monotone limit of
kernel projections, which gives the upper bound. The lower bound would need uniform control of the spectral measure
near `0` on 2-cells of unbounded length. I found no
argument for it.

## 4. Consequences for the cycle-tail programme

Route `fpbs-cycle-tail-compactness-via-length-canonical-covers`:

1. From `T_fp` and `SEL_len`, Theorem C(i) gives `C(b_G) = 1 + beta_1(G)`.
2. Section 1, Step 2 gives bounded-degree finite-window graphings `Phi_n` with `c(Phi_n) -> C(b_G)`.
3. The identity `c = 1 + beta_1 + z` then gives `z(Phi_n) -> 0`. Since `0 <= z - z_L <= z`, the tail vanishes.

What this kills:

- Any transfer of cost-Betti, or of fixed price, from finitely presented groups to finitely generated groups that uses
  lower semicontinuity of cost (or of `beta_1`) along an arbitrary sequence of finitely presented covers.
- The invariant that dies is the relator-length profile of the covers. In Theorem B the level-`R` cover uses a relator
  of length about `8R`, so its cheap certificate lives beyond the agreement radius (Corollary B'). The step where every
  such argument dies is Step 3, the passage to the limit.
- The same applies to Pichot-type arguments run in the lower direction.

What survives:

- The length-canonical covers, the only enumeration-free choice. For them the obstruction is absent in the example
  (C0).
- The open pure-L2 question `BA_len`.
