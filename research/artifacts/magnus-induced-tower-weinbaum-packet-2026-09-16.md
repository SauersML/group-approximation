# 2026-09-16: induced Magnus towers and the Weinbaum packet

Written for [[one-relator-weinbaum-packet-amenably-visible]]. This artifact
gives a construction of amenable, locally indicable quotients of a
two-generator one-relator group from one *window* group attached to its Magnus
piece. The window is induced along the staggered chain and then collapsed by
the shift. Every proper subword of the relator is detected inside the window,
so the quotient retains the whole Weinbaum packet. The quotient need not be
solvable, and in the Baumslag--Gersten case it is not, because its kernel over
`Z` is perfect.

Results proved here:

* **Theorem A (tower transfer).** A split window `P = L x| Phi` satisfying the
  relator, the shift-matching condition and retention of the proper subwords
  of the Magnus rewriting gives a packet-retaining amenable locally indicable
  quotient. Hence the group is sofic.
* **Lemma 4 (packet correspondence).** Every `t`-exponent-zero proper subword
  of `w` is conjugate, by a power of `t`, to a proper nonempty contiguous
  subword of the cyclic Magnus rewriting `W_0`. The converse fails.
* **Theorem B (rank-one lifting).** Suppose the overlap rank is one and `W_0`
  has zero exponent sum in `a_1` (or in `a_0`). Then packet visibility of the
  Magnus piece `B_0` implies packet visibility of `G`.
* **Theorem C (bottom-linear wreath towers).** Suppose `W_0` lies in the
  normal closure of `a_0` and its Fox polynomial meets at least two
  top-degrees. Then Theorem A applies with `Phi` an iterated wreath product of
  copies of `Z`. Retention is then a test inside one solvable group.
* **Theorem D (Baumslag--Gersten calibration).** `BG` has an elementary
  amenable, locally indicable, nonsolvable quotient retaining its whole Weinbaum
  packet.
* **Proposition E.** Every elementary amenable torsion-free image of `BG` in
  which `a` survives has infinite Hirsch length.

Nothing here resolves the universal claim. Section 9 records exactly where the
mechanism stops.

## 1. Conventions

Let `F = F(a,t)`, and let `w` be cyclically reduced, involving both `a` and
`t`, with `t`-exponent sum zero. Put `a_i = t^(-i) a t^i`. Walk once around
`w` from a base point. An `a`-letter `a^eps` whose prefix has `t`-exponent
`E` is recorded as the indexed letter `a_(-E)^eps`.

Reading the indexed letters in order gives a cyclic word `W` in the `a_i`.
Moving the base point conjugates `w` by a power of `t` and shifts every index
by the same constant, so we normalize the minimum index to `0`. The maximum
index `r >= 1` is the *overlap rank*, and both `a_0` and `a_r` occur. We write
`W_0(a_0,...,a_r)` for this cyclic word.

Because the total `t`-exponent of `w` is zero, telescoping gives, in `F`,

    w = prod_j t^(E_j) a^(eps_j) t^(-E_j) = W_0(a_0,...,a_r)

up to conjugation by a power of `t`. Here `E_j` is the prefix exponent of the
`j`-th `a`-letter. The Magnus piece is `B_0 = <a_0,...,a_r | W_0>`, with
Magnus subgroups `F_- = <a_0,...,a_(r-1)>` and `F_+ = <a_1,...,a_r>`, which
are free by the Freiheitssatz.

`W_0` is cyclically reduced. Two cyclically consecutive `a`-letters of `w` are
separated by a reduced block `t^k`, and their indices differ by `k`. Equal
indices therefore force `k=0`, so the letters are adjacent in `w` and cannot
cancel. Conversely, the cyclic indexed word `W_0` determines `w` up to
rotation, because the block between letters of indices `i`, `i'` is
`t^(i-i')`. Hence `W_0` is a proper power iff `w` is.

The **Weinbaum packet** `S(w)` of `G_m = F/<<w^m>>` for the splitting
`F = <a> * <t>` is the set of elements represented by proper nonempty
contiguous subwords of the cyclic letter spelling of `w`. This is the packet
of [[proper-subword-amenable-visibility-criterion]].

Similarly, the packet of `B_0` for the splitting `<a_0> * <a_1>` (when `r=1`)
is the set of proper nonempty contiguous subwords of the cyclic word `W_0`.

A **marked group** is a group with a chosen generating tuple. A marked
homomorphism sends chosen generators to chosen generators. Two marked
homomorphisms with the same source and target coincide.

## 2. Induced groups

Let `S` be a group, `Phi <= S`, and `L` a group on which `Phi` acts by
automorphisms `x -> phi.x`. Define `Ind_Phi^S L` as the group, under pointwise
product, of functions `f : S -> L` satisfying:

* `f(s phi) = phi^(-1).f(s)` for all `s in S`, `phi in Phi`;
* `f` is trivial outside finitely many cosets `s Phi`.

`S` acts by `(sigma.f)(s) = f(sigma^(-1) s)`, and this preserves both
conditions. Put `E = Ind_Phi^S L x| S`.

**Lemma 2.1 (identity coset).** Define `iota(x)(phi) = phi^(-1).x` for
`phi in Phi`, and `iota(x)(s) = 1` for `s notin Phi`. Then:

* `iota : L -> Ind_Phi^S L` is an injective homomorphism;
* `sigma.iota(x) = iota(sigma.x)` for `sigma in Phi`;
* `x phi -> iota(x) phi` is an injective homomorphism `L x| Phi -> E`.

*Proof.* For `s in Phi`, `iota(x)(s phi) = phi^(-1).(s^(-1).x)`, so
`iota(x)` lies in the induced group. It is multiplicative because each `phi.`
is an automorphism, and it is injective because `iota(x)(1) = x`.

For `sigma in Phi`, `(sigma.iota(x))(s) = iota(x)(sigma^(-1)s)` is supported
on `Phi`, with value `s^(-1).(sigma.x) = iota(sigma.x)(s)`. Hence `iota(L)`
is a `Phi`-invariant copy of `L` with the given action, and the last assertion
follows. `QED`

**Lemma 2.2 (restriction).** If `Phi <= U <= S`, the functions supported in
`U` form a `U`-invariant subgroup equal to `Ind_Phi^U L`. Extension by `1`
therefore gives an injective homomorphism
`Ind_Phi^U L x| U -> Ind_Phi^S L x| S`. It is the identity on `U` and
compatible with the two maps `iota`.

*Proof.* If `supp f` is contained in `U` and `sigma in U`, then
`supp(sigma.f) = sigma supp f` is contained in `U`. The rest is immediate.
`QED`

**Lemma 2.3 (permanence).** If `L` and `S` are both amenable, then so is `E`.
The same holds for elementary amenable, and for locally indicable.

*Proof.* Choosing a transversal, the functions supported on finitely many
cosets form subgroups isomorphic to finite direct products `L^k`. So the
induced group is a directed union of finite products of copies of `L`.

All three classes are closed under finite direct products, directed unions and
extensions. For local indicability, let `Gamma` be a finitely generated
nontrivial subgroup of an extension `K -> E -> Q`.

* If `Gamma` has nontrivial image in `Q`, that image maps onto `Z`.
* Otherwise `Gamma <= K`.

Finite products work in the same way, using a coordinate projection. Directed
unions are local. `QED`

**Lemma 2.4 (generation).** Suppose `L` is generated by the `Phi`-orbit of one
element `ell`. Then `E` is generated by `iota(ell)` together with `S`.

*Proof.* `iota(L)` is generated by the `Phi`-translates of `iota(ell)`, by
Lemma 2.1. A function supported on one coset `s Phi` equals
`s.iota(x)` for `x = f(s)`. Every element of the induced group is a finite
product of such functions. `QED`

## 3. Theorem A (tower transfer)

Fix `w` as in Section 1, with overlap rank `r >= 1` and Magnus rewriting
`W_0(a_0,...,a_r)`.

A **window** for `w` consists of the following data:

* an amenable locally indicable group `P = L x| Phi`;
* a marked subgroup `Phi = <phi_1,...,phi_r>`;
* an element `ell in L`.

The data must satisfy three conditions.

* **(T1)** `W_0(ell, phi_1, ..., phi_r) = 1` in `P`.
* **(T2)** There is an isomorphism `mu : Phi -> <ell, phi_1, ..., phi_(r-1)>`
  with `mu(phi_1) = ell` and `mu(phi_(i+1)) = phi_i` for `1 <= i < r`.
* **(T3)** `U(ell, phi_1, ..., phi_r) != 1` for every proper nonempty
  contiguous subword `U` of the cyclic word `W_0`.

For `r = 1`, (T2) says only that `ell` and `phi_1` have the same order. Since
`P` is torsion-free, this means both are trivial or both are nontrivial.

Replacing `L` by the subgroup generated by the `Phi`-orbit of `ell` changes
none of (T1)--(T3) and keeps `P` amenable and locally indicable. We assume this
from now on.

**Theorem A.** Let `(P, Phi, ell)` be a window satisfying (T1) and (T2). Then
there are:

* a group `H = N x| <tau>` that is amenable and locally indicable, and
  elementary amenable when `P` is;
* a homomorphism `pi : G_m -> H` for every `m >= 1`, with `pi(a) = a_0 in N`
  and `pi(t) = tau`.

The subgroup `<pi(a_0), ..., pi(a_r)>` is the image of a marked embedding of
`<ell, phi_1, ..., phi_r>`. If (T3) also holds, then `pi` is nontrivial on
every element of the Weinbaum packet `S(w)`. Hence `G_m` is sofic by
[[proper-subword-amenable-visibility-criterion]].

*Proof.*

**Windows.** For integers `p <= q` with `q - p >= r - 1`, we define a marked
group `S_[p,q]` with generators `a_p, ..., a_q`, by induction on `q - p`. At
the same time we prove:

> **(M)** For every `i` with `p <= i <= q - r + 1`, the map
> `phi_j -> a_(i+j-1)` extends to an isomorphism
> `Phi -> <a_i, ..., a_(i+r-1)>`.

*Base case `q - p = r - 1`.* Put `S_[p,q] = Phi`, with `a_(p+j-1) = phi_j`.
Then (M) is tautological.

*Step `q - p >= r`.* `S_[p+1,q]` is already defined and satisfies (M). Let
`Phi_p = <a_(p+1), ..., a_(p+r)>`. By (M) for `i = p+1`, `Phi_p` is identified
with `Phi` via `phi_j -> a_(p+j)`. Hence `Phi_p` acts on `L`. Put

    S_[p,q] = Ind_(Phi_p)^(S_[p+1,q]) L  x|  S_[p+1,q],     a_p = iota(ell),

and keep `a_(p+1), ..., a_q` in the complement.

By Lemma 2.4, `S_[p,q]` is generated by `a_p, ..., a_q`. By Lemma 2.1, the map
`x phi -> iota(x) phi` embeds `P` into `S_[p,q]`. This embedding sends `ell` to
`a_p` and `phi_j` to `a_(p+j)`.

Now check (M) for `S_[p,q]`. For `i >= p+1` it holds inside the complement
`S_[p+1,q]`. For `i = p`, the embedding carries `<ell, phi_1, ..., phi_(r-1)>`
onto `<a_p, ..., a_(p+r-1)>`, marked. Composing with `mu` from (T2) gives
`phi_1 -> a_p` and `phi_(j+1) -> a_(p+j)`, which is (M) for `i = p`.

**Relations.** In `S_[p,q]`, `W_0(a_i, ..., a_(i+r)) = 1` whenever
`p <= i <= q - r`.

* For `i = p`, this is (T1) transported by the embedding of `P`.
* For `i > p`, it holds in the complement by induction.
* In the base case there is no such `i`.

Moreover `S_[0,r]` is `P` itself, and `a_0 = ell`, `a_j = phi_j`. Here
`Phi_0 = S_[1,r]`, and `Ind_Phi^Phi L = iota(L)`.

**Marked maps.** There are three kinds of marked maps between windows.

* `rho : S_[p+1,q] -> S_[p,q]` is the inclusion of the complement. It is
  injective.
* `sigma : S_[p,q] -> S_[p+1,q+1]` shifts every index by one. The two groups
  are built by the same recipe from the same data, so `sigma` is an
  isomorphism.
* `lambda : S_[p,q-1] -> S_[p,q]` is defined for `q - 1 - p >= r - 1`. It is
  marked and injective, and we prove this by induction on `q - p`.
  * If `q - p = r`, then `S_[p,q-1] = Phi` and `S_[p,q] = P`. The map is
    `(T2)`, that is, `mu` followed by the inclusion of
    `<ell, phi_1, ..., phi_(r-1)>`.
  * If `q - p >= r + 1`, induction gives a marked embedding
    `lambda' : S_[p+1,q-1] -> S_[p+1,q]`. Its image `U` contains `Phi_p`,
    because `p + r <= q - 1`. `lambda'` respects the identifications of
    `Phi_p` with `Phi`, because these are marked. Transporting along
    `lambda'` and then applying Lemma 2.2 to `Phi_p <= U <= S_[p+1,q]` gives
    a marked embedding `S_[p,q-1] -> S_[p,q]`. It sends `iota(ell)` to
    `iota(ell)`.

All three kinds are marked homomorphisms between groups generated by their
marked generators. So any two composites with the same source and target
coincide, and every square built from `rho`, `lambda`, `sigma` commutes.

**Colimit.** The intervals `[p,q]` with `q - p >= r - 1` form a directed set
under inclusion. The unique marked composite of `rho`s and `lambda`s gives
injective structure maps. Let `N` be the directed colimit. It contains every
`S_[p,q]` as a subgroup and is generated by the images of `a_i`, `i in Z`.
Every finite set of generators lies in one window, so:

* `W_0(a_i, ..., a_(i+r)) = 1` for every `i in Z`;
* `<a_i, ..., a_(i+r-1)>` is marked isomorphic to `Phi` for every `i`;
* `<a_i, ..., a_(i+r)>` is marked isomorphic to `<ell, phi_1, ..., phi_r>` for
  every `i`.

The shifts `sigma` commute with the structure maps. They therefore induce an
automorphism `theta` of `N` with `theta(a_i) = a_(i+1)`, whose inverse comes
from `sigma^(-1)`. Let `H = N x| <tau>` with `tau^(-1) x tau = theta(x)`.

**The map.** Define `pi(a) = a_0` and `pi(t) = tau`. Then
`pi(t^(-i) a t^i) = a_i`. By Section 1, `pi(w)` is conjugate by a power of
`tau` to `W_0(a_0, ..., a_r) = 1`. So `pi` factors through
`F/<<w>>`, and hence through every `G_m`.

**Permanence.** Every subgroup of `P` is amenable and locally indicable, and
elementary amenable when `P` is. So `L` and `Phi` are. By Lemma 2.3 and
induction, every window is. `N` is a directed union of windows, and `H` is an
extension of `N` by `Z`. Hence `H` inherits all three properties.

**Retention.** Let `u` be a proper nonempty contiguous subword of the cyclic
spelling of `w`.

* If the `t`-exponent of `u` is nonzero, then `pi(u)` maps to a nonzero
  element of `H/N = Z`.
* Otherwise Lemma 4 below gives `pi(u) = theta^c(U(a_0, ..., a_r))` for some
  integer `c` and some proper nonempty contiguous subword `U` of the cyclic
  word `W_0`. Now `U(a_0, ..., a_r) = U(ell, phi) != 1` in `S_[0,r] = P` by
  (T3), `P` embeds in `N`, and `theta` is an automorphism. So `pi(u) != 1`.

`QED`

## 4. Lemma 4 (packet correspondence)

**Lemma 4.** Let `u` be a proper nonempty contiguous subword of the cyclic
spelling of `w` with `t`-exponent zero. Let `U` be the word formed by the
indexed `a`-letters of `u`, read in order, with the indices of Section 1. Then:

* `U` is a proper nonempty contiguous subword of the cyclic word `W_0`;
* in `F`, `u = t^(e) U(a_0, ..., a_r) t^(-e)` for some integer `e`, where
  `a_i = t^(-i) a t^i`.

*Proof.* Write `u = t^(k_0) a^(eps_1) t^(k_1) ... a^(eps_s) t^(k_s)`, where
`sum k_j = 0`. Put `D_j = k_0 + ... + k_(j-1)`. Telescoping gives

    u = prod_j t^(D_j) a^(eps_j) t^(-D_j).

If `u` begins at a point of the cyclic word where the prefix exponent is `D`,
the `j`-th `a`-letter of `u` has index `-(D + D_j)`. After the normalizing
shift `c_0` of Section 1, it becomes `a_(-(D+D_j)+c_0)`. Hence
`u = t^(e) U t^(-e)` with `e = D - c_0`.

`U` consists of consecutive `a`-letters of the cyclic word, so it is a
contiguous subword of cyclic `W_0`.

* **`U` is nonempty.** Otherwise `u = t^(k_0)` with `k_0 = 0`, so `u` would be
  empty.
* **`U` is proper.** Write the cyclic word `w` as the concatenation of `u` and
  a complementary nonempty arc `u'`. The arc `u'` also has `t`-exponent zero.
  By the previous point, `u'` contains an `a`-letter, and `U` omits it.

`QED`

*Remarks.*

1. **(T3) implies retention of the `t`-exponent-zero part of `S(w)`.** The
   `t`-exponent-nonzero part is detected by `H -> Z`.
2. **(T3) is stronger than needed.** Only the words `U` arising from Lemma 4
   matter, and not every arc of `W_0` arises.
   * Take `w = a a t^(-1) a a t a^(-1) t^(-1) a^(-1) t`. Then
     `W_0 = a_0^2 a_1^2 a_0^(-1) a_1^(-1)`.
   * The arc `a_0 a_1` sits in `w` as `a t^(-1) a`. The letters before and
     after it have the same indices as its ends, so no `t`-exponent-zero
     subword of `w` produces it.
   * So the converse of Lemma 4 is false. Everything below uses (T3) as
     stated, which is sufficient.

## 5. Rank one, and the truncation obstruction

Write `e_j(V)` for the exponent sum of `a_j` in a word `V`.

**Theorem B (rank-one lifting).** Let `r = 1`, so `W_0 = W_0(a_0, a_1)`, and
assume `e_1(W_0) = 0`. Let `B_0 = <a_0, a_1 | W_0>`. Suppose there is a
homomorphism `beta : B_0 -> Q` to an amenable locally indicable group that is
nontrivial on every proper nonempty contiguous subword of the cyclic word
`W_0`. Then for every `m >= 1` there is a homomorphism from `G_m` to an
amenable locally indicable group that is nontrivial on all of `S(w)`. The
target is elementary amenable when `Q` is.

The same holds when `e_0(W_0) = 0`.

`B_0` lies in the scope of [[one-relator-weinbaum-packet-amenably-visible]].

* `F(a_0, a_1) = <a_0> * <a_1>`.
* `W_0` is cyclically reduced, by Section 1.
* `W_0` has syllable length at least two, because both letters occur.
* `W_0` is not a proper power when `w` is not.
* `|W_0| <= |w| - 2`, because `w` contains at least two `t`-letters.

So Theorem B reduces the packet question for `G` to the packet question for a
strictly shorter relator, under the exponent hypothesis.

*Proof.* Let `c : F(a_0, a_1) -> Z` be the `a_1`-exponent sum. Put
`beta' = (beta, c) : F(a_0, a_1) -> Q x Z`. Then `beta'(W_0) = 1`, because
`c(W_0) = e_1(W_0) = 0`. Let `P = beta'(F(a_0, a_1))`; it is amenable, locally
indicable, and elementary amenable when `Q` is.

Let `L = P intersect (Q x {0})`, and let `phi_1 = beta'(a_1)`. Since
`c(a_1) = 1`, the projection `P -> Z` is split by `<phi_1>`. So
`P = L x| Phi` with `Phi = <phi_1> = Z`. Put
`ell = beta'(a_0) = (beta(a_0), 0) in L`.

* **(T1)** `W_0(ell, phi_1) = beta'(W_0) = 1`.
* **(T3)** For a proper arc `U` of cyclic `W_0`,
  `U(ell, phi_1) = (beta(U), c(U))`, and `beta(U) != 1` by hypothesis.
* **(T2)** `a_0` is a proper arc, because `|W_0| >= 2`. So `ell != 1`, and
  `ell` has infinite order since `Q` is torsion-free. Also `phi_1` has
  infinite order. Hence `phi_1 -> ell` is an isomorphism `Phi -> <ell>`.

Theorem A applies.

For `e_0(W_0) = 0`, apply the automorphism `t -> t^(-1)` of `F(a,t)`. It
carries `w` to a relator `w'`, maps `S(w)` bijectively onto `S(w')`, and
induces an isomorphism `G_m -> F/<<w'^m>>`. The Magnus rewriting of `w'` is
`W_0` with `a_0` and `a_1` exchanged, so `e_1(W_0') = e_0(W_0) = 0`. Its
Magnus piece is isomorphic to `B_0` by an isomorphism matching the two packets.
`QED`

No new soficity follows in rank one. Here `G_m` is an HNN extension of
`<a_0, a_1 | W_0^m>` along the cyclic subgroups `<a_0>` and `<a_1>`. If the
piece is packet-visible, it is sofic by the criterion. Soficity then passes to
the HNN extension over an amenable subgroup. What Theorem B transports is the
**packet property** itself, which is the content of the hole.

**Proposition 5.1 (truncation obstruction).** Let `(P, Phi, ell)` satisfy
(T1) and (T2), with `ell != 1`. For `1 <= k <= r`, let
`V_k(x_1, ..., x_(r-k+1))` be the word obtained from `W_0` by substituting
`a_0 = ... = a_(k-1) = 1` and `a_(k-1+j) = x_j`. Then:

1. `V_k(phi_1, ..., phi_(r-k+1)) = 1` in `Phi`, for every `k`.
2. In the group `H` of Theorem A, `V_k(a_i, ..., a_(i+r-k)) = 1` for all `i`
   and `k`. So `pi` factors through `G_m / <<t^j V_k(a_0, ..., a_(r-k)) t^(-j)>>`.
3. `e_r(W_0) = 0`.
4. `Phi` is a marked quotient of `F(a_1, ..., a_r)/<<W_0(1, a_1, ..., a_r)>>`.

*Proof.* Induction on `k`.

* **Base `k = 1`.** Project (T1) along `P -> P/L = Phi`.
* **Step.** If `V_k(phi_1, ..., phi_(r-k+1)) = 1`, apply `mu` from (T2) to get
  `V_k(ell, phi_1, ..., phi_(r-k)) = 1` in `P`. Projecting to `Phi` gives
  `V_k(1, phi_1, ..., phi_(r-k)) = V_(k+1)(phi_1, ..., phi_(r-k)) = 1`.

This proves (1). Item (2) follows from (1) and the marked isomorphisms
`Phi = <a_i, ..., a_(i+r-1)>` in `N`. For (3), `V_r(x_1) = x_1^(e_r(W_0))`.
Now `phi_1 = mu^(-1)(ell) != 1` has infinite order, since `P` is torsion-free.
Item (4) is (1) with `k = 1`. `QED`

Consequences:

* **Rank one.** `V_1(x_1) = x_1^(e_1(W_0))`, so (T1)--(T3) force
  `e_1(W_0) = 0`. Moreover a window is then itself a packet-retaining quotient
  of `B_0`, by (T1) and (T3). So Theorem B is exactly the scope of Theorem A in
  rank one.
* **Bottom-linear case.** Call `W_0` **bottom-linear** if
  `W_0(1, a_1, ..., a_r) = 1` in `F(a_1, ..., a_r)`. Then every `V_k` is
  trivial in the free group, and (2) imposes no extra relation.
  * In rank one, bottom-linear means `e_1(W_0) = 0`.
* **Otherwise.** The tower quotient satisfies the nontrivial additional
  relations `V_k`. A window can exist only if `S(w)` survives in the quotient
  of `G` by all their shifts.

## 6. Theorem C (bottom-linear wreath towers)

**Iterated wreath products.** Put `W_1 = Z = <phi_1>`. For `k >= 2`, let
`W'_(k-1)` be a copy of `W_(k-1)` whose marked generators are renamed
`phi_2, ..., phi_k`, and put

    W_k = Z wr W'_(k-1) = (direct sum over W'_(k-1) of Z) x| W'_(k-1).

Here `phi_1` is the lamp at the identity. There is a homomorphism
`deg : W_k -> Z` with `deg(phi_k) = 1` and `deg(phi_j) = 0` for `j < k`: kill
the base and use `deg` on `W'_(k-1)`. Let `A_k = ker deg`, so that
`W_k = A_k x| <phi_k>`.

**Lemma 6.1 (bottom truncation).** For `k >= 2`, the subgroup
`<phi_1, ..., phi_(k-1)>` of `W_k` is marked isomorphic to `W_(k-1)`, and it
lies in `A_k`.

*Proof.* For a subgroup `T <= W'_(k-1)`, the subgroup `<phi_1, T>` equals
`Z[T].phi_1 x| T`. The `T`-orbit of the identity lamp is free, so this is
`Z wr T`. Take `T = <phi_2, ..., phi_(k-1)>`.

* For `k = 2`, `T = 1` and the subgroup is `Z = W_1`.
* For `k >= 3`, induction applied to `W'_(k-1)` makes `T` marked isomorphic to
  `W'_(k-2)`, so the subgroup is marked `Z wr W'_(k-2) = W_(k-1)`.

The generators have degree `0`. `QED`

**Lemma 6.2 (degree-extreme products).** For nonzero `g`, `f` in `Q[W_k]`,
the product `gf` has a nonzero coefficient in degree
`maxdeg(g) + maxdeg(f)` and one in degree `mindeg(g) + mindeg(f)`. Here
`maxdeg` and `mindeg` are taken over the support.

*Proof.* **Ordering.** Free abelian groups are orderable. An extension of a
left-orderable group by a left-orderable group is left-orderable, using the
lexicographic positive cone. By induction `W_k` is left-orderable, and hence so
is `A_k`. Order `W_k` lexicographically along `1 -> A_k -> W_k -> Z -> 1`:
`x < y` iff `deg(x^(-1) y) > 0`, or `deg(x^(-1) y) = 0` and
`x^(-1) y >_(A_k) 1`. This order is left-invariant, and `deg(x) < deg(y)`
implies `x < y`.

**The maximum.** Let `X = supp g`, `Y = supp f`, and `y* = max Y`. The
elements `x y*` for `x in X` are distinct, so there is a unique `x_0` making
`x_0 y*` maximal. Suppose `x_0 y* = x y` with `x in X` and `y in Y`. Then
`x y <= x y* <= x_0 y*`, so `y = y*` and `x = x_0`. Hence the coefficient of
`x_0 y*` in `gf` is `g_(x_0) f_(y*) != 0`.

Because the order is degree-dominant, `deg y* = maxdeg(f)`. Since `x_0` is
maximal among the `x y*`, also `deg x_0 = maxdeg(g)`. The minimum is
symmetric. `QED`

**Lemma 6.3 (Fox formula).** Let `M x| S` have multiplication
`(x,s)(x',s') = (x + s.x', s s')`, with `M` a left `Z[S]`-module. Let
`h : F(a_0, ..., a_r) -> M x| S` satisfy `h(a_0) = (m, 1)` and
`h(a_j) = (0, s_j)` for `j >= 1`. Let `psi(a_0) = 1` and `psi(a_j) = s_j`.
Then for every word `V`,

    h(V) = ( psi(dV/da_0) . m ,  psi(V) ).

*Proof.* Let `d` be the first coordinate of `h`. It satisfies
`d(UV) = d(U) + psi(U).d(V)`, with `d(a_0) = m` and `d(a_j) = 0`. The map
`V -> psi(dV/da_0).m` satisfies the same rule, by the product rule for Fox
derivatives, and takes the same values on the generators. A `psi`-derivation
is determined by its values on generators. `QED`

**Setup.** Assume `W_0` is bottom-linear: `W_0(1, a_1, ..., a_r) = 1` in
`F(a_1, ..., a_r)`. Define:

* `psi : F(a_0, ..., a_r) -> W_r` by `a_0 -> 1` and `a_j -> phi_j`;
* `fbar = psi(dW_0/da_0) in Z[W_r]`;
* `L = Q[W_r] / Q[W_r] fbar`, a left module;
* `ell` = the class of `1`;
* `P = L x| W_r`, with `Phi = W_r`;
* `B = <phi_1, ..., phi_(r-1)>`, with `B = 1` when `r = 1`.

**(FH)** `Q[B] intersect Q[W_r] fbar = 0`.

**Theorem C.** Assume `W_0` is bottom-linear and (FH) holds. Then
`(P, W_r, ell)` is a window satisfying (T1) and (T2). `P` is solvable of
derived length at most `r+1`, locally indicable, and elementary amenable.

(FH) holds whenever `fbar = 0`, or the support of `fbar` meets at least two
values of `deg`. Consequently, if (T3) also holds, Theorem A gives an
elementary amenable, locally indicable quotient of `G_m` retaining `S(w)`,
and `G_m` is sofic.

*Proof.*

**Properties of `P`.** `L` is a rational vector space, hence torsion-free
abelian. `W_r` is solvable and locally indicable. So `P` is elementary amenable
and locally indicable, of derived length at most `r+1`.

**(T1).** By Lemma 6.3, `W_0(ell, phi) = (fbar.ell, W_0(1, phi)) = (0, 1)`.
The first coordinate is `fbar.ell = [fbar] = 0`. The second is `1` by
bottom-linearity.

**(T2).** The subgroup `<ell, B>` equals `Z[B].ell x| B`. The map
`Z[B] -> L`, `x -> x.ell = [x]`, has kernel
`Z[B] intersect Q[W_r] fbar = 0` by (FH). So `<ell, B>` is `Z wr B`, with
`ell` the identity lamp.

* **Rank `r >= 2`.** By Lemma 6.1, `B` is marked isomorphic to `W_(r-1)`, with
  `phi_j` corresponding to the `j`-th generator. Also
  `W_r = Z wr W'_(r-1)`, with `phi_1` the identity lamp and `phi_(j+1)`
  corresponding to the `j`-th generator. A marked isomorphism of the acting
  groups extends to the wreath products. This gives `mu`, with
  `phi_1 -> ell` and `phi_(j+1) -> phi_j`.
* **Rank `r = 1`.** (FH) says `Z.ell = Z`, so `ell` has infinite order.

**Sufficient condition for (FH).** Suppose `fbar != 0` and `g fbar` is a
nonzero element of `Q[B]`. Then `g != 0`. By Lemma 6.1, `Q[B] <= Q[A_r]` is
supported in degree `0`. By Lemma 6.2, `g fbar` has nonzero coefficients in
degrees `maxdeg(g) + maxdeg(fbar)` and `mindeg(g) + mindeg(fbar)`. These are
different when `fbar` meets two degrees. That is a contradiction. `QED`

**Lemma 6.4 (metabelian retention test).** Let
`R = Q[x_1^(+-1), ..., x_r^(+-1)]`. Let `psi~ : F(a_0, ..., a_r) -> Z^r`
send `a_0 -> 0` and `a_j -> e_j`, extended to group rings, and put
`f~ = psi~(dW_0/da_0) in R`.

Under the hypotheses of Theorem C, (T3) holds provided the following holds for
every proper nonempty contiguous arc `U` of cyclic `W_0`: either
`(e_1(U), ..., e_r(U)) != 0`, or `psi~(dU/da_0)` is not in the ideal
`R f~`.

*Proof.* `W_r -> Z^r` with `phi_j -> e_j` exists: sum the lamps and use
induction. The induced ring map `Q[W_r] -> R` sends `fbar` to `f~`. So
`L -> R/(f~)` is compatible with the actions, and
`P -> R/(f~) x| Z^r` is a homomorphism sending `ell -> [1]` and
`phi_j -> e_j`. By Lemma 6.3, the image of `U(ell, phi)` is
`([psi~(dU/da_0)], e(U))`. `QED`

Membership in a principal ideal of a Laurent polynomial ring is decided by
clearing monomials and dividing. The test is metabelian, but it runs on the
window, which is a quotient of `B_0` and not of `G`. So it is not subject to
the solvable boundary [[rational-solvable-weinbaum-visibility-boundary]], which
concerns quotients of `G` itself.

When the support of `fbar` lies in a single degree, (FH) is open in general.
In rank one, this case means `fbar = c phi_1^d` with `c != 0` rational. Then
`L = 0` and (T2) fails.
