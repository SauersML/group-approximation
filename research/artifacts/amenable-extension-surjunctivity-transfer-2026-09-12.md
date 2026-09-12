# Surjunctivity through normal subgroups: coset transplants, decoders in the kernel, amenable quotients

Lane `w5-free-pos-c`, 2026-09-12.

**Established claims supported:**
- `normal-surjunctive-decoder-memory-forces-surjectivity` (Section 2)
- `complex-lamplighter-linearizations-are-normal-iff-surjective` (Section 1.3)

**Open claim supported:** `surjunctive-by-amenable-extensions-are-surjunctive`.

Conventions: a cellular automaton over a group `G` has a finite alphabet `A`, a finite memory `M`, a
local rule `mu`, and `tau(x)(g) = mu((x(gm))_(m in M))`. It commutes with left shifts
`(h.x)(g) = x(h^-1 g)`. Curtis--Hedlund--Lyndon holds over every group. `lambda` is the uniform
product measure. We add `e` to every memory set without loss.

## 0. Choice and scope

The lane was asked for a positive approach no active lane holds. Section 1 checks the three
suggestions in the launch prompt and finds that each collapses onto a front that is already held,
with one exception: extensions with amenable quotient, of which ascending HNN extensions are the
simplest case. Sections 2--3 develop that exception by transplanting an automaton over `G` to the
kernel `N` along coset coordinates.

## 1. The three suggested ideas

### 1.1 Amalgams and HNN extensions over finite or amenable edge groups

- **Free products and amalgams.** `graph-folds-over-surjunctive-groups-are-surjunctive` (O5) needs a
  surjunctive target injective on vertex groups. For `A *_C B` the natural target is a product, and
  `graph-products-of-surjunctive-groups-are-surjunctive` already records that graph products, free
  products included, follow from binary products. Binary products are held by the quantitative
  surjunctivity lane.
- **HNN extensions over finite subgroups.** A finite-index subgroup meeting every conjugate of the edge
  group trivially reduces them to free products by commensurability invariance, so again to products.
  Without such a subgroup the edge data act through vertex groups that need not be residually finite,
  and no host is known.
- **Ascending HNN extensions** `N *_phi = <N, t | t n t^-1 = phi(n)>` with `phi` injective are the
  exception. Their kernel onto `Z` is the directed union `N^ = union_k t^-k N t^k` of copies of `N`,
  which is surjunctive whenever `N` is (directed unions preserve surjunctivity). So they are
  `(surjunctive)`-by-`Z` groups, and no operation O1--O7 of
  `gottschalk-counterexamples-lie-outside-the-permanence-closure` applies when `N^` is not residually
  finite. This is the case developed below.

### 1.2 Model-theoretic compactness

Surjunctivity is axiomatized by rectangle clauses, and every strict datum has a universal finitely
presented test group (`surjunctivity-is-axiomatized-by-rectangle-clauses`,
`strict-pairs-transfer-to-table-realizations`). The launch-prompt question "do the test groups share
a uniform property" is the design-filter programme already on main (table groups, holonomy, forward
cores). Nothing new was found to add.

### 1.3 Characteristic-zero linearization

Identify `A` with `Z/q`, and put `L = (+)_(g in G) Z/q` and `H = L x| G = Z/q wr G`. Fourier expansion
identifies the locally constant functions `LC(A^G)` with the group algebra `C[L]`: the character of
`xi in L` is `chi_xi(x) = exp(2 pi i sum_g xi(g) x(g) / q)`, and shifts permute the basis. So
`LC(A^G) x|_alg G = C[H]`. The canonical trace `tr(sum a_h h) = a_e` restricts to `f -> integral f d lambda`
on `C[L]`.

**Theorem C.** Let `tau` be an automaton on `A^G` and `nu = tau_* lambda`.

1. `Phi_tau(sum_g f_g u_g) = sum_g (f_g o tau) u_g` is a unital *-endomorphism of `C[H]` fixing `C[G]`.
2. `tau` is injective iff `Phi_tau` is surjective, and `tau` is surjective iff `Phi_tau` is injective.
3. `tr o Phi_tau` is the trace of `nu`: `tr(Phi_tau(f u_g)) = [g = e] integral f d nu`. For the von Neumann
   rank function `rk` of `L(H)`, `rk(Phi_tau(f)) = nu(supp f)` for `f in C[L]`.
4. Let `G` be infinite and `tau` injective. These are equivalent: (a) `tau` is surjective; (b) `Phi_tau`
   preserves `tr`; (c) `Phi_tau` extends to a normal *-endomorphism of `L(H)`; (d) `nu << lambda`.

*Proof.*
1. Pullback of locally constant functions along a continuous map is a unital *-homomorphism of
   `LC(A^G)`, and it commutes with shifts. The formula `(f u_g)(f' u_h) = f (g.f') u_(gh)` is preserved
   because `(g.f') o tau = g.(f' o tau)`.
2. If `tau` is injective it is a homeomorphism onto the closed set `X = tau(A^G)`. A locally constant `h`
   on `A^G` gives `h o tau^-1` on `X`, locally constant with finitely many clopen level sets. These are
   traces of disjoint clopens of `A^G`, so `h o tau^-1` extends to `k in LC(A^G)` with `k o tau = h`.
   Conversely, if `tau(x) = tau(y)` with `x != y`, a cylinder function `f` separating `x` and `y` cannot
   equal `k o tau`. For surjectivity: `f o tau = 0` iff `f` vanishes on `X`, and a nonzero locally
   constant function vanishing on `X` exists iff `X != A^G`, since `A^G \ X` is open and contains a
   cylinder. `Phi_tau` acts coefficientwise, so both statements pass to `C[H]`.
3. `tr(f o tau) = integral f o tau d lambda = integral f d nu`. A multiplication operator in `L(H)` has
   rank equal to the trace of its support projection, and `supp(f o tau) = tau^-1(supp f)`.
4. (a) => (b): a bijective automaton preserves `lambda` (`bijective-ca-preserve-uniform-bernoulli-measure`).
   (b) => (c): a trace-preserving unital *-homomorphism is isometric on `L^2(tr)`, so it extends to a
   normal *-endomorphism of the generated von Neumann algebra. (c) => (d): suppose `nu(K) > 0` for a
   compact `lambda`-null `K`. Choose clopens `C_k` decreasing to `K`. Then `1_(C_k) -> 0` strongly in
   `L(H)`, so a normal extension sends it to `1_(tau^-1 C_k) -> 0` weakly, and
   `lambda(tau^-1 C_k) = tr(1_(tau^-1 C_k)) -> 0`. But `tau^-1 C_k` decreases to `tau^-1 K`, whose measure is
   `nu(K) > 0`. (d) => (a): `nu` is invariant and absolutely continuous with respect to the ergodic `lambda`,
   so `nu = lambda`. Then `X` is closed with full measure, hence `X = A^G`. QED

**Consequence (proved).** A strict automaton linearizes to a surjective, non-injective,
non-normal *-endomorphism of the lamplighter algebra `C[Z/q wr G]`.

**Interpretation (not a theorem).** Theorem C computes only the canonical trace and the von Neumann rank
function of `L(H)`, together with normality over `(A^G, lambda)`. For these, detecting surjectivity is exactly
proving `nu << lambda`, which is `every-injective-ca-preserves-uniform-bernoulli-measure` in other notation. Our
reading is that characteristic-zero positivity (Kaplansky's trace) gives no independent access. That is not
proved: other Sylvester rank functions on `C[Z/q wr G]`, and non-tracial invariants, are not addressed.
(Wording requested by w4-vf-positive-b, §6 of its verification artifact.)

**Remark (the finite-dimensional filtration).** The local functions of radius `s`, `V_s = span{chi_xi :
supp xi in g B_s for some g}`, form a permutation module `C (+) (+)_O C[G/F_O]` with finite stabilizers,
of von Neumann dimension `d_s = sum_(xi : e in supp xi) 1/|supp xi|` over the nonzero modes counted.
Pullback gives bounded `L(G)`-operators `T_s : V_s^- -> V_(s+R)^-`. The decoder identity and
strictness give only `d_(s+R') >= d_s + dim ker T_(s+R')`. That is satisfied by trivial complex linear
data, because the obstruction lives in the ideal of functions vanishing on `X`, which is
multiplicative, while every filtration of finite dimension is additive. No claim is landed on this.

## 2. Decoders inside a surjunctive normal subgroup

**Coset coordinates.** Let `N` be normal in `G`, `Q = G/N`, and fix representatives `s_q` with `s_e = e`.
For `x in A^G` put `x_q(n) = x(n s_q)`. Left translation by `n' in N` acts on every `x_q` by the left
shift. For `g in G` and `q in Q` write `s_q g = n_(q,g) s_(q gbar)` with `n_(q,g) in N`.

**Lemma 2.1 (transplant).** For an automaton `tau` over `G` with memory `M`,
`tau(x)_q(n) = mu((x_(q mbar)(n n_(q,m)))_(m in M))`. So for every finite `F <= Q`, with `F^+ = F Mbar`,
restricting `tau` gives an automaton over `N`, `tau_F : (A^(F^+))^N -> (A^F)^N`.

*Proof.* `n s_q m = n n_(q,m) s_(q mbar)`. The rule is equivariant under left `N`-translation, and it
reads finitely many coordinates. QED

**Theorem A.** Let `N` be a surjunctive normal subgroup of `G`, and `tau`, `sigma` automata over `G` with
`sigma tau = id`. If the memory `S` of `sigma` lies in `N`, then `tau` is surjective.

*Proof.* Suppose `X = tau(A^G) != A^G`. Then some pattern `p` on a finite window `W` never occurs in `X`.
Put `F = Wbar` and `F^+ = F Mbar`.
- **The decoder stays on its coset.** For `d in S`, `s_q d = (s_q d s_q^-1) s_q`, so `sigma` acts
  coordinatewise: `sigma(y)_q` depends only on `y_q`, through an automaton `sigma_q` over `N`.
- **An injective automaton over `N`.** Define `Psi(x) = (tau_F(x), x|_(F^+ \ F))` on `(A^(F^+))^N`. For
  `q in F`, `sigma_q(tau_F(x)_q) = x_q`. So `Psi` is injective, continuous and `N`-equivariant, from the
  full shift with alphabet `A^(F^+)` into the full shift with alphabet `A^F x A^(F^+ \ F)`, which has the
  same size.
- **Its image is proper.** For `w in W` write `w = n_w s_(wbar)`. The translate `nW <= U_F` gives
  positions `n n_w s_(wbar)`, which are coordinates `(wbar, n n_w)`. Every `tau_F(x)` lies in the
  subshift `Z` of `(A^F)^N` in which `(z_(wbar)(n n_w))_(w in W) != p` for every `n`. The map
  `w -> (wbar, n_w)` is injective, so some configuration shows `p` at `n = e`, and `Z` is proper.
- **Contradiction.** `Psi` is then an injective, non-surjective automaton on a full shift over `N`,
  contradicting surjunctivity of `N`. QED

**Remarks.**
1. The encoder memory is arbitrary, and neither `G/N` nor the decoder's memory group needs to be
   amenable. This complements `amenable-decoder-memory-forces-surjectivity`, which needs the decoder's
   memory group to be amenable but no normality.
2. **Filter.** In a strict pair, the normal closure of the decoder memory in `G` is not surjunctive. In
   particular it is not sofic and does not lie in the permanence closure `S*`.
3. **Where it is vacuous.** On a simple group the normal closure is the whole group, so Theorem A says
   nothing on the payoff hosts. It restricts designs over non-simple memory groups and table groups.

## 3. Decoders that read across cosets: amenable quotients

**Definition (uniform quantitative surjunctivity, UQS).** A group `N` is *uniformly quantitatively
surjunctive* if, for every finite alphabet `B` and every `w >= 1`, there is `delta(B,w) > 0` with the
following property. Take any finite alphabet `D`, any `n >= 1` and `j, j' >= 0` with
`(j' - j) log|D| < delta(B,w) n`, and subshifts `Y_1, ..., Y_n` of `B^N`, each missing some pattern on a window
of at most `w` elements. Then no injective automaton maps `(B^n x D^j)^N` into `(Y_1 x ... x Y_n) x (D^(j'))^N`.

- **Relation to QS.** UQS implies `surjunctive-groups-are-quantitatively-surjunctive`'s property: take all `Y_i`
  equal. The difference is that different tracks may miss different patterns, with a constant depending only on
  `|B|` and the window size.
- **Sofic groups (remark, not re-derived).** The counting in Section 3 of
  `product-fibre-garden-of-eden-filter-2026-09-12.md` treats each track's missing pattern separately, and its
  constant depends only on `|B|` and `|W|`. So it gives UQS for sofic groups.

**Definition (asymptotic version, AQS).** `N` is *asymptotically quantitatively surjunctive* if, for every `B`,
`w` and `K >= 0`, there is `n_0` such that the same maps do not exist when `n >= n_0` and
`(j' - j) log|D| <= K`. UQS implies AQS, with `n_0 > K / delta(B,w)`.

**Theorem B.** Let `N` be a normal subgroup of `G` with amenable quotient `Q = G/N`.
1. If `N` is UQS, then `G` is surjunctive.
2. If `N` is AQS and `Q` is two-ended, then `G` is surjunctive.

*Proof.* Let `tau` be injective with a left-inverse automaton `sigma` of memory `S`, and suppose `X = tau(A^G)` misses
a pattern `p` on `W`. Take a finite `F <= Q` and put
`F^+ = F Mbar`, `F^- = {q in F : q Sbar <= F}` and `F' = {q : q Wbar <= F}`.
- **Tiles.** Choose `q_1, ..., q_n` in `F'` with the tiles `T_i = q_i Wbar` pairwise disjoint and the family
  maximal. Every `q in F'` lies in some `q_i Wbar Wbar^-1`, so `n >= |F'| / |Wbar Wbar^-1|`.
- **The transplant.** `Psi(x) = (tau_F(x), x|_(F^+ \ F^-))` on `(A^(F^+))^N`. The decoder restricted to the coordinates
  of `F` is an automaton over `N` returning `x_q` for `q in F^-` (Lemma 2.1 applied to `sigma`). So `Psi` is an
  injective automaton over `N`.
- **Where the image lies.** Write `s_(q_i) w = n_(i,w) s_(q_i wbar)`. Every `tau_F(x)` lies in
  `Z_1 x ... x Z_n x (A^(F \ union T_i))^N`, where `Z_i` is the subshift of `(A^(T_i))^N` with
  `(z_(q_i wbar)(n n_(i,w)))_(w in W) != p` for all `n`. The map `w -> (q_i wbar, n_(i,w))` is injective, so `Z_i` is
  proper and misses a pattern on `|W|` sites. Identify `A^(T_i)` with `B = A^(Wbar)`.
- **Bookkeeping.** The source is `(B^n x A^j)^N` with `j = |F^+| - n|Wbar|`. The target's full track has
  `j' = |F \ union T_i| + |F^+ \ F^-|`. So `j' - j = |F \ F^-|`.
- **Part 1.** Take `F` right Følner: `|F K \ F| <= eps|F|` for `K = Sbar union Wbar`. Then
  `|F \ F^-| <= |Sbar| eps |F|` and `|F \ F'| <= |Wbar| eps |F|`, so `n >= (1 - |Wbar| eps)|F| / |Wbar Wbar^-1|`. For
  small `eps`, `(j' - j) log|A| < delta(B,|W|) n`, and `Psi` contradicts UQS.
- **Part 2.** For two-ended `Q`, choose `F` large with `|F \ F^-|` bounded independently of `|F|`: take unions of
  long intervals of a finite-index infinite cyclic subgroup over a transversal. Then `j' - j` is bounded while
  `n -> infinity`, and `Psi` contradicts AQS. QED

**Proposition 3.1 (heredity).**
1. If `N` is UQS with constant function `delta(B,w)`, or AQS with threshold function `n_0(B,w,K)`, every subgroup of `N`
   has the same property with the same constant or threshold.
2. Let `N^ = union N_k` be a directed union. Suppose every `N_k` is UQS with one shared constant function
   `delta(B,w)`, or AQS with one shared threshold function `n_0(B,w,K)`. Then `N^` is UQS, respectively AQS, with that
   constant or threshold.

Uniformity in part 2 is needed: a forbidden map living at stage `k` contradicts only that stage's constant, so
constants tending to `0`, or thresholds tending to infinity, along the stages give nothing. (Scope note by
w3-vf-positive, Section 19 of its verification artifact.)

*Proof.*
- **Subgroups.** Let `H <= N` and let `Psi` over `H` be a forbidden map. Its memory lies in `H`, so it acts
  independently on left cosets `gH`, and the product over cosets is injective over `N`. Put
  `Y~_i = {y in B^N : (y(gh))_(h in H) in Y_i for all g}`. This is closed, `N`-invariant and proper, and it misses the
  same pattern. The product map lands in `prod Y~_i x full` and is forbidden over `N`.
- **Directed unions.** A map over `N^ = union N_k` that violates the shared constant has its memory, and the
  windows of the missing patterns, inside some `N_k`. Restricted to the coset `N_k`, it is a map over `N_k` into the
  restrictions `Y_i|_(N_k)`, which are proper subshifts missing the same patterns. The parameters `n, j, j', |D|`
  are unchanged, so it violates the same constant for `N_k`. QED

**Corollary 3.2 (ascending HNN extensions).** Let `phi: N -> N` be an injective endomorphism.
- If `N` is AQS, the ascending HNN extension `N *_phi` is surjunctive.
- **Proof.** Its kernel onto `Z` is the directed union of the copies `t^-k N t^k`. They are isomorphic to `N`, so they
  share `N`'s AQS threshold, and the union is AQS by Proposition 3.1 part 2. Apply Theorem B part 2.

**Calibration.** For sofic `N`, Theorem B gives nothing new: sofic-by-amenable groups are sofic
(`sofic-kernel-amenable-quotient-permanence`). The payoff needs UQS or AQS for a nonsofic surjunctive kernel.

## 4. Where it stops

- **No nonsofic kernel is known to be UQS or AQS.** The Kun--Thom wreaths and doubles are proved surjunctive by
  marked-site peeling. That argument separates finite quotients stratum by stratum and carries no deficit, so it
  proves neither property. A proof would have to carry a per-track deficit through each peeled stratum.
- **What a failure of AQS looks like.** A surjunctive `N`, and injective automata over `N` from full shifts into `n`
  proper subshift tracks plus a full track `K` symbols larger, for unboundedly large `n`. Plain surjunctivity
  forbids this only when `K = 0`.
- **Theorem A is the `K = 0` case.** It needs no quantitative property, because a decoder inside the kernel loses
  no boundary.
- **Twisted extensions need the uniform version.** In a split extension that is not a direct product, the tiles
  carry different transported patterns (offsets `s_q n_w s_q^-1` times a cocycle in `N`). That is why UQS has to allow
  different missing patterns on different tracks. For `G = N x Q` all tiles agree, and the existing
  single-subshift QS suffices for Theorem B part 1.
- **The payoff hosts.** Simple Kazhdan groups have no normal subgroup with amenable quotient other than finite
  index. So neither theorem reaches the Leavitt unit groups.
