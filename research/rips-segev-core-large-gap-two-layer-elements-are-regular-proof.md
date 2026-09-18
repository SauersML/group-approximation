---
rg: 2
id: rips-segev-core-large-gap-two-layer-elements-are-regular-proof
kind: route
title: Follow extreme ports along b-edges until the walk closes, then read a complete b-a-b syllable off a large exterior arc of a van Kampen face
target: rips-segev-core-large-gap-two-layer-elements-are-regular
requires: [rips-segev-groups-embed-every-torsion-free-group]
---

**Conventions.**  Citations are to Steenbock, arXiv:1307.0981: Theorem "tf" (torsion-freeness), Theorem "gi"
(injection of the graph into the Cayley graph), Lemma "Hilfssatz van Kampen", and the graphical small cancellation
lemma.  Further conventions:
- `F = <a> * <b>`, with `a`, `b` of infinite order.
- `Gamma` is a generalized Rips--Segev graph labelled by `{a^{±1}, b^{±1}}`, with reduced labelling satisfying
  `Gr'_*(lambda)`, `lambda = 1/8`.  Put `R` for the labels of its cycles, `K = F / <<R>>`, and `Lambda`, `gamma`
  for the maximal piece length and the minimal cycle length (free product length `|.|_*`).  So `Lambda < gamma/8`.
- A single `a`-edge immerses at many places of a line, so it is a piece: `Lambda >= 1` and `gamma >= 9`.
- `K` is torsion-free (Theorem "tf"), and `a != 1` in `K` (Step 0 of
  `rips-segev-groups-embed-every-torsion-free-group-proof`).  So `a` has infinite order in `K`.
- The vertices of `Gamma` are the line vertices `v_{il}`, `0 <= l <= C_i`.  The `a`-edges run `v_{il} -> v_{i,l+1}`.
  Every `b`-edge runs from a vertex `v_{iq}` with `q in S_i` (its *source position*) to a vertex `v_{jp}` with
  `p in T_j` (its *target position*).  In a reduced labelling each vertex has at most one outgoing and at most
  one incoming edge of each label.
- `Delta = {0} ∪ {q - p : i a line, p in T_i, q in S_i}`, `Delta_± = max/min Delta`.  So
  `Delta_- <= 0 <= Delta_+` and `|Delta_±| <= max_i C_i`.
- For `0 != f in k[<a>]`, `f_+` and `f_-` are its top and bottom exponents.  Since `k[<a>] = k[t^{±1}]` is a
  domain, `(fg)_± = f_± + g_±`.
- A *left `<a>`-coset* is `T = x<a>`.  It is ordered by `x a^m < x a^{m'}` iff `m < m'`.  This is well defined
  because `a` has infinite order and right translation by `a` is order preserving.  Every nonempty finite subset
  of `T` has a max and a min.

---

## 1. Port configurations

**Definition.**  A *port configuration with offsets `(d_+, d_-)`* is a finite nonempty set `𝒞` of left
`<a>`-cosets together with, for each `T in 𝒞`, nonempty finite subsets `Out_T, In_T ⊆ T`, such that:
- (P1) `⊔_T In_T = (⊔_T Out_T) · b`, as subsets of `K`;
- (P2) `max Out_T = (max In_T) a^{d_+}` and `min Out_T = (min In_T) a^{d_-}` for every `T in 𝒞`.

The unions in (P1) are disjoint because distinct cosets are disjoint.

**Lemma 1 (port lemma).**  Let `u, w in k[<a>]` be nonzero.
- (a) If `0 != alpha in k[K]` and `alpha (u + w b) = 0`, then there is a port configuration with offsets
  `(w_+ - u_+, w_- - u_-)`.
- (b) If `0 != alpha' in k[K]` and `alpha' (v + b z) = 0` with `0 != v, z in k[<a>]`, then there is a port
  configuration with offsets `(z_+ - v_+, z_- - v_-)`.
- (c) If `0 != alpha in k[K]` and `(u + w b) alpha = 0`, then there is a port configuration with offsets
  `(w_- - u_-, w_+ - u_+)`.

*Proof of (a).*  Write `alpha = sum_T alpha_T`, where `alpha_T` is the part of `alpha` supported on the coset `T`.
Let `𝒞` be the set of `T` with `alpha_T != 0`.  Fix `x_T in T` and write `alpha_T = x_T f_T(a)` with
`0 != f_T in k[t^{±1}]`.  Put `Out_T = supp(alpha_T w)` and `In_T = supp(alpha_T u)`.  Both are nonempty, since
`f_T w` and `f_T u` are nonzero Laurent polynomials.
- (P1).  `alpha_T u` and `alpha_T w` are supported in `T`.  So `supp(alpha u) = ⊔_T In_T` and
  `supp(alpha w) = ⊔_T Out_T`.  Right multiplication by `b` is a bijection on `K`, so
  `supp(alpha w b) = (⊔_T Out_T) b`.  Since `alpha u = - alpha w b`, the two supports agree.
- (P2).  `max Out_T = x_T a^{(f_T)_+ + w_+}` and `max In_T = x_T a^{(f_T)_+ + u_+}`, so their offset is
  `w_+ - u_+`.  The minimum is the same with bottom exponents. ∎

*Proof of (b).*  Decompose `alpha'` and `p := alpha' b` over left cosets: `alpha'_T` and `p_T`.  Since `v` and `z`
lie in `k[<a>]`, the coset-`T` part of `alpha' v` is `alpha'_T v`, and that of `p z` is `p_T z`.  So
`alpha' v = - p z` gives `alpha'_T v = - p_T z` for every `T`.  In particular `alpha'_T != 0` iff `p_T != 0`.
Let `𝒞` be the set of such `T`, and put `Out_T = supp(alpha'_T)`, `In_T = supp(p_T)`.
- (P1).  `⊔ In_T = supp p = supp(alpha') b = (⊔ Out_T) b`.
- (P2).  Comparing top exponents in `alpha'_T v = - p_T z` gives
  `max Out_T · a^{v_+} = max In_T · a^{z_+}`, so the offset is `z_+ - v_+`.  The bottom is the same. ∎

*Proof of (c).*  Let `*` be the linear anti-involution `g -> g^{-1}` of `k[K]`.  Applying it gives
`alpha^* (u^* + b^{-1} w^*) = 0`, that is, `(alpha^* b^{-1}) (w^* + b u^*) = 0`, with `alpha' = alpha^* b^{-1} != 0`.
Apply (b) with `v = w^*`, `z = u^*`.  Since `(f^*)_+ = - f_-` and `(f^*)_- = - f_+`:
- `z_+ - v_+ = - u_- + w_- = w_- - u_-`;
- `z_- - v_- = - u_+ + w_+ = w_+ - u_+`. ∎

---

## 2. Walks close into positive relations

A *positive relation* of `K` is an equation `b a^{n_1} b a^{n_2} ... b a^{n_L} = 1` in `K`, with `L >= 1` and
integers `n_k`, possibly zero.

**Lemma 2 (walk lemma).**  Let `(𝒞, Out, In)` be a port configuration with offsets `(d_+, d_-)`.  Then `K` has
four positive relations:
- (i) one with all `n_k >= d_+`;
- (ii) one with all `n_k <= d_+`;
- (iii) one with all `n_k <= d_-`;
- (iv) one with all `n_k >= d_-`.

*Proof of (i): top out-ports, forward.*  For `T in 𝒞` put `y_T = max Out_T`.
- By (P1), `y_T b in In_{T'}` for a unique `T' in 𝒞`, namely `T' = y_T b <a>`.  Put `sigma(T) = T'`.
- Then `max In_{T'} = y_T b a^e` for some `e >= 0`.  By (P2), `y_{T'} = y_T b a^{e + d_+}`.
- So `y_{sigma(T)} = y_T b a^{n(T)}` with `n(T) >= d_+`.

`sigma` is a self-map of the finite set `𝒞`.  Pick `T_0 in 𝒞` and put `T_j = sigma^j(T_0)`.  Some `T_i = T_j` with
`i < j`.  Then

    y_{T_i} = y_{T_j} = y_{T_i} b a^{n(T_i)} b a^{n(T_{i+1})} ... b a^{n(T_{j-1})},

so `b a^{n(T_i)} ... b a^{n(T_{j-1})} = 1` with `L = j - i >= 1` and every exponent `>= d_+`. ∎

*Proof of (ii): top in-ports, backward.*  For `T in 𝒞` put `x_T = max In_T`.
- By (P1), `x_T = z b` for a unique `z in ⊔ Out`, say `z in Out_{T'}`.  Put `tau(T) = T'`.
- Then `max Out_{T'} = z a^e` with `e >= 0`, and by (P2) `x_{T'} = max In_{T'} = z a^{e - d_+}`.
- So `x_T = x_{tau(T)} a^{m(T)} b` with `m(T) = d_+ - e <= d_+`.

Again `tau^i(T_0) = tau^j(T_0)` for some `i < j`.  Writing `T_l = tau^l(T_0)` and iterating gives

    x_{T_i} = x_{T_j} a^{m(T_{j-1})} b ... a^{m(T_i)} b.

So `a^{m(T_{j-1})} b ... a^{m(T_i)} b = 1`.  Conjugating by `b` gives the positive relation
`b a^{m(T_{j-1})} b ... b a^{m(T_i)} = 1`, with every exponent `<= d_+`. ∎

*Proof of (iii): bottom out-ports, forward.*  Put `y_T = min Out_T`.  Then `y_T b in In_{T'}`, so
`min In_{T'} = y_T b a^{-e}` with `e >= 0`, and `min Out_{T'} = y_T b a^{d_- - e}`.  The exponents are
`<= d_-`, and the cycle closes as in (i). ∎

*Proof of (iv): bottom in-ports, backward.*  Put `x_T = min In_T = z b` with `z in Out_{T'}`.  Then
`min Out_{T'} = z a^{-e}` with `e >= 0`, so `min In_{T'} = z a^{-e - d_-}` and `x_T = x_{T'} a^{e + d_-} b`.  The
exponents are `>= d_-`, and the cycle closes as in (ii). ∎

*Calibration.*
- In `F_2` there is no positive relation: `b a^{n_1} ... b a^{n_L}` has `b`-exponent sum `L >= 1`.  So no port
  configuration exists, and `u + w b` is regular in `k[F_2]`.  That is correct.
- In `Z × Z/2 = <a> × <b | b^2>`, `(1 - b)(1 + b) = 0`.  Lemma 1(a) applies verbatim to any group in which `a`
  has infinite order, giving offsets `(0, 0)`.  The relation `b a^0 b a^0 = 1` indeed holds there.

---

## 3. Every positive relation of `K` uses a line difference

**Lemma 3 (positive relation lemma).**  If `b a^{n_1} ... b a^{n_L} = 1` in `K` with `L >= 1`, then
`n_k in Delta` for some `k`.

*Proof.*  Suppose no `n_k` lies in `Delta`.  Since `0 in Delta`, every `n_k != 0`.
- So `W = b a^{n_1} ... b a^{n_L}` is a cyclically reduced normal form in `F`, with `|W|_* = 2L`.  It is nontrivial
  in `F` and trivial in `K`.
- In the cyclic word `W`, every syllable `a^{n_k}` sits between two occurrences of the syllable `b`.  When
  `L = 1` these are the same occurrence.

Let `D` be a minimal van Kampen diagram for `W` over `R`, and `D̃` the diagram obtained by deleting originating
edges.

**Standing reading of `D` (as in Steenbock's proofs of Theorems "gi" and "tf").**
- The boundary cycle of `D` reads the cyclic normal form `W`, each syllable subdivided into edges.
- Every face `M` of `D̃` is simply connected and lifts, together with its boundary cycle, to a reduced cycle
  `c_M` of `Gamma` (Lemma "Hilfssatz van Kampen" and the discussion preceding Theorem "lii").
- A subpath `s` of the boundary cycle of `M` lifts to a subpath `c_s` of `c_M` with `omega(c_s) = omega(s)` in
  `F`.
- A reduced cycle in a reduced labelling is backtrack-free.  So the letters along `c_s` form a freely reduced
  word.  Its normal form in `F` groups maximal runs of `a`-letters, all of one sign, and maximal runs of
  `b`-letters, again all of one sign.

**Claim A (reading a complete `b a^n b`).**  Let `M` be a face of `D̃` with a connected exterior arc `s`.
Suppose that either:
- `s` is the whole boundary cycle of `D` and `|omega(s)|_* >= 2`; or
- `s` is a proper subpath of the boundary cycle with `|omega(s)|_* >= 6`.

Then some `n_k` lies in `Delta`.

*Proof.*
- *The proper case.*  The label of `s` is a contiguous part of the cyclic normal form, possibly cutting into
  the first and last syllable.  So `omega(s) = x_0 sigma_1 ... sigma_r x_{r+1}` in normal form: the
  `sigma_j` are complete consecutive syllables of `W`, and `x_0`, `x_{r+1}` are partial syllables or empty.
  - Hence `|omega(s)|_* <= r + 2`, so `r >= 4`.
  - Four consecutive syllables of `W` alternate between `b` and some `a^{n}`, so they contain a complete
    `b a^{n_k} b`.
- *The whole-cycle case.*  Every syllable is complete, and `b a^{n_k} b` is read cyclically.
- *Reading off the lift.*  By uniqueness of normal forms, `c_s` reads the complete syllables along consecutive
  segments.
  - The segment reading `b` is a single `b`-edge traversed forward.  It is backtrack-free with all letters of
    one sign and product `b^1`.
  - The segment reading `a^{n_k}` is `|n_k|` consecutive `a`-edges of one sign, hence a monotone walk along one
    line `i`, from a position `p` to `p + n_k`.
  - The next segment is a `b`-edge traversed forward.
  - The first `b`-edge ends at `v_{ip}`, so `p in T_i`.  The second starts at `v_{i,p+n_k}`, so
    `p + n_k in S_i`.
  - Hence `n_k = (p + n_k) - p in Delta`.  (When `L = 1` and `s` is the whole cycle, the two `b`-edges are the
    same edge and the argument is unchanged.) ∎

**Case analysis on `D̃`.**  Every face `M` of `D̃` has `|omega(∂M)|_* >= gamma >= 9`, since its label is the label
of a cycle of `Gamma`.  Free product length is subadditive.
- *No face.*  Then `W = 1` in `F`, which is impossible.
- *One face `M`.*  The boundary label of `D` is weakly cyclically reduced, so `D̃` has no spurs.  Hence `∂M = ∂D`,
  and `s = ∂D` is a whole-cycle exterior arc with `|omega(s)|_* >= 9`.  Claim A applies.
- *Two faces `M_1`, `M_2`.*
  - Two faces of a simply connected planar diagram share at most one maximal arc `t`.  Two disjoint common arcs
    would enclose a region containing a third face.
  - `t` does not originate, so it is a piece and `|omega(t)|_* <= Lambda < gamma/8`.
  - The exterior boundary `s` of `M_1` is `∂M_1` minus `t`, which is connected.  So
    `|omega(s)|_* >= |omega(∂M_1)|_* - |omega(t)|_* > (7/8) gamma > 7`.
  - If `s` is all of `∂D`, Claim A applies in the whole-cycle case.  Otherwise it applies in the proper case.
- *More than two faces.*
  - The graphical small cancellation lemma gives an exterior face `M` whose exterior boundary `s` is connected,
    with `|omega(s)|_* > (1 - 3 lambda) |omega(∂M)|_* >= (5/8) · 9 > 5`, so `|omega(s)|_* >= 6`.
  - Again Claim A applies.

In every case some `n_k in Delta`, contradicting the assumption. ∎

*Remark on rigor.*  Lemma 3 uses Steenbock's diagram machinery exactly as his proofs of Theorems "gi" and "tf" do,
and as the landed `rips-segev-witness-supports-carry-no-zero-divisors-proof` does:
- the boundary cycle reads the normal form;
- faces of `D̃` lift to reduced cycles of `Gamma`.

The only new ingredient is Claim A: once an exterior arc has at least six syllables, it contains a complete
`b a^n b` block read on a line of `Gamma`.  A referee should check the lifting convention for faces whose
boundary meets `∂D`.

---

## 4. The theorem

**Theorem.**  Let `0 != u, w in k[<a>]`, `beta = u + w b`, `delta_+ = w_+ - u_+`, `delta_- = w_- - u_-`.  If
`delta_+ notin [Delta_-, Delta_+]` or `delta_- notin [Delta_-, Delta_+]`, then `alpha beta = 0` or
`beta alpha = 0` forces `alpha = 0`.

*Proof.*  Suppose `alpha != 0`.
- If `alpha beta = 0`, Lemma 1(a) gives a port configuration with offsets `(d_+, d_-) = (delta_+, delta_-)`.
- If `beta alpha = 0`, Lemma 1(c) gives one with `(d_+, d_-) = (delta_-, delta_+)`.

In both cases `{d_+, d_-} = {delta_+, delta_-}`, so some offset `d in {d_+, d_-}` lies outside
`[Delta_-, Delta_+]`.  Lemma 2 gives a positive relation whose exponents all lie outside `Delta`:
- `d = d_+ > Delta_+`: relation (i), all `n_k >= d_+ > Delta_+`;
- `d = d_+ < Delta_-`: relation (ii), all `n_k <= d_+ < Delta_-`;
- `d = d_- > Delta_+`: relation (iv), all `n_k >= d_- > Delta_+`;
- `d = d_- < Delta_-`: relation (iii), all `n_k <= d_- < Delta_-`.

In each case no `n_k` lies in `Delta ⊆ [Delta_-, Delta_+]`, contradicting Lemma 3. ∎

**Steenbock's explicit graphs.**  Here `S_i = {0, O_i1, O_i2, C_i}` and `T_i = {0, I_i1, I_i2, C_i}`, so
`C_i - 0` and `0 - C_i` lie in `Delta`, and `Delta_± = ±N` with `N = max_i C_i`.  The hypothesis reads
`max(|delta_+|, |delta_-|) > N`.

Example: `beta = 1 + a^{N+1} b` (so `delta_± = N + 1`) is regular.  So is `beta = (1 + a) + (a^{-N-1} + a^{N+1}) b`,
which has `delta_+ = N`, `delta_- = -N - 1`.

**Transfer to generalized Rips--Segev groups.**
- By `rips-segev-groups-embed-every-torsion-free-group-proof`, `G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2`, and `K`
  embeds in `G(Gamma)`.
- Let `G = ⊔_j t_j K` be the left coset decomposition.  For `alpha in k[G]` write `alpha = sum_j t_j alpha_j` with
  `alpha_j in k[K]`.
  - `alpha beta = sum_j t_j (alpha_j beta)`, with the summands supported in distinct cosets `t_j K`.  So
    `alpha beta = 0` forces every `alpha_j beta = 0`, hence every `alpha_j = 0`.
  - Using right cosets `K t_j` handles `beta alpha = 0` the same way.

So the theorem holds in `k[G(Gamma)]` for every choice of torsion-free factors `G_1 ∋ a`, `G_2 ∋ b` of infinite
order. ∎

---

## 5. What the method does not reach

**Balanced offsets.**
- When `delta_+, delta_- in [Delta_-, Delta_+]`, the four relations of Lemma 2 are all compatible with Lemma 3.
- For Steenbock's explicit graphs, the cycles of `Gamma` along the permutation of `x_2`-edges give positive
  relations with all exponents `C_i - I_i2 >= 99900`.  The `x_1`-edges give relations with all exponents
  `-I_i1 <= -10`.  So for `delta_± in [-10, 99900]` every walk conclusion is satisfiable by an actual relation.
- Balanced elements such as `1 + a + (1 + lambda a) b` need an argument using coefficients, not only supports.

**No malnormality or extremal-coset lemma is used.**
- The brief's route asked for an extremal coset with at most one `b`-neighbour.
- The companion node `rips-segev-port-data-cannot-exclude-balanced-divisors` shows that `Gamma` itself
  yields a port configuration in `K` with offsets `(0, 0)`.  So no argument from (P1), (P2) alone, extremal-coset
  counts included, can exclude `delta_+ = delta_- = 0`.
- The walk lemma replaces the extremal-coset step: it needs only the finiteness of `𝒞`.
