---
rg: 2
id: orbit-preserving-germ-corollary-rationality-proof
kind: route
title: Singular points are eventually periodic, germs normalizing the periodic shift commute with a power of it, and commuting germs are periodic prefix replacements
target: orbit-preserving-germ-corollary-extensions-of-v-are-rational
requires:
  - rational-homeomorphism-subgroups-have-exponential-wp
---

Notation as in the claim. Words are finite binary strings, `cone(c)` is the set
of points with prefix `c`, and `p|m` is the length-`m` prefix of `p`. An element
of `V` is a homeomorphism that, on each piece of a finite partition of `C` into
cones, acts as a prefix replacement `c y -> d y`.

**Step 0. Two compactness facts.**
- (C1) If `h ∈ Homeo(C)` agrees near every point of a clopen set `K` with some
  element of `V`, then `K` has a finite partition into cones on each of which `h`
  is a prefix replacement. Cover `K` by cones where `h` agrees with some `v`,
  refine each until `v` is a single prefix replacement on it, and take a finite
  subcover by disjoint cones.
- (C2) `sing(G)` is `G`-invariant. If `x ∉ sing(G)` and `g(x) = y ∈ sing(f)`, then
  `x ∈ sing(fg)`: otherwise `f = (fg) g^(-1)` would agree with an element of `V`
  near `y`, because `g^(-1)` does near `y` (the point `x` is not singular for `g`).
  So `g^(-1)(sing(G)) ⊆ sing(G)` for all `g`, hence equality.

  In particular (T) holds when `sing(G)` is a single `V`-orbit.

**Step 1. Singular points are eventually periodic.** Let `p` be a point that is
not eventually periodic, and `v ∈ Fix_V({p})`. Near `p`, `v` is a prefix
replacement `c y -> d y` with `c = p|m`, `d` a prefix of `p`. If `|d| ≠ |c|`, say
`|d| > |c|`, write `p = c y_0`. Then `d y_0 = c y_0`, so `d = c e` with `e` nonempty
and `y_0 = e y_0`, i.e. `y_0 = e^∞`, contradicting aperiodicity; `|d| < |c|` is
symmetric. So `d = c` and `v` is the identity on `cone(p|m)`. Hence
`Fix_V({p}) = ∪_m R_m`, with `R_m` the elements of `V` fixing `cone(p|m)`
pointwise.

The chain is strictly increasing. Let `b` be the complement of the bit `p_(m+1)`.
A nontrivial element of `V` supported in `cone((p|m) b)` lies in `R_(m+1)` but not
in `R_m`. A finitely generated subgroup of a strictly increasing union lies in
some term, so `Fix_V({p})` is not finitely generated. By (H2) every
`p ∈ sing(G)` is eventually periodic.

**Step 2. The `V`-germs at a periodic point.** Let `p = u w^∞` with `w` primitive,
`L = |w|`, and let `τ` be an element of `V` acting on `cone(u)` by `u y -> u w y`.
It fixes `p`. Write `τ_p` for its germ.

Let `v ∈ V` fix `p`, acting near `p` as `c y -> d y`, with `c, d` prefixes of `p`
of length at least `|u|`. Then `σ^(|c|) p = σ^(|d|) p`, where `σ` is the shift.
This is a periodic word of primitive period `L`, so `L` divides `|d| - |c| = kL`.

Write `c = u s`, with `s` a prefix of `w^∞`. Then `d = u w^k s`, since both are
prefixes of `p` of the right length. So `v` and `τ^k` agree on `cone(c)`, and
`(V)_p = <τ_p> ≅ Z`.

**Step 3. Germs commute with a power of `τ_p`.**
- *Choosing `N`.* If `<τ_p>` is normal in `(G)_p`, put `N = 1`. If it has finite
  index, its normal core has finite index in it; write the core as `<τ_p^N>`, which
  is normal. In both cases `h τ_p^N h^(-1) ∈ {τ_p^N, τ_p^(-N)}` for every
  `h ∈ (G)_p`.
- *Excluding the minus sign.* Put `C_k = cone(p|k)` for `k >= |u|`. Then
  `τ^N(C_k) = C_(k+NL)`, and `τ^(-N)(C_k) = C_(k-NL)` when `k >= |u| + NL`.
  Suppose `h τ_p^N h^(-1) = τ_p^(-N)`, let `g ∈ G` represent `h`, and put
  `f = g τ^N g^(-1)`.
  - Choose `m >= |u| + NL` with `f = τ^(-N)` on `C_m`.
  - Choose `m'` with `U := g(C_(m')) ⊆ C_m`, and `m''` with `C_(m'') ⊆ U`.
  - `f(U) = g(τ^N(C_(m'))) = g(C_(m'+NL)) ⊆ U`, so `f^j(C_(m'')) ⊆ U ⊆ C_m` for
    every `j >= 0`.
  - As `f = τ^(-N)` on `C_m`, induction gives `f^j(C_(m'')) = C_(m''-jNL)` as long
    as `m'' - (j-1)NL >= m`.
  - Let `j` be least with `m'' - jNL < m`. Then `C_(m''-jNL)` is a cone strictly
    containing `C_m`, yet `f^j(C_(m'')) ⊆ C_m`. Contradiction.

  So every `h ∈ (G)_p` commutes with `τ_p^N`.

**Step 4. A commuting germ is rational near `p`.** Let `g ∈ G` fix `p` with germ
commuting with `τ_p^N`. Choose `m >= |u|` with the following properties:
- `g τ^N = τ^N g` on `C_m`;
- `p` is the only singular point of `g` in `C_m`;
- `g(C_m) ⊆ cone(u)`.

The annulus `A = C_m \ C_(m+NL)` is clopen and contains no singular point of `g`.
By (C1), `A` is a disjoint union of cones `cone(u q_i)` on which `g` acts as
`u q_i y -> u r_i y`, finitely many `i`.

Every `x ∈ C_m \ {p}` is `τ^(Nk) z` for unique `k >= 0` and `z ∈ A`. Since
`τ^(Nj) z ∈ C_m` for `j <= k`, induction gives `g(x) = τ^(Nk) g(z)`, that is

    g(u w^(Nk) q_i y) = u w^(Nk) r_i y      for all k >= 0, all i, all y.

Write `p|m = u s_0`. Then `C_(m+NL) = cone(u w^N s_0)`, and after reading
`u w^(Nk)` the remaining input `r` lies in exactly one of `cone(w^N s_0)` or some
`cone(q_i)`, unless `r = w^∞`. So `g` is realized on `C_m` by a finite asynchronous
transducer:
- read and copy `u`;
- look ahead `max(NL + |s_0|, max_i |q_i|)` symbols;
- if the input begins with `w^N s_0`, copy the block `w^N` and repeat;
- if it begins with `q_i`, output `r_i` and copy the rest.

On `p` it copies forever, matching `g(p) = p`. Hence `g` is rational on `C_m`.

**Step 5. Every element is rational.** Let `g ∈ G`, with `sing(g) = {q_1, ..., q_s}`.
- By (T), `g(q_j) = v_j(q_j)` for some `v_j ∈ V`. Then `v_j^(-1) g` fixes `q_j`, and
  `q_j ∈ sing(G)`. Steps 1–4 apply at `q_j`, so `v_j^(-1) g` is rational on a
  cone `C^(j)` around `q_j`, and so is `g = v_j (v_j^(-1) g)`.
- On the clopen complement of the union of the `C^(j)` (shrunk to be disjoint),
  `g` has no singular points and is a finite prefix replacement by (C1).
- A homeomorphism that is rational on each piece of a finite clopen partition into
  cones is rational: select the piece with bounded lookahead, then run that
  piece's transducer.

So every element of `G`, and in particular every generator and its inverse, is
rational. `rational-homeomorphism-subgroups-have-exponential-wp` gives the
`2^(O(n))` word problem, and every subgroup inherits it by substituting
generators, so the class lies in `F(2^n)`.

**Scope.** Steps 1–2 use only (H2); Step 3 only (H3); Step 5 needs (T). Without
(T), Steps 3–4 still make every germ that *fixes* a singular point rational. A
transport `g(q) = q'` between different `V`-orbits only satisfies
`g τ_q^N = σ g` with `σ` rational, and `g` near `q` then applies the `k`-th
iterate of a fixed annulus map at depth `k`. That case is not covered.
