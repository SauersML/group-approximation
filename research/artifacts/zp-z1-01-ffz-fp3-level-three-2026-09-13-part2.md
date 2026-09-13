# Problem 1.1 at level three: the acyclic-host twisted container (part 2)

Lane z1-01-ffz-fp3, 2026-09-13. Part 1 quotes the source. This part records one candidate `F_3` host
for a universal finitely presented group. It escapes every trivial-coefficient obstruction proved so
far. Everything below is unreviewed.

**Update, same day: the candidate is refuted.** `K_ac(G)` is not `FP_3`, by
`split-edge-hnn-with-non-fp2-edge-is-not-fp3` (lane z1-01-ffz-fpinf, a9735c0298). See
`acyclic-host-twisted-rope-container-is-never-fp3`. In section (F4) below, the degree-one injectivity
fails.
- `H_1(N; W) = 0` because `N = P_0 × G` is finitely presented. So `H_1(A; W)` injects into
  `H_1(L; W_N)`.
- The `N`-cosets `Nk` have trivial `L`-stabilizer, since `Nak = Nk` forces `a ∈ N`. So `W_N` is free
  over `L`.
- The collapse `ZK → Z[N\K]` is a split sum map with free kernel. That kernel carries
  `H_1(L; Π_I ZL) ≠ 0`.

The paragraph in (F4) that speculates about "collapsing along p" is superseded by this computation.
Facts (F1)–(F3) still hold.

## Construction

1. Baumslag–Dyer–Miller (Topology 22 (1983); cited as [BDM, Theorem E] in arXiv:2607.21727v1): every
   recursively presented group embeds in a finitely presented acyclic group. Apply it to a universal
   finitely presented group `U`. This gives a finitely presented, integrally acyclic group `G ⊇ U`,
   itself universal. Fix a finite presentation `G = F/R`, `F` free on `x_1, …, x_k`, with `R` the
   normal closure of finitely many relators. Then `G` is infinite and `R ≠ 1`.
2. `L = F_1 *_R F_2` is finitely generated and recursively presented, since `R` is recursively
   enumerable. BDM again gives an embedding `ι_0: L → P_0` into a finitely presented acyclic group.
3. Vertex group `A = P_0 × L × G`. Edge maps `f_1(y) = (ι_0(y), 1, 1)` and `f_2(y) = (1, y, π(y))` for
   `y ∈ L`, where `π: L → G` kills `F_2`. Both are injective.
4. `K = K_ac(G)`: the HNN extension of `A` with stable letter `t` and `t f_1(y) t^{-1} = f_2(y)`.
   This is the twisted rope-trick container `Hig_{ι,ι'}(G)` over the host `P = P_0 × L`, with
   `ι = (ι_0, 1)` and `ι' = (1, id)`.

## (F1) K is finitely presented

Generators: a finite set `S_0` generating `P_0` (relations `Q_0`); letters `X^(1), X^(2)` for the
generators `x_i^(1), x_i^(2)` of the `L` factor; letters `Y = {y_i}` for the generators of `G` (finite
relators `Q_G`); and `t`. Relations of the candidate presentation `K''`:
`Q_0`, `Q_G`, `[S_0, X]`, `[S_0, Y]`, `[X, Y]`, and for each `i`,
`t u_i t^{-1} = x_i^(1) y_i` and `t v_i t^{-1} = x_i^(2)`. Here `u_i`, `v_i` are words in `S_0`
representing `ι_0(x_i^(1))`, `ι_0(x_i^(2))`.

Derivation of the infinitely many relations of the `L` factor. Let `r ∈ R`, written as a word in
the letters `x_i`.
- Conjugation by `t` is an automorphism, and the letters `X` commute with the letters `Y`. So
  `t r(u) t^{-1} = r(X^(1) Y) = r(X^(1)) r(Y)`.
- `r(Y) = 1` is a consequence of `Q_G`, since `R` is the normal closure of the relators.
- Likewise `t r(v) t^{-1} = r(X^(2))`.
- In `P_0` we have `ι_0(r^(1)) = ι_0(r^(2))`, which is a consequence of `Q_0`, so `r(u) = r(v)`.
- Hence `r(X^(1)) = r(X^(2))` in `K''`, and the letters `X` generate a quotient of `L`.

Every defining relation of `K` then holds in `K''`: the relations of `P_0`, `L` and `G`; the
commutation relations between the factors, where generators suffice; and the HNN relations, where
generators of `L` suffice. The obvious maps are inverse isomorphisms. So `K ≅ K''` is finitely
presented, although the vertex group `A` is not.

## (F2) K contains G, hence U, hence every finitely presented group

`G` is a factor of the vertex group, and vertex groups embed in HNN extensions.

## (F3) K is an integral homology circle

- `P_0` and `G` are integrally acyclic, so the projection `p: A → L` induces
  `H_*(A; Z) ≅ H_*(L; Z)` (Künneth; the Tor terms vanish because an acyclic factor has homology `Z` in
  degree 0).
- `H_k(L; Z) = 0` for `k ≥ 3`: in Mayer–Vietoris for the amalgam `F_1 *_R F_2`, the free groups
  `F_i, R` have no homology above degree 1.
- `p ∘ f_1` is trivial, so `H_k(f_1) = 0` for `k ≥ 1`. `p ∘ f_2 = id_L`, so `H_k(f_2)` is an
  isomorphism.
- In the HNN Mayer–Vietoris sequence `… → H_k(L) --α_k--> H_k(A) → H_k(K) → H_{k−1}(L) --α_{k−1}--> …`
  with `α_k = H_k(f_1) − H_k(f_2)`, every `α_k` with `k ≥ 1` is an isomorphism, and `α_0 = 0`.

Therefore `H_1(K; Z) ≅ Z` (the stable letter) and `H_k(K; Z) = 0` for `k ≥ 2`.

Consequences.
- `fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3` does not apply: the vertex group `A` has
  infinite rational `H_2`, namely `H_2(L; Q)`.
- `twisted-rope-trick-container-is-not-fp3-over-fp2-hosts` does not apply either: `H_2(ι) = 0` and
  `H_2(ι')` is injective, so the subspace `V` there is `0`.
- No trivial-coefficient homology obstruction remains in any degree.

## (F4) What FP_3 means here: product coefficients

`K` is finitely presented. A finitely presented group `K` is of type `FP_3` iff `H_2(K; Π_I ZK) = 0`
for every index set `I`. This is the Bieri–Eckmann direct-product criterion (Bieri, *Homological
dimension of discrete groups*, §1; to be checked from the source before any node relies on it).
Write `W = Π_I ZK`. The Mayer–Vietoris sequence with coefficients `W` gives

    H_2(L; W) --α^W_2--> H_2(A; W) → H_2(K; W) → H_1(L; W) --α^W_1--> H_1(A; W).

So `K` is of type `FP_3` iff `α^W_2` is surjective and `α^W_1` is injective, for every `I`.

- `f_1` factors through `P_0`. The restriction of `W` to `P_0` is a product of free modules. `P_0` is
  finitely presented, hence of type `FP_2`, so `H_1(P_0; W) = 0`. Hence `H_1(f_1; W) = 0` and
  `α^W_1 = −H_1(f_2; W)`.
- Injectivity of `H_1(f_2; W)`. There is a retraction `p: A → L` with `p ∘ f_2 = id`. But `W` is
  restricted from `K`, not pulled back along `p`. Collapsing along `p` identifies the free `L`-module
  summands of one `A`-coset, so a left inverse exists only up to that collapse. Classes supported on
  differences across the `L`-cosets of one `A`-coset are not controlled. Open.
- Surjectivity of `α^W_2`. `H_2(A; W)` may contain the level-2 product defects of `P_0` and `G`, which
  exist when these groups are not of type `FP_3`. `H_2(f_1)` can reach the `P_0` part only through
  `H_2(ι_0; W)`, and `H_2(f_2)` reaches the `G` part only through `H_2(π; W)`. A double has
  cohomological dimension 2 and carries no "identities among relations", so covering the defect of a
  non-`FP_3` group `G` through `π` looks doubtful. Neither direction is settled.
- Circularity check. If `P_0` could be chosen of type `FP_3`, the `P_0` part of the defect vanishes.
  But an `FP_3` host of `L` is not obviously easier to find than one of `U`, since `L` is a finitely
  generated recursively presented group and so embeds in `U`. `G` must contain `U`; whether some
  universal finitely presented group is of type `FP_3` is exactly the open question.

## Lane z1-01-embed-pos, preliminary

That lane reports that a related variant fails on product coefficients: edge `L' → G` with `FP_∞`
kernel over an acyclic `FP_∞` host `P`, where `ι × 1` factors through `P`. The present container
differs in one way: the host contains `L` itself as a factor, and `ι'` lands there, so `f_2` carries
the whole `L`-defect. The next computation is `H_1(L; W) → H_1(A; W)` for `W = Π_N ZK`, where the
defect of `L` is the unbounded use of the relators `r^(1)(r^(2))^{-1}`.
