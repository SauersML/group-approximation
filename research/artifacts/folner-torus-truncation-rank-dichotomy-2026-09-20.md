# Følner truncations of torus automata: exact rank or linear loss

Agent swarm-0917-w21-w21-gs-break, 2026-09-20. Calibration of
`local-rectangular-small-fibre-maps-lose-proportional-rank` (LRSF) on the instances that a group
produces from its own finite subsets.

## 0. Conventions

As in `research/artifacts/lef-torus-small-fibre-2026-09-18.md`, Section 1 and Lemmas A, B.
- `X_d = (T^d)^G`, shift `(h x)_g = x_(h^-1 g)`, `tau(x)_g = mu(g^-1 x)` with `mu = ev_1 o tau`.
- `H^1(X_d) = Z[G]^d` (row vectors), basis `e_(g,a) = g e_a`, and `tau^*(xi) = xi D`.
- Lemma A gives a finite `W` with `1 in W` and `eta > 0`: `eta`-closeness of `tau(x), tau(y)` on `W`
  forces `rho(x_1, y_1) < 1/16`.
- Lemma B (with `eps_1 = eta/3`) gives a finite `F` with `1 in F`, `supp D <= F`, and
  `mu': (T^d)^F -> T^d` within `eta/3` of `mu`, of the same degree data.
- Pairing on finitely supported vectors: `<x, y> = sum_g x(g) . y(g)` (dot product in `Q^d`).
- Involution: `D^*(m) = D(m^-1)^T`. For row vectors, `v D^* = 0` iff `D v^* = 0` (column form), so the
  left annihilator of `D^*` is the right annihilator of `D`.
- `D` is *left-regular* if `xi D = 0` forces `xi = 0` for `xi in Q[G]^d`; this is C2
  (`injective-torus-automata-have-regular-degree`, as used in
  `sofic-torus-c2-reduces-to-rectangular-small-fibres`, item 2). *Right-regular*: `v D^* = 0` forces `v = 0`.

## 1. The truncation of `tau` to a finite set

For finite `E <= G` put `J(E) = E F^-1 ∪ E W` and define
`g_E: (T^d)^E -> (T^d)^(J(E))`, `g_E(u)_j = mu'((x_(jf))_(f in F))` where `x = u ∪ 0` (extend by `0`
off `E`).

**Lemma 1.1 (it is an LRSF instance).** With `K = max(|F|, |W|)`, `g_E` is `(K, eta/3)`-local
rectangular:
- (L) output `j` reads only the inputs in `jF ∩ E`;
- (C) input `i` is controlled by `C_i = iW <= J(E)`.

*Proof.* (L) is the definition. For (C), let `u, u'` have `g_E(u), g_E(u')` `eta/3`-close on `iW`,
and put `x = u ∪ 0`, `x' = u' ∪ 0`. By Lemma B, `tau(x)_(iw)` is within `eta/3` of `g_E(u)_(iw)`, and
likewise for `x'`. So `tau(x), tau(x')` are `eta`-close on `iW`, i.e. `tau(i^-1 x), tau(i^-1 x')` are
`eta`-close on `W`. Lemma A gives `rho(x_i, x'_i) < 1/16`. QED.

**Lemma 1.2 (its `H^1` map).** For `xi in Z^(dJ(E)) <= Z[G]^d`,
`g_E^*(xi) = res_E(xi D)`, where `res_E` keeps the coordinates at sites of `E`.

*Proof.* `g_E^*(e_(j,a))` is the class of `u -> mu'((x_(jf))_f)_a`. By Lemma B that is
`sum_(f, b : jf in E) c_(a,f,b) e_(jf,b)`, which is `res_E(j . row_a(D)) = res_E(e_(j,a) D)`. QED.

## 2. The exact rank identity (every group)

**Proposition 2.1.** For every group `G`, every `tau` as above and every finite `E <= G`,

`rank g_E^* = d|E| - dim_Q A(E)`,  where  `A(E) = { v in Q[G]^d : supp v <= E, v D^* = 0 }`.

In particular, if `D` is right-regular, every truncation `g_E` has exactly full rank `d|E|`.

*Proof.* By Lemma 1.2, `rank g_E^*` is the rank of `M_E: Q^(dJ) -> Q^(dE)`, `xi -> res_E(xi D)`,
with `J = J(E)`. Compute its transpose with the pairing. For `xi` supported in `J` and `v` in `E`:

`<res_E(xi D), v> = <xi D, v> = sum_h sum_(km = h) xi(k) D(m) . v(h) = sum_k xi(k) . (v D^*)(k)`,

because `(v D^*)(k) = sum_m v(km) D(m)^T`. The vector `v D^*` is supported in `E F^-1 <= J`, so the
transpose is `M_E^T: Q^(dE) -> Q^(dJ)`, `v -> v D^*`, with no truncation. Hence
`rank M_E = rank M_E^T = d|E| - dim ker M_E^T = d|E| - dim A(E)`. QED.

*Remark.* No hypothesis on `G` is used, and injectivity of `tau` enters only through Lemma 1.1.
The rank of a truncation of the group itself is decided by an exact finite annihilator of `D` on
the *right*. C2 is regularity on the *left*.

## 3. The amenable dichotomy

Call `(E_n)` *right-Følner* if `|E_n s \ E_n| = o(|E_n|)` for every `s in G`. Inverses of a left
Følner sequence are right-Følner, so every countable amenable group has one. Along it
`|J(E_n) \ E_n| = o(|E_n|)`: the surplus of `g_(E_n)` is `o(|E_n|)`, which is the LRSF regime.

**Lemma 3.1 (translates).** Let `(E_n)` be right-Følner and `Sigma <= G` finite and nonempty. There
are `P_n <= G` with `|P_n| >= |E_n| / |Sigma Sigma^-1| - o(|E_n|)` such that the sets `g Sigma`
(`g in P_n`) are pairwise disjoint and contained in `E_n`.

*Proof.* `{g : g Sigma <= E_n} = ∩_(s in Sigma) E_n s^-1`, and
`|E_n \ E_n s^-1| = |E_n s \ E_n| = o(|E_n|)`, so this set has `|E_n| - o(|E_n|)` elements. Choose a
maximal subfamily with disjoint translates. Each chosen `g` excludes only `g' in g Sigma Sigma^-1`.
QED.

**Theorem 3.2.** Let `G` be amenable, `tau` as above, and `(E_n)` right-Følner. The following are
equivalent:
1. C2 for `tau`: `D` is left-regular.
2. `D` is right-regular.
3. `rank g_E^* = d|E|` for every finite `E <= G`.
4. `rank g_(E_n)^* / (d|E_n|) -> 1`.

If they fail, there is `c > 0`, depending only on `tau`, with
`rank g_(E_n)^* <= d|E_n| - c|E_n| + o(|E_n|)` along every right-Følner sequence.

*Proof.*
- (2 => 3) is Proposition 2.1. (3 => 4) is trivial.
- (4 => 1). Suppose `xi D = 0` with `0 != xi`, `Sigma = supp xi`. Apply Lemma 3.1 to `J_n = J(E_n)`,
  which is right-Følner as well, since `|J_n \ E_n| = o(|E_n|)`. The vectors `g xi` (`g in P_n`) are
  supported in `J_n`, satisfy `(g xi) D = g (xi D) = 0`, so lie in `ker M_(E_n)`, and are linearly
  independent (disjoint nonempty supports). So
  `rank g_(E_n)^* <= d|J_n| - |P_n| <= d|E_n| - |E_n| / |Sigma Sigma^-1| + o(|E_n|)`,
  contradicting 4.
- (1 => 2). Assume 1. The map `xi -> xi D` is injective on `Q^(dJ_n)`, with image supported in
  `J_n F`. Restricting to `E_n` kills at most `d|J_n F \ E_n|` dimensions, and
  `J_n F <= E_n (F^-1 ∪ W) F`, so `|J_n F \ E_n| = o(|E_n|)`. Hence
  `rank g_(E_n)^* >= d|J_n| - o(|E_n|) >= d|E_n| - o(|E_n|)`. Now suppose `v D^* = 0` with `0 != v`,
  `Upsilon = supp v`. Lemma 3.1 in `E_n` gives independent vectors `g v in A(E_n)`, since
  `(g v) D^* = g (v D^*) = 0`. So `dim A(E_n) >= |E_n| / |Upsilon Upsilon^-1| - o(|E_n|)`, and
  Proposition 2.1 gives `rank g_(E_n)^* <= d|E_n| - |E_n|/|Upsilon Upsilon^-1| + o(|E_n|)`. That
  contradicts the lower bound, so `D` is right-regular.
- The last sentence is the bound in (4 => 1), with `c = 1/|Sigma Sigma^-1|` for any left witness
  `Sigma` (which exists when 1 fails; by (1 <=> 2) the two witnesses exist together). QED.

The equivalence (1 <=> 2) is the matrix version of the familiar fact that one-sided and two-sided
zero divisors agree in amenable group rings. The proof here uses only counting in Følner sets.
For uncountable `G` replace sequences by Følner nets; nothing else changes.

## 4. What this says about LRSF

1. **Følner instances are a 0/1 test.** On the instances `g_(E_n)` an amenable group produces, the
   rank is either exactly `d|E_n|` for every `E` (with the surplus `|J| - |E|` not even used), or it
   loses a fixed proportion `c|E_n|` while the surplus is `o(|E_n|)`. There is no intermediate
   regime. So these instances cannot probe `beta(K, d, eta, delta)` or the constant `C(K, d, eta)` of
   the linear form. They can only confirm or refute C2 for the host.
2. **They are the target, not a test.** The LRSF node lists "the rectangular maps that Følner sets
   produce for amenable groups that are not LEF" as a first test case. By Theorem 3.2, LRSF on those
   instances is equivalent to C2 over that group, which is open for amenable non-LEF groups with
   torsion (`injective-torus-automata-have-regular-degree`, w10 and w13 entries). Every proof of LRSF
   proves amenable C2, and a counterexample to amenable C2 is a counterexample to LRSF, with
   `delta < c` fixed and `beta -> 0`.
3. **Amenable C2 is a statement about exact right annihilators.** By Proposition 2.1 and
   Theorem 3.2, over an amenable group C2 fails for `tau` iff some nonzero finitely supported `v`
   has `v D^* = 0`, i.e. `D v^* = 0`: a right annihilator, not the left one C2 names. Rank defects of
   truncations never come from approximation. They come only from this exact finite object.
4. **Where LRSF's quantitative content lives.** Over amenable groups LRSF is used only in the
   qualitative form 4 of Theorem 3.2, on Følner instances. The proportional form with a uniform
   `beta(K, d, eta, delta)` is needed only for sofic models of non-amenable groups, where the frozen
   vertices of `sofic-torus-c2-reduces-to-rectangular-small-fibres` make genuinely non-exact
   rectangular maps. A test of the quantitative statement must use such models, or group-free
   instances. Truncations are no test either when `F ∪ W` generates a non-amenable subgroup `H`:
   splitting `E` along left cosets of `H` and applying Følner's criterion in each coset gives a
   surplus of at least a fixed proportion of `|E|`, outside the regime.
5. **Invariant and dying step for the "test on Følner sets" approach.** The invariant is
   `dim A(E)`, the exact finite right-annihilator space of `D` inside `E`. The approach dies at the
   step "check LRSF on Følner instances of a candidate host": that step is already the open problem
   C2 on that host, and it gives no information on `beta`.

## 5. Remark: square subfamilies (Hall-type restriction)

This remark is recorded for completeness and is not part of the claim.

For any `(K, eta)`-local rectangular `g: (T^d)^I -> (T^d)^J` and `T <= I`, put `N(T) = ∪_(i in T) C_i`.
- Freeze the inputs off `T` at `0` and keep the outputs in `N(T)`. The result
  `h_T: (T^d)^T -> (T^d)^(N(T))` has fibres of sup-diameter `<= 1/16`.
- Padding the target with constant coordinates and applying [LEF] Theorem 1 shows `|N(T)| >= |T|`.
- If `|N(T)| = |T|`, Theorem 1 makes `h_T^*` bijective. Since `h_T^* = iota_T^* g^* pi_(N(T))^*`,
  this gives `rank g^* >= d|T|`.

So `rank g^* >= d max{ |T| : |N(T)| = |T| }`. On truncations of an infinite group with `W`
generating an infinite subgroup, `|TW| > |T|` for every nonempty finite `T`, so the bound is
empty there. That is the expected failure of every square-restriction approach to LRSF: control
graphs of the relevant instances have no square subfamily at all.
