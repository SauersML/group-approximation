# Sofic-radical localization of Bernoulli entropy deficit witnesses

Lane `gk-rokhlin`, 2026-09-12. This supports the Cairn claims
`sofic-radical-localizes-bernoulli-deficit-witnesses` and
`bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`. The proofs are handwritten, with no
computation.

## Summary

* **Theorem 1.** A finite configuration with an entropy deficit has two points that differ by a
  sofic-invisible element of the subgroup it generates.
* **Corollaries 2–4.**
  * Sofic groups are Rokhlin-maximal at every alphabet size, by a direct count.
  * A deficit proves nonsoficity.
  * Witnesses fold inside the kernel of every homomorphism to a sofic group, so over a Kun–Thom
    wreath they fold on lamps.
  * On a simple nonsofic host the theorem constrains only the generated subgroup.
* **Proposition 5.** Maximality for every countable group reduces to finitely generated infinite
  simple Kazhdan groups.

## 0. Conventions

* `G` is a countable group, `A` a finite alphabet with `|A| = q >= 2`, and `k >= 1`. The field
  `x = (x(g))_(g in G)` is iid uniform on `A^k`.
* A *configuration* `(k, E, F, psi)` consists of finite sets `E, F` in `G` and a function `psi`
  from `(A^k)^E` to a finite set `R`. Put

  ```text
  U_f = psi( (x(f e))_(e in E) )      (f in F),
  Phi(k, E, F, psi) = (1/k) [ H(psi(x|_E)) + H( x(1) | (U_f)_(f in F) ) ].
  ```

  A *witness* is a configuration with `Phi < log q`. By Theorem 3 of
  `research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md`, `G` has a witness at `q`
  exactly when `h^Rok_G((A^k)^G) < k log q` for some `k`.
* `P = FE ∪ {1}` is the point set, `D = { p^-1 p' : p != p' in P }` is the difference set, and
  `K = <E ∪ F>`. Every quantity in `Phi` is a function of `(x(p))_(p in P)`.
* Models and the sofic radical are as in Section 0 of
  `research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md`.
  * For a finite `F'` in `K` containing `1`, an `(F', delta)`-model of `K` is a finite set `V`
    with `phi: F' -> Sym(V)` such that `phi(1) = id` and `d(phi(a) phi(b), phi(ab)) <= delta`
    whenever `a, b, ab` lie in `F'`. Here `d` is normalized Hamming distance.
  * `v.a := phi(a)^-1 (v)`. This is a right action up to defect.
  * `Rad(K)` is the set of `g` with the following property: for every `eps > 0` there are a
    finite `F'` containing `g` and a `delta > 0` such that `d(phi(g), id) <= eps` in every
    `(F', delta)`-model.

  Restricting models of `G` to finite subsets of `K` gives models of `K`, so `Rad(K) <= Rad(G)`.

## 1. The localization theorem

**Theorem 1.** If `Phi(k, E, F, psi) < log q`, then `D` meets `Rad(K)`.

*Proof.* Suppose `D` misses `Rad(K)`. We show `Phi >= log q`.

*Degenerate cases.*
* If `F` is empty, then `Phi = (1/k)[H(psi(x|_E)) + k log q] >= log q`.
* If `D` is empty, then `P = {1}`. So `E = {e}`, `F = {e^-1}` and `U = psi(x(1))`. Since
  `H(psi(x|_E)) = H(psi(x(1)))`,
  `k Phi = H(psi(x(1))) + H(x(1) | psi(x(1))) = H(x(1)) = k log q`.

So assume `F` and `D` are nonempty. For `f in F` and `e != e'` in `E`,
`(f e)^-1 (f e') = e^-1 e'`, so `E^-1 E` minus `{1}` lies in `D`.

Let `F'` be a finite subset of `K` containing `1`, `E`, `F`, `P` and `D`. It then contains the
factors and products used below: `f, e, fe`; `p, p^-1 p', p'`; and `e, e^-1 e', e'`.

**Step 1: separating models.** No `d in D` lies in `Rad(K)`. So there is `eps_d > 0` such that for
every `delta > 0` some `(F', delta)`-model moves `d` at a fraction greater than `eps_d`. Put
`eps_0 = min_d eps_d` and fix `delta > 0`.
* Choose such a model for each `d in D`, replicate the models to a common cardinality, and take the
  disjoint union `V'`. This is an `(F', delta)`-model in which every `phi(d)`, `d in D`, moves a
  fraction greater than `eps_0/|D|`.
* The `r`-fold product `V = V'^r`, with coordinatewise maps, is an `(F', r delta)`-model, since
  `d(pi^(xr), pi'^(xr)) <= r d(pi, pi')`. A point is fixed only when every coordinate is fixed, so
  each `phi(d)` fixes at most a fraction `theta_r = (1 - eps_0/|D|)^r`.

**Step 2: good points.** Let `W` be the set of `v in V` with `(v.a).b = v.(ab)` for all `a, b` in
`F'` with `ab in F'`. For one pair `(a, b)`, the failures are the points `v = phi(ab) w` with
`phi(ab) w != phi(a) phi(b) w`, a fraction at most `r delta`. So `|V \ W| <= beta |V|`, with
`beta = |F'|^2 r delta`.

1. Let `v in W` and `p != p'` in `P`, and put `d = p^-1 p'`. Then `v.p' = (v.p).d`, so
   `v.p = v.p'` exactly when `v.p` is fixed by `phi(d)`. Since `v -> v.p` is a bijection, at most
   `theta_r |V|` points `v` have this. So the set `U_P` of `v in W` whose chart `p -> v.p` is
   injective on `P` satisfies `|V \ U_P| <= (beta + |P|^2 theta_r) |V|`.
2. In the same way, the set `U_E` of `u in W` with `e -> u.e` injective on `E` satisfies
   `|V \ U_E| <= (beta + |E|^2 theta_r) |V|`.

**Step 3: the count.** Let `x in (A^k)^V` be iid uniform, and put

```text
Z_u = psi( (x(u.e))_(e in E) )   (u in V),        Z = (Z_u)_(u in V).
```

Since `Z` is a function of `x`,

```text
k |V| log q = H(x) = H(Z) + H(x | Z).
```

* *The code.* For `u in U_E` the tuple `(x(u.e))_e` is iid uniform on `(A^k)^E`, so
  `H(Z_u) = H(psi(x|_E))`. For every other `u`, `H(Z_u) <= log |R|`. Hence

  ```text
  H(Z) <= sum_u H(Z_u) <= |V| H(psi(x|_E)) + (beta + |E|^2 theta_r) |V| log |R|.
  ```

* *The decoding.* We have
  `H(x | Z) <= sum_v H(x(v) | Z) <= sum_v H( x(v) | (Z_(v.f))_(f in F) )`. Let `v in U_P`.
  * Since `v in W`, `(v.f).e = v.(fe)`, so `Z_(v.f) = psi((x(v.(fe)))_e)`.
  * Since `phi(1) = id`, `v.1 = v`.
  * The chart is injective on `P`, so `(x(v.p))_(p in P)` is iid uniform. The pair
    `(x(v), (Z_(v.f))_f)` is the same function of it as `(x(1), (U_f)_f)` is of
    `(x(p))_(p in P)` in `G`.

  So `H(x(v) | (Z_(v.f))_f) = H(x(1) | (U_f)_f)`. Every other term is at most `k log q`. Hence

  ```text
  H(x | Z) <= |V| H( x(1) | (U_f)_f ) + (beta + |P|^2 theta_r) |V| k log q.
  ```

Dividing by `k |V|` gives

```text
log q <= Phi + (beta + |E|^2 theta_r) (log |R|)/k + (beta + |P|^2 theta_r) log q.
```

Here `eps_0`, `|D|`, `|E|` and `|P|` are fixed. So `theta_r -> 0` as `r -> infinity`, and for
fixed `r`, `beta -> 0` as `delta -> 0`. Hence `log q <= Phi`. QED.

*Remark.* The Garden-of-Eden count (`sofic-radical-localizes-garden-of-eden-windows`) needs
injective charts only on a positive fraction of points. The entropy count needs them on all but a
vanishing fraction, and the product amplification supplies that.

**Corollary 2 (sofic groups, and nonsoficity).**
1. Every sofic group is Rokhlin-maximal at every `q`: `h^Rok_G((A^k)^G) = k log q` for all `k`.
2. If `h^Rok_G((A^k)^G) < k log q` for some `k`, then the subgroup generated by some witness is
   nonsofic, and so is `G`. For example, a deficit over Thompson's `V` would prove `V` nonsofic.

*Proof.*
1. Subgroups of sofic groups are sofic, so `Rad(K) = 1`, and by Theorem 1 no witness exists. The
   lower-bound half of Theorem 3 of the route artifact, applied at each `k`, gives
   `inf Phi <= h^Rok_G((A^k)^G)/k`. Also `h^Rok_G((A^k)^G) <= k log q` always.
2. Take a witness (Theorem 3) and apply Theorem 1. A countable group with `Rad(K) != 1` is
   nonsofic, by Lemma 1 of the Garden-of-Eden artifact. QED.

This recovers without sofic entropy the fact that uniform Bernoulli shifts over sofic groups have
maximal Rokhlin entropy.

**Corollary 3 (sofic quotients).** If `pi: G -> M` is a homomorphism to a sofic group, then
`Rad(G) <= ker pi`. So every witness over `G` has two points `p != p'` in `P` with
`p^-1 p' in Rad(K) <= K ∩ ker pi`.

*Proof.* Suppose `pi(g) != 1`. Composing sofic approximations of `M` with `pi` gives models of `G`
on any finite set, with defect as small as desired, that move `g` at a fraction near `1`. QED.

*Kun–Thom wreaths.* For `W = (Z/2) wr_(G/Gamma) G` with `G` residually finite, the quotient
`W -> G` is sofic. So every witness over `W` has two points in one coset of the lamp subgroup, and
they differ by a sofic-invisible lamp configuration. Theorem 1 does not exclude such a witness, and
INF for these groups remains open.

**Corollary 4 (simple nonsofic hosts).** If `G` is simple and nonsofic, then `Rad(G) = G`, because
`Rad(G)` is a nontrivial normal subgroup. Theorem 1 then asks only that `K` be nonsofic. The binary
Leavitt unit group is such a host (`leavitt-unit-group-has-only-trivial-sofic-morphisms`).

**Relation to strict automata.** Theorem 1 of the route artifact turns a strict automaton into a
witness. So a strict automaton is folded twice: on its Garden-of-Eden window, and on the point set
of the witness it produces.

## 2. INF on simple Kazhdan hosts

**Proposition 5.** Fix `q >= 2`. If every finitely generated infinite simple group with property
(T) is Rokhlin-maximal at `q`, then every countably infinite group is Rokhlin-maximal at `q`.

*Proof.* Every countable group `C` embeds in a finitely generated infinite simple Kazhdan group `G`
(`countable-group-embeds-in-fg-simple-kazhdan-group`). Part 1 of
`bernoulli-rokhlin-maximality-passes-to-subgroups` passes maximality from `G` to `C`. QED.

The converse is specialization, so `bernoulli-rokhlin-entropy-maximal-for-every-group` is
equivalent to its restriction to this class. By Corollary 4, the localization constrains no
nonsofic host in the class, so a lower bound there needs a mechanism other than finite models.
