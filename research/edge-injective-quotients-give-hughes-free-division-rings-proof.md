---
rg: 2
id: edge-injective-quotients-give-hughes-free-division-rings-proof
kind: route
title: The kernel of an edge-injective map acts on the Bass-Serre tree with trivial edge stabilizers, so it is a free product of groups in H; one map to Z per step then climbs Magnus root towers, and Higman's perfect amalgam shows the edge hypothesis is needed
target: edge-injective-quotients-give-hughes-free-division-rings
requires:
  - vertex-injective-quotients-give-hughes-free-division-rings
  - hughes-extension-lemma-and-fsp-universal-field-imports
  - hughes-free-division-rings-pass-to-directed-unions
  - higman-bs-amalgam-has-hughes-free-division-rings
  - higman-group-splits-as-amalgams-over-free-subgroups
---

## Inputs

- **(C)** `𝓗` is closed under subgroups, extensions, directed unions and free products (of any family, as a
  directed union of finite free products). It contains free groups and locally indicable amenable groups. These
  are items 1 and 4 of [[vertex-injective-quotients-give-hughes-free-division-rings]].
- **(R)** Retract criterion: if `B ∈ 𝓗` retracts onto `A` or onto `θ(A)`, then `B *_θ ∈ 𝓗` (item 6 there).
- **(L)** Every HFE group is locally indicable, by the definition in
  [[hughes-extension-lemma-and-fsp-universal-field-imports]].
- **(BS)** Bass–Serre theory: a group acting on a tree without inversions, with trivial edge stabilizers, is the
  free product of a set of representatives of its vertex stabilizers and a free group.
- **(M)** Magnus–Moldavanskii: Freiheitssatz, and the Magnus splitting of a one-relator group with an
  exponent-zero generator as an HNN extension of a one-relator group over Magnus (free) subgroups. The kernel of
  the exponent map is the directed union of the finite segment groups. See Lyndon–Schupp, Ch. IV.5, and
  Moldavanskii (1967).

## Item 1: the edge-injective quotient lemma

Let `T` be the Bass–Serre tree of the splitting and `K = ker φ`. The stabilizer in `G` of an edge of `T` is a
conjugate `gG_eg^{-1}`. Since `φ` is injective on `G_e`, it is injective on each conjugate. So
`K ∩ gG_eg^{-1} = 1`, and `K` acts on `T` with trivial edge stabilizers. By (BS),
`K = (*_i K ∩ g_iG_{v_i}g_i^{-1}) * F`, with `F` free. Each factor is a subgroup of a conjugate of some
`G_v ∈ 𝓗`, so it lies in `𝓗`. By (C), `K ∈ 𝓗`. The image `φ(G) ≤ Q` lies in `𝓗` by (C). So `G`, an extension of
`K` by `φ(G)`, lies in `𝓗` by (C). The converse takes `φ = id`, which is injective on everything. When `φ` is
injective on vertex groups, the vertex stabilizers of `K` are trivial too and `K` is free. That is item 2 of
[[vertex-injective-quotients-give-hughes-free-division-rings]]. ∎

## Item 2: cyclic edge groups

Put `p = f(a)` and `q = f(c)`, both nonzero, and `Q = Z[1/pq] ⋊ Z`, with the generator `τ` of `Z` acting by
multiplication by the unit `q/p`. `Q` is torsion-free metabelian and locally indicable: every finitely generated
subgroup lies in `Z[1/pq]`, or maps nontrivially to `Z`. So `Q ∈ 𝓗` by (C). Define `φ(b) = (f(b), 0)` for
`b ∈ B` and `φ(t) = τ`, where the semidirect product is formed so that `τ^{-1} (x,0) τ = ((q/p)x, 0)`. Then
`φ(t)^{-1} φ(a) φ(t) = ((q/p)p, 0) = (q, 0) = φ(c)`. So `φ` respects the HNN relation `t^{-1} a t = c`, and it
is a homomorphism. On the edge group `<a>` it is `a^n ↦ np`, which is injective, and likewise on `<c>`. Item 1
gives `G ∈ 𝓗`.

- **`BS(p,q)`.** Take `B = <x> ≅ Z`, `a = x^p`, `c = x^q` and `f = id`.
- **Span one.** Let `G = <a,t | w(a, t^{-1}at)>` with `w` involving both letters. Magnus gives
  `G = B *_{a_0 ↦ a_1}`, where `B = <a_0, a_1 | w(a_0,a_1)>`. The cyclic edge groups `<a_0>` and `<a_1>` are
  infinite, by the Freiheitssatz. Let `e_0, e_1` be the exponent sums.
  - If `e_0 e_1 ≠ 0`, then `f(a_0) = e_1`, `f(a_1) = -e_0` kills `w`, so `f` is well defined and satisfies the
    hypothesis.
  - If `e_0 = 0`, then `a_1 ↦ 1` sends `w` to `a_0^{e_0} = 1`. This is a retraction of `B` onto `<a_0>`, and
    (R) applies. The case `e_1 = 0` is symmetric.
  - So `B ∈ 𝓗` implies `G ∈ 𝓗`. The converse holds because `B ≤ G` and (C). ∎

## Item 3: root adjunction

Since `f(g) ≠ 0`, `g` has infinite order, so `P *_{g = s^k} <s>` is an honest amalgam of `P` and `Z` over
`Z`. Define `φ = k·f` on `P` and `φ(s) = f(g)`. Then `φ(s^k) = k f(g) = φ(g)`, so `φ: P *_{g=s^k} <s> -> Z` is
well defined. It is injective on the edge group `<g>`, since `φ(g^n) = nk f(g)`. The vertex groups `P` and `Z`
lie in `𝓗`. Item 1 applies.

For the root rule, `<X, b | w> = <X, s, b | w_k(X, s), s = b^k>`. Here `Hom(<X,s | w_k>, Z)` is the set of
integer vectors orthogonal to the exponent vector of `w_k`. It contains an `f` with `f(s) ≠ 0` exactly when that
exponent vector is not a nonzero multiple of the `s`-coordinate vector. ∎

## Item 4: the root-tower theorem

Normalize indices so that `r'` involves exactly `a_0, …, a_m`. Take the top case; the bottom case follows by
replacing `t` with `t^{-1}`, which reverses the indices. Cyclically, `r' = a_m^k v` with `k = e_m ≠ 0` and
`v ∈ F(a_0, …, a_{m-1})`. Put `u = v^{-1}`, so the relation reads `a_m^k = u`. Write `r'_j`, `u_j` for the
shifts by `j` of `r'` and `u`.

**Segments.** For `p ≤ n + 1`, let `S_{[p,n]} = <a_p, …, a_{n+m} | r'_p, …, r'_n>`. So `S_{[p,p-1]}` is free on
`a_p, …, a_{p+m-1}`. Since `a_{n+1+m}` occurs only in `r'_{n+1}`, and there only as `a_{n+1+m}^k`,
`S_{[p,n+1]} = S_{[p,n]} *_{u_{n+1} = s^k} <s>`, with `s = a_{n+1+m}` and `u_{n+1} ∈ S_{[p,n]}`.

**The map to `Z`.** A homomorphism `S_{[p,n]} -> Q` is a vector `(x_p, …, x_{n+m})` with
`Σ_{i=0}^m e_i x_{j+i} = 0` for `p ≤ j ≤ n`. Its value on `u_{n+1}` is `-Σ_{i=0}^{m-1} e_i x_{n+1+i}`.
- Let `c = min{i : e_i ≠ 0}`. By hypothesis `c ≤ m - 1`. Put `d = m - c ≥ 1`.
- Every relation involves only positions `j+c, …, j+m`, with nonzero end coefficients `e_c` and `e_m`.
  - Positions `p, …, p+c-1` occur in no relation; set them to `0`.
  - On `[p+c, n+m]` the relations form a recurrence of order `d` that can be solved both forward and
    backward. So any values on `d` consecutive positions of `[p+c, n+m]` extend uniquely to a solution.
- The positions `n+1+c, …, n+m` are `d` consecutive positions in `[p+c, n+m]`, because `n + 1 ≥ p`. Set
  `x_{n+1+c} = 1` and `x_{n+2+c} = … = x_{n+m} = 0`, and extend.
- The value on `u_{n+1}` is then `-e_c ≠ 0`. Clear denominators to get `f: S_{[p,n]} -> Z` with
  `f(u_{n+1}) ≠ 0`.

In particular `u_{n+1}` has infinite order, so the amalgam above is honest. This also covers `n = p - 1`,
where there are no relations.

**Induction.** `S_{[p,p-1]}` is free, so it lies in `𝓗`. By item 3 and the map just built, each `S_{[p,n+1]}`
lies in `𝓗` if `S_{[p,n]}` does. So every `S_{[p,n]} ∈ 𝓗`.

**Assembly.** Let `N = ker(G -> Z)` be the kernel of the `t`-exponent map. By (M), `N = <a_i, i ∈ Z | r'_j, j ∈ Z>`,
and for intervals `[p,n] ⊆ [p',n']` the natural maps `S_{[p,n]} -> S_{[p',n']}` are injective. So `N` is the
directed union of the subgroups `S_{[p,n]}`. By (C), `N ∈ 𝓗`, and then `G = N ⋊ Z ∈ 𝓗`. ∎

## Item 5: the example

In `r = a^2 b a b a^2 b^{-2}`, `b` has exponent sum `0`. We have
`r = a^2 · (b a b^{-1}) · (b^2 a^2 b^{-2})`. With `a_i = b^{-i} a b^i`, this is `a_0^2 a_{-1} a_{-2}^2`.
Replacing `b` with `b^{-1}` and reindexing gives `r' = a_0^2 a_1 a_2^2`. The top letter `a_2` forms one
syllable, and `(e_0, e_1) = (2, 1) ≠ 0`, so item 4 applies.

**Base and edge groups.** In `B = <a_0,a_1,a_2 | a_0^2 a_1 a_2^2>` we have `a_1 = a_0^{-2} a_2^{-2}`, so
`B = F(x,z)` with `x = a_0` and `z = a_2`. Then `A = <a_0,a_1> = <x, z^2>` and `C = <a_1, a_2> = <x^2, z>`.

**No retraction.** Suppose `ρ: B -> A` is a retraction. Then `ρ(z)^2 = ρ(z^2) = z^2`. Square roots are unique in
free groups, so `ρ(z) = z`. But the map `F(x,z) -> Z/2` given by `x ↦ 0, z ↦ 1` kills `A` and not `z`, so
`z ∉ A`. This is a contradiction. The same argument with `x` and `z` exchanged works for `C`.

**Primitivity rank.** The abelianization is `Z ⊕ Z/5` (the exponent sums are `5` and `0`), which is not `Z`. So
`r` is not primitive. `r` is not a proper power. So no cyclic subgroup contains `r` as an imprimitive element,
and `F_2` itself does. Hence `π(r) = 2`. ∎

## Item 6: Higman's group

By [[higman-bs-amalgam-has-hughes-free-division-rings]], `G_1 = K ⋊ BS(1,2)`, where `K` is locally free. `K` is a
directed union of free groups and `BS(1,2)` is locally indicable amenable, so `G_1 ∈ 𝓗` by (C). By relabelling,
`G_2 ∈ 𝓗`. By [[higman-group-splits-as-amalgams-over-free-subgroups]], `Hig = G_1 *_{F_ac} G_2` with
`F_ac ≅ F_2`.

Each relation `y^{-1} x y = x^2` abelianizes to `x = 0`, so `Hig` is perfect. `Hig` is nontrivial, since it
contains `G_1`. A nontrivial finitely generated perfect group has no map onto `Z`, so `Hig` is not locally
indicable. By (L) it is not HFE, so it is not in `𝓗`.

For any `φ: Hig -> Q ∈ 𝓗`, the image is finitely generated and perfect inside a locally indicable group, so it is
trivial. In particular `φ` is not injective on `F_ac`. This is consistent with item 1, and shows that its
edge hypothesis cannot be removed. ∎

## Item 7: the computation

**Soundness.** `hierarchy_certify.py` returns `True` only through the following steps:
- a letter occurring once (the group is free);
- Nielsen moves (automorphisms of the free group);
- the Magnus rewrite at an exponent-zero letter, with a certified base;
- then one of: a free product (rank 0), a retraction onto `A` or `C` checked by substitution in the free group
  (R), the cyclic-edge quotient (item 2), the root rule (item 3), or the root-tower test (item 4).

Proper powers return `False`. Every `False`, including the memo value `cycle` and depth cutoffs, means only
"not certified".

**Census.** `census.py L LIMIT` enumerates cyclically reduced two-letter words of length at most `L`, involving
both letters and not proper powers, up to rotation, inversion and relabelling. It runs `certify` in modes `old`
and `new`. The output for `L = 11` is `census-L11.txt`: no uncertified words through length 10, and 8 at
length 11. A run at `L = 12` (about 100 s) leaves 73 uncertified. Every cyclically reduced relator of a
torsion-free two-generator one-relator group appears in this enumeration, up to those symmetries. ∎
