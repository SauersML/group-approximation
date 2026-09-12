# The Kun--Thom Clifford cover as a Gottschalk test host

Lane `w3-free-neg`, 2026-09-12.

## 0. Why this host

The negative lanes work on the Leavitt unit groups, Thompson's `V`, the projective ternary group,
lattices in products of trees, and Fournier-Facio's group. Every one of those is a simple, or nearly
simple, nonsofic group with no known surjunctive quotient.

This lane takes a host of a different kind: a **finite central extension of a group already known to be
surjunctive**.

- `Gamma < G` is the Kun--Thom Theorem E pair and `X = G/Gamma`.
- `S` is a `G`-invariant graph on `X` with `b_S(o,y) = 1`.
- `Vtilde_S` is the central `F_2`-extension of `directSum_X F_2` with commutator form `b_S`, and
  `E_S = Vtilde_S semidirect G`.
- `eps` is the central involution, `c_x` a lift of the basis vector at `x`, and `c_x c_y = eps^(b_S(x,y)) c_y c_x`.

Known facts (all on main):
- `E_S` is weakly sofic and not sofic (`kun-thom-clifford-cover-weakly-sofic`).
- `E_S / <eps> = W`, the Kun--Thom wreath, which is surjunctive (`kun-thom-nonsofic-wreaths-are-surjunctive`).

So `E_S` is exactly the open residue of `finite-normal-subgroups-do-not-affect-surjunctivity`: a central
subgroup of order two over a surjunctive quotient. If `E_S` is not surjunctive, it refutes both that claim
and Gottschalk's conjecture, and it does so on a weakly sofic host, by a mechanism unrelated to the
Leavitt hosts. If `E_S` is surjunctive, that settles the first nontrivial instance of the closure question.

Sections 1 and 2 show that no landed tool reaches `E_S`. Section 3 reduces its linear case to one skew
group ring.

## 1. No finitary site structure

**Proposition 1.1.** For every `G`-invariant graph `S` with at least one edge, the split extension
`E_S = Vtilde_S semidirect G` carries no finitary structure in the sense of
`finitary-split-extension-surjunctivity-permanence`, whatever the support function `L`.

*Proof.* Suppose `(p_T, iota, L)` is a finitary structure on `N = Vtilde_S`. Fix an edge `{o, y}` of `S`,
so `[c_o, c_y] = eps`, and a finite set `T` of sites.

By (A2) with `U` empty, `p_T(alpha_g n) = 1` whenever `g L(n)` misses `T`.

The set `B = {g : g L(c_o) meets T} union {g : g L(c_y) meets T}` is a finite union of sets
`{g : g l = t}`. Each is empty or a left coset of `Stab_G(l)`, which is conjugate to `Gamma` and so of
infinite index. By B. H. Neumann's lemma, finitely many cosets of infinite-index subgroups do not cover
`G`, so there is `g` outside `B`.

For that `g`, `p_T(c_(go)) = p_T(c_(gy)) = 1`. By invariance `b_S(go, gy) = b_S(o, y) = 1`, so
`p_T(eps) = p_T([c_(go), c_(gy)]) = 1`.

This holds for every finite `T`, so (A1) fails for `n = eps`. QED

**Consequence.** Neither Theorem 0 of the finitary artifact nor its wreath instance applies to `E_S`.

## 2. The center dies in every finite quotient (complete graph)

**Proposition 2.1.** Let `S` be the complete graph on `X`, so all distinct lamps anticommute modulo
`eps`. Every homomorphism from `E_S` to a finite group kills `eps`.

*Proof.* Let `f : E_S -> Q` be a homomorphism with `Q` finite and `f(eps) = z != 1`. For distinct sites
`x, y`, `[f(c_x), f(c_y)] = z != 1`, so `f(c_x) != f(c_y)`. `X` is infinite, so `Q` would contain
infinitely many distinct elements. QED

**Consequence.** `eps` does not inject into any finite quotient, so
`separated-finite-normal-subgroups-preserve-surjunctivity` does not apply.

## 3. The linear case reduces to a Clifford skew group ring

**Proposition 3.1.** `F_3[E_S]` is the product of the two central summands cut by
`(1 + eps)/2` and `(1 - eps)/2`:

```text
F_3[E_S]  =  F_3[W]  x  A_S,
A_S  =  (F_3-algebra on c_x with c_x^2 = (-1)^(q(x)),  c_x c_y = (-1)^(b_S(x,y)) c_y c_x)  *  G,
```

Here `q` is the square function of the extension, and `*` is the skew group ring for the site permutation
action.

A one-sided inverse pair in `F_3[E_S]` exists iff one exists in `F_3[W]` or in `A_S`: pad with the unit
on the other factor, or project. `F_3[W]` is stably finite by
`rf-lamps-preserve-stable-finiteness-for-arbitrary-actions`, since `F_3[G]` is stably finite for
residually finite `G`.

**So:** `F_3[E_S]` fails direct finiteness iff `A_S` does. By
`stable-finiteness-failure-refutes-surjunctivity`, that failure makes `E_S` not surjunctive.

*Proof.* `eps` is central of order two and `2` is invertible in `F_3`, so the two idempotents are central
and orthogonal and sum to `1`. The first summand is `F_3[E_S / <eps>] = F_3[W]`. In the second, `eps`
acts as `-1`, which gives the displayed relations. `G` fixes `eps`, so it acts on the lamp algebra by site
permutations. QED
