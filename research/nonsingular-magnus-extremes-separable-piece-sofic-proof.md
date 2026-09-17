---
rg: 2
id: nonsingular-magnus-extremes-separable-piece-sofic-proof
kind: route
title: Grow a locally finite alphabet along the Magnus shift by solving nonsingular equations, then fold with an enlarged stabilizer
target: nonsingular-magnus-extremes-separable-piece-sofic
requires:
  - hnn-folds-into-free-coset-wreath
  - kervaire-laudenbach-holds-for-hyperlinear
  - separating-sofic-quotient-sets-make-an-action-sofic
  - sofic-actions-restrict-to-co-amenable-subgroups
  - gkp-sofic-action-toolkit
  - gkp-free-generalized-wreath-soficity
  - elek-szabo-sofic-permanence
---

Date: 2026-09-17. Written proof, not a Lean certificate.

## 0. Setting and statement

Let `G = <a,t | w>` with `t`-exponent sum `0`. Put `a_i = t^(-i) a t^i`. A
cyclic permutation of `w` rewrites as a word `W_0(a_0,...,a_n)`, `n >= 1`,
in which both `a_0` and `a_n` occur. Let

    B_0 = <a_0,...,a_n | W_0>,   F_- = <a_0,...,a_(n-1)>,   F_+ = <a_1,...,a_n>.

By the Freiheitssatz, `F_-` and `F_+` are free on the listed letters, so
`phi(a_i) = a_(i+1)` is an isomorphism `F_- -> F_+`. By Magnus--Moldavanskii,

    G = < B_0, t | t^(-1) c t = phi(c)  (c in F_-) >.

Let `eps_0` and `eps_n` be the exponent sums of `a_0` and `a_n` in `W_0`.

**Theorem.** If (N) `eps_0 != 0 != eps_n`, and (S) `B_0` is residually
finite with `F_-`, `F_+` closed in its profinite topology, then `G` is sofic.

Hypothesis (S) is used only through the following consequence.

**(S').** For finite sets `E_- <= B_0 \ F_-`, `E_+ <= B_0 \ F_+` and
`E_1 <= B_0 \ {1}` there are a finite group `P` and a homomorphism
`r_0 : B_0 -> P` such that
* `r_0(b)` is not in `r_0(F_-)` for `b in E_-`;
* `r_0(b)` is not in `r_0(F_+)` for `b in E_+`;
* `r_0(b) != 1` for `b in E_1`.

*Proof of (S') from (S).* For `b` not in the closed subgroup `F_-`, some
finite-index normal `N_b` has `b` not in `F_- N_b`. So in `B_0/N_b` the image of
`b` avoids the image of `F_-`. Treat `F_+` in the same way, and use residual
finiteness for `E_1`. Then take `r_0` to be the diagonal map into the finite
product of these quotients. If `r_0(b) in r_0(F_-)`, then projecting to the
factor `B_0/N_b` gives a contradiction, and similarly for the other two
conditions. ∎

## 1. The shift dictionary

Let `Q` be a group. Let `S = Q^Z rtimes <sigma>`, where `Q^Z` is the full
product and `(sigma y sigma^(-1))_j = y_(j-1)`, so `(sigma^(-i) y sigma^i)_j = y_(j+i)`.

**Lemma 1.** Suppose `x in Q^Z` satisfies `W_0(x_j, x_(j+1), ..., x_(j+n)) = 1`
for every `j in Z`. Then `rho(a) = x`, `rho(t) = sigma` defines a
homomorphism `rho : G -> S`. For `b in B_0` and `j in Z`,

    rho(b)_j = b(x_j, ..., x_(j+n)),

where `b(...)` evaluates any word for `b` in `a_0..a_n`. In particular
`r := pi_0 o rho|_(B_0)` is the homomorphism `a_i -> x_i`.

*Proof.* `rho(a_i) = sigma^(-i) x sigma^i` has `j`-th coordinate `x_(j+i)`.
So `rho(W_0)` has `j`-th coordinate `W_0(x_j,...,x_(j+n)) = 1`. Then `rho(w)`
is conjugate to `rho(W_0) = 1`, which gives the homomorphism. The coordinate
formula holds on generators, and multiplication in `Q^Z` is coordinatewise.
The value is well defined because each window is a representation of `B_0`. ∎

## 2. Growing the alphabet

**Lemma 2.** Let `r_0 : B_0 -> P` with `P` finite, and let `(N)` hold. Then
there are finite groups `P = P_0 <= P_1 <= P_2 <= ...` and a configuration
`x : Z -> P_inf := union_k P_k` such that:
* `x_i = r_0(a_i)` for `0 <= i <= n`;
* `W_0(x_j,...,x_(j+n)) = 1` for all `j`.

*Proof.* **Input.** One nonsingular equation over a finite group has a
solution in a finite overgroup. This is Nitsche--Thom, Theorem 1.2, credited
to Gerstenhaber--Rothaus and Pestov, as recorded in
[[kervaire-laudenbach-holds-for-hyperlinear]]: "if `G` is finite, `H` can be
taken finite". It applies to one equation `v(X) in <X> * P` with nonzero
exponent sum `e`. The presentation complex of `<X | X^e>` has `H_2 = 0`. The
overgroup contains `P` as a subgroup.

The classical argument runs as follows:
1. Embed `P` in `U(m)` by its regular representation.
2. The map `X -> v(X)` on `U(m)` is homotopic to `X -> X^e`, by moving the
   coefficients to `1` inside the connected group `U(m)`.
3. That map has degree `e^m != 0`, so it is onto and `v` has a root `X_0`.
4. `<P, X_0>` is a finitely generated linear group, so it is residually finite
   (Malcev). A finite quotient injective on `P` gives the finite overgroup.

**Construction.** By induction we build finite `P_k` and an interval
`[l_k, u_k]` containing `[0,n]`, with `x_j in P_k` for `j` in the interval and
all windows inside the interval satisfied. Start with `P_0 = P`, `[l_0,u_0] = [0,n]`,
`x_i = r_0(a_i)`. The only window is `W_0(r_0(a_0),...,r_0(a_n)) = r_0(W_0) = 1`.

* **Forward step (k even).** Consider
  `v(X) = W_0(x_(u-n+1), ..., x_u, X) in <X> * P_k`, where `u = u_k`. Its
  `X`-exponent sum is `eps_n != 0`. Take a finite `P_(k+1) >= P_k` and a root
  `x_(u+1) in P_(k+1)`. The new window is `(x_(u-n+1),...,x_(u+1))`. Old
  windows still hold because `P_k <= P_(k+1)` is a subgroup.
* **Backward step (k odd).** Solve
  `v(X) = W_0(X, x_l, ..., x_(l+n-1)) = 1`, where `l = l_k`. The `X`-exponent
  sum is `eps_0 != 0`. Set `x_(l-1)` to be the root.

Both ends grow without bound, so `x` is defined on all of `Z`. Every window
lies in some finite stage, where it holds. ∎

Note that `P_inf` is locally finite: a finite subset lies in some `P_k`.

## 3. The target group is sofic

Fix `x` from Lemma 2 and `rho : G -> S = P_inf^Z rtimes <sigma>` from Lemma
1. Let `H = rho(G) = <x, sigma>`, and let `L = H cap P_inf^Z`. Then `L` is
normal in `H`, `H/L = <sigma> = Z`, and `L` is generated by the shifts
`sigma^k x sigma^(-k)`. So `L` is countable, and `rho(B_0) <= L` because
`rho(a_i) = sigma^(-i) x sigma^i`. For `N >= 0`, let
`pi_N : L -> P_inf^([-N,N])` be the restriction of coordinates, and
`K_N = ker pi_N`.

**Lemma 3.** `L` and `H` are sofic.

*Proof.* `P_inf^(2N+1)` is locally finite, since a finitely generated
subgroup lies in `P_k^(2N+1)` for some `k`. So `pi_N(L)` is locally finite,
hence amenable, hence sofic. The intersection of the `K_N` is trivial, so `L`
embeds in `prod_N pi_N(L)`. Therefore `L` is sofic
([[elek-szabo-sofic-permanence]]: products and subgroups). Also `H/L = Z` is
amenable, so `H` is sofic by the amenable-extension clause of the same
theorem. ∎

## 4. The enlarged stabilizer and its coset action

Define

    D_N = rho(F_-) K_N   (a subgroup of L, since K_N is normal in L),
    D   = intersect_(N >= 0) D_N.

Then `rho(F_-) <= D <= L`.

**Lemma 4.** The action `H action H/D` is sofic.

*Proof.* The argument has three steps.

1. **`L action L/D_k'` is sofic for every conjugate `D_k' = sigma^k D sigma^(-k)`.**
   Write `D_k' = intersect_N sigma^k D_N sigma^(-k)`. Each group in the
   intersection is `sigma^k rho(F_-) sigma^(-k) * sigma^k K_N sigma^(-k)`.
   Conjugation by `sigma^k` is an automorphism of `L`, so `sigma^k K_N sigma^(-k)`
   is normal in `L` and `L / sigma^k K_N sigma^(-k) = L/K_N = pi_N(L)` is
   amenable. The normal core of `sigma^k D_N sigma^(-k)` in `L` contains
   `sigma^k K_N sigma^(-k)`, so `L / core` is a quotient of an amenable group
   and is amenable. Now (C2) of
   [[separating-sofic-quotient-sets-make-an-action-sofic]] applies to the
   countable group `L`.
2. **Orbits.** `H` is the disjoint union of the cosets `sigma^k L`, and `L` is
   normal. The `L`-orbit of `sigma^k D` in `H/D` is `sigma^k L D / D`. Its
   stabilizer in `L` is `L cap sigma^k D sigma^(-k) = D_k'`, since `D <= L`.
   So each orbit of `L action H/D` is `L`-isomorphic to `L/D_k'`, which is
   sofic by step 1. By GKP Proposition 2.16
   ([[gkp-sofic-action-toolkit]]), `L action H/D` is sofic.
3. **Co-amenable restriction.** `L` is normal in `H` with amenable quotient
   `Z`, so it is co-amenable in `H`. By
   [[sofic-actions-restrict-to-co-amenable-subgroups]], `H action H/D` is
   sofic. ∎

## 5. Separation at coordinate 0

**Lemma 5.** Let `b in B_0`, and let `r = pi_0 o rho|_(B_0)`. By Lemma 1,
`r(a_i) = x_i = r_0(a_i)`, so `r = r_0` followed by the inclusion `P <= P_inf`.
Then:
* (i) `rho(b) in D` implies `r_0(b) in r_0(F_-)`;
* (ii) `rho(b) in sigma^(-1) D sigma` implies `r_0(b) in r_0(F_+)`;
* (iii) `rho(b) = 1` implies `r_0(b) = 1`.

*Proof.*

**(i)** `D <= D_0 = rho(F_-) K_0`. Elements of `K_0` have coordinate `0`
equal to `1`, so `pi_0(D_0) = pi_0(rho(F_-)) = r_0(F_-)`.

**(ii)** Let `y` be in `sigma^(-1) D sigma`. Then `y` is in
`sigma^(-1) D_1 sigma`, which equals `sigma^(-1) rho(F_-) sigma * sigma^(-1) K_1 sigma`.
* First factor: `sigma^(-1) rho(a_i) sigma = rho(t^(-1) a_i t) = rho(a_(i+1))`,
  so `sigma^(-1) rho(F_-) sigma = rho(F_+)`.
* Second factor: if `k in K_1`, then `(sigma^(-1) k sigma)_j = k_(j+1)`, which
  is `1` for `j in [-2, 0]`, in particular at `j = 0`.

So `pi_0(y) in pi_0(rho(F_+)) = r_0(F_+)`.

**(iii)** is immediate from `pi_0`. ∎

## 6. The fold with an enlarged stabilizer

This is [[hnn-folds-into-free-coset-wreath]], with `rho(C)`
replaced by any subgroup `D >= rho(C)`. The proof is repeated here, because
the stabilizer changes.

Let `X = H/D`, `o = D`, `F_X = F(z_x : x in X)`, and `W = F_X rtimes H` with
`h z_x h^(-1) = z_(hx)`. Here `C = F_-`, `C' = F_+`.

**Lemma 6.** `Phi(b) = rho(b)` for `b in B_0` and `Phi(t) = z_o sigma` define
a homomorphism `G -> W`. Let `E <= G` be finite. Fix Britton-reduced forms of
the elements of `E^(-1) E \ {1}`. Suppose that for every inner syllable `b`:
* if `b` sits between `t` and `t^(-1)`, then `rho(b)` is not in
  `sigma^(-1) D sigma`;
* if `b` sits between `t^(-1)` and `t`, then `rho(b)` is not in `D`.

Suppose also that `rho(b) != 1` for every element of `t`-length `0`. Then
`Phi` is injective on `E`.

*Proof.* **Relations.** For `c in F_-`, `rho(c) in D` fixes `o`, so
`rho(c) z_o rho(c)^(-1) = z_o`. Hence
`Phi(t)^(-1) Phi(c) Phi(t) = sigma^(-1) rho(c) sigma = rho(phi(c)) = Phi(phi(c))`.
The relations of `B_0` hold because `Phi|_(B_0) = rho|_(B_0)`.

**Normal form.** Let `g = b_0 t^(e_1) b_1 ... t^(e_k) b_k` be reduced, and
`P_i = rho(b_0 t^(e_1) ... b_(i-1))`. Moving the `z` letters left gives

    Phi(g) = z_(x_1)^(e_1) ... z_(x_k)^(e_k) rho(g),

with `x_i = P_i o` if `e_i = +1` and `x_i = P_i sigma^(-1) o` if `e_i = -1`.
Two adjacent letters cancel only if `e_(i+1) = -e_i` and `x_(i+1) = x_i`.
* `(+1,-1)`: `x_(i+1) = P_i sigma rho(b_i) sigma^(-1) o`, so equality means
  `rho(b_i) in sigma^(-1) D sigma`.
* `(-1,+1)`: `x_(i+1) = P_i sigma^(-1) rho(b_i) o`, so equality means
  `rho(b_i) in D`.

Both are excluded, so the `z` word is freely reduced of length `k`.

**Injectivity.** Suppose `Phi(g) = 1` with `g != 1`. Then `k = 0` and `rho(g) = 1` with `g = b_0 in B_0`, which is
excluded. So `Phi` separates distinct elements of `E`. ∎

## 7. Proof of the Theorem

Let `E <= G` be finite. Fix Britton-reduced forms of `E^(-1)E \ {1}`, and let
* `E_+` be the inner syllables sitting between `t` and `t^(-1)`;
* `E_-` be those sitting between `t^(-1)` and `t`;
* `E_1` be the elements of `t`-length `0`.

Reducedness gives `E_+ <= B_0 \ F_+` and `E_- <= B_0 \ F_-`, because
`t c' t^(-1)` with `c' in F_+` and `t^(-1) c t` with `c in F_-` are pinches.
Also `E_1 <= B_0 \ {1}`. The argument then runs:
1. By (S'), take `r_0 : B_0 -> P`.
2. By Lemma 2, grow `x`, which uses (N).
3. By Lemma 1, get `rho`, `H`, `L`, `D`.
4. By Lemma 5, the hypotheses of Lemma 6 hold. So `Phi : G -> W` is injective
   on `E`.
5. `W = Z wr^*_(H/D) H` is sofic by [[gkp-free-generalized-wreath-soficity]]
   (with `K = Z`), using Lemma 3 (`H` sofic) and Lemma 4 (`H action H/D` sofic).

So for every finite `E` there is a homomorphism from `G` to a sofic group that
is injective on `E`. Such a group is sofic, as in the Corollary of
[[hnn-folds-into-free-coset-wreath]]. ∎

## 8. Corollary: free pieces

If `W_0` is primitive in `F(a_0,...,a_n)`, then `B_0` is free of rank `n`.
Free groups are residually finite, and finitely generated subgroups of free
groups are closed in the profinite topology (M. Hall 1949). So (S) holds, and
(N) gives soficity. A letter `a_i` with `0 < i < n` occurring exactly once
makes `W_0` primitive: solve for it.

Example (BS(1,2)): `t^(-1) a t = a^2` gives `W_0 = a_1 a_0^(-2)` with `n = 1`.
`a_1` occurs once, so the piece is free on `a_0`, and `eps_0 = -2`, `eps_1 = 1`.

**Conditional corollary (not claimed).** If `B_0` is hyperbolic and virtually
compact special, and `F_-`, `F_+` are quasiconvex, then (S) holds by
Haglund--Wise separability of quasiconvex subgroups. The quasiconvexity of
Magnus subgroups in this setting has not been pinned from the literature here.

## 9. Calibrations and the exact break

**BS(2,3) = <a,t | t^(-1) a^2 t = a^3>.** Here `W_0 = a_1^2 a_0^(-3)`, and
`B_0 = <a_0,a_1 | a_0^3 = a_1^2>` is the trefoil group. Seifert-fibred
3-manifold groups are LERF (Scott), so (S) holds. `eps_0 = -3`, `eps_1 = 2`,
so the theorem gives soficity. That agrees with the known answer: the map
`a -> 1`, `t -> (x -> 3x/2)` to `Z[1/6] rtimes Z` is injective on the vertex
group `<a>`, so its kernel acts freely on the Bass--Serre tree and is free,
and BS(2,3) is free-by-metabelian, hence sofic by Elek--Szabo.

*Why the alphabet must grow.* Suppose every `x_j` lies in one finite group
`Q`. Write `o_j = ord(x_j)`, `v_p` for the `p`-adic valuation, and use
`x_(j+1)^2 = x_j^3`.
* **Orders are prime to 2.** `v_2(o_j) = v_2(ord x_j^3) = v_2(ord x_(j+1)^2) = max(v_2(o_(j+1)) - 1, 0)`.
  If some `v_2(o_j) >= 1`, then `v_2(o_(j+1)) = v_2(o_j) + 1`, which is
  unbounded going forward. So all `o_j` are odd.
* **Orders are prime to 3.** `max(v_3(o_j) - 1, 0) = v_3(o_(j+1))` forces
  unbounded growth going backward unless `v_3 = 0`.
* **Consequence.** With orders prime to `6`, `x_(j+1)` is a power of
  `x_(j+1)^2 = x_j^3`, hence of `x_j`. So `x_j` and `x_(j+1)` commute, and
  `rho([a, t^(-1) a t])` has coordinate `[x_j, x_(j+1)] = 1` everywhere.

But `[a, t^(-1) a t] != 1` in BS(2,3) (Britton), and it lies in the kernel of
every finite quotient. So a fixed finite alphabet reproduces exactly the
classical non-residual-finiteness. The growth of `P_inf` is what separates
this element: for `b = a_0 a_1 a_0^(-1) a_1^(-1)`, (S') separates `b` from `1`
in a finite quotient of the trefoil group, and the continuation then forces an
unbounded alphabet. The method therefore does not "prove" residual finiteness,
which is false here, and its targets are genuinely infinite and not residually
finite.

**The break at a singular extreme.** If `eps_n = 0`, the forward step is an
equation with zero exponent sum, and such equations can be unsolvable in every
overgroup. For Baumslag--Gersten, `<a,t | (t^(-1)at)^(-1) a (t^(-1)at) = a^2>`,
the rewriting is `W_0 = a_1^(-1) a_0 a_1 a_0^(-2)`, with `eps_0 = -1` and
`eps_1 = 0`. The forward step is `X^(-1) x_j X = x_j^2`, which has no solution
in any group once `x_j` has even order, since `x_j` and `x_j^2` then have
different orders. So Lemma 2 fails at the first forward step for every `r_0`
with `r_0(a_1)` of even order. Lemma 2 uses (N) and nothing else, and the only
place (N) enters is the solvability of the forward and backward equations.

Choosing odd orders does not rescue the method. The obstruction is to the
whole dictionary with *any* torsion alphabet, not just to this growth scheme:

**Proposition (BG kills every torsion alphabet).** Let `Q` be any group, and
let `x in Q^Z` satisfy the Baumslag--Gersten window relation
`x_(j+1)^(-1) x_j x_(j+1) = x_j^2` for all `j >= j_0`. If every `x_j`
(`j >= j_0`) has finite order, then `x_j = 1` for all `j >= j_0`. If the
relation holds for all `j`, then `x = 1`, so `rho(a) = 1`.

*Proof.* Let `m_j = ord(x_j)`. Conjugation by `x_(j+1)` sends `x_j` to
`x_j^2`, so these have equal order and `m_j` is odd. It restricts to the
automorphism `y -> y^2` of `<x_j>`, which has order `ord_(m_j)(2)`, so
`ord_(m_j)(2)` divides `m_(j+1)`.

Suppose `x_j != 1` for some `j >= j_0`, and take a prime `p_0 | m_j`. Then
`p_0 >= 3`, so `ord_(p_0)(2) > 1`, and `ord_(p_0)(2)` divides `ord_(m_j)(2)`.
Hence it divides `m_(j+1)`. Choose a prime `p_1 | ord_(p_0)(2)`. Then
`p_1 | m_(j+1)`, so `p_1` is odd, and `p_1 <= p_0 - 1 < p_0`. Iterating gives an
infinite strictly decreasing sequence of odd primes, which is impossible. So
`x_j = 1` for `j >= j_0`.

For the second statement, take `j_0` arbitrarily negative. ∎

So for BG every shift representation over a periodic alphabet (finite, locally
finite, or of bounded exponent) is trivial on `a`, and no choice of `r_0` or
growth scheme helps. This is the class-killing obstruction for the
torsion-alphabet dictionary at this singular extreme. It calibrates against the
classical fact that every finite quotient of BG is cyclic. A singular extreme
needs a non-periodic alphabet (for instance `U(m)` with infinite-order
letters), and then the local finiteness used in Lemmas 3 and 4 is lost.

**Consistency with the radical constraint.** By
`magnus-piece-meets-nontrivial-linton-radical`, a nontrivial Linton radical
meeting `B_0` dies in every target with trivial rationally perfect radical.
Our `H` is `L rtimes Z` with `L` residually locally finite, and the locally
finite quotients `pi_N(L)` can be perfect (for instance, products of `A_5`).
So this construction is not in the class that constraint rules out.
