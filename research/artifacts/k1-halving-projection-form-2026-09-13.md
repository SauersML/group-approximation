# The halving homotopy as a projection homotopy between two free copies of O_2

Lane `ex-k1-halving-homotopy`, 2026-09-13. Everything below is proved in full. None of it has been
reviewed externally, and none of it decides the halving homotopy or STW Problem LXI.

Notation. `U = O_2 *_C C(T)` is the full unital free product, with Cuntz generators `s_1, s_2` and free
unitary `z`. `D = O_2 *_C O_2` has the canonical inclusions `iota_1, iota_2`. Blanchard's substitution
(arXiv:0804.4624, proof of Proposition 4.6(i), written there for O_3) gives an isomorphism
`D -> U`, `iota_1(s_k) -> s_k`, `iota_2(s_k) -> z s_k`, with inverse `z -> sum_l iota_2(s_l) iota_1(s_l)^*`.
In a unital algebra A with a Cuntz pair, `C(w) = s_1 w s_1^* + s_2 s_2^*`. All citations of BRR are to
Blanchard--Rohde--Rordam, arXiv:0704.1554v1 (J. Noncommut. Geom. 2 (2008)), read in full for this lane.

BRR inputs, quoted by number:
- Proposition 2.3 (Cuntz): properly infinite full projections p, q satisfy `p ~ q` iff `[p] = [q]` in `K_0`.
- Lemma 2.4(ii): if `[u] = 0` in `K_1(A)` and some projection p with p and `1-p` properly infinite and full
  satisfies `||up - pu|| < 1`, then `u in U^0(A)`.
- Proposition 5.1, (i) <=> (iii): a unital properly infinite A is K1-injective iff for all properly infinite
  full projections p, q there are properly infinite full `p_0 <= p`, `q_0 <= q` with `p_0 ~_h q_0`.
- Proposition 5.1, (i) => (ii): in a K1-injective properly infinite A, `p ~ q` with `p, q, 1-p, 1-q`
  properly infinite and full gives `p ~_h q`.

## 1. The projection form

**Theorem 1.** The following are equivalent.
(a) `U` (equivalently `D`) is K1-injective.
(c) Every unital properly infinite C\*-algebra A with `[1_A] = 0` in `K_0(A)` is K1-injective.
(d) `s_1 s_1^* ~_h z s_1 s_1^* z^*` in `U`. Equivalently, `iota_1(s_1 s_1^*) ~_h iota_2(s_1 s_1^*)` in `D`.
(e) There are projections `p, q in O_2`, both different from 0 and 1, with `iota_1(p) ~_h iota_2(q)` in `D`.
(f) The C([0,1])-algebra `A_2 = { f in C([0,1], D) : f(0) in iota_1(O_2), f(1) in iota_2(O_2) }`
    contains a projection other than 0 and 1.

The equivalence (a) <=> (c) is `trivial-unit-class-lxi-iff-universal-halving-homotopy`. So (d), (e) and (f)
are further equivalent forms of the halving homotopy `o2-free-circle-halving-homotopy`. They are the
`[1] = 0` analogues of BRR Proposition 4.3 and Theorem 5.5 (iv), (v), with O_2 in place of O_infty.

*Proof.* (a) => (d). Put `e_1 = s_1 s_1^*` and `e_2 = z e_1 z^*`. The partial isometry `z e_1` gives
`e_1 ~ e_2`. The projections `e_1`, `e_2`, `1 - e_1 = s_2 s_2^*` and `1 - e_2 = z s_2 s_2^* z^*` are all
equivalent to 1, which is properly infinite and full. BRR Proposition 5.1 (i) => (ii) gives `e_1 ~_h e_2`.
Under Blanchard's isomorphism, `iota_2(s_1 s_1^*) -> z s_1 s_1^* z^* = e_2`, so both forms of (d) agree.

(d) => (c). Let A be unital and properly infinite with `[1_A] = 0`. By BRR Proposition 5.1 (iii) => (i) it
suffices, given properly infinite full projections p and q, to find properly infinite full `p_0 <= p` and
`q_0 <= q` with `p_0 ~_h q_0`. As in the proof of BRR Theorem 5.5, (iv) => (i), there are properly infinite
full `p_0 <= p` with `p_0 ~ 1` and `1 - p_0` properly infinite and full. Indeed, p contains two orthogonal
copies of 1. Take `p_0` to be the first one. Then `1 - p_0` dominates the second, and a projection that
dominates a properly infinite full projection is properly infinite and full. Choose `q_0 <= q` the same way.
Now `[p_0] = [1] = 0` and `[1 - p_0] = [1] - [p_0] = 0 = [1]`. Both are properly infinite and full, so
`1 - p_0 ~ 1` by BRR Proposition 2.3. So there are isometries `t_1, t_2` in A with `t_1 t_1^* = p_0` and
`t_2 t_2^* = 1 - p_0`, which is a Cuntz pair. Likewise there is a Cuntz pair `r_1, r_2` with
`r_1 r_1^* = q_0`. The universal property of D gives a unital \*-homomorphism `phi: D -> A` with
`phi(iota_1(s_k)) = t_k` and `phi(iota_2(s_k)) = r_k`. Applying phi to a homotopy from (d) gives
`p_0 ~_h q_0`.

(c) => (a). U contains O_2 unitally, so it is properly infinite and `[1_U] = [1_{O_2}] = 0`.

(d) => (e) is trivial. (e) => (d): in O_2, every projection other than 0 and 1 is homotopic to `s_1 s_1^*`.
Indeed, O_2 is purely infinite and simple with `K_0(O_2) = 0`, so `p ~ s_1 s_1^*` and `1 - p ~ s_2 s_2^*`.
Hence `p = v s_1 s_1^* v^*` for a unitary `v in O_2`, and `U(O_2)` is connected (Cuntz). Apply this to p in
`iota_1(O_2)` and to q in `iota_2(O_2)`, and compose the three homotopies.

(e) <=> (f) is the proof of BRR Proposition 4.3, (i) <=> (ii), word for word. A nontrivial projection
`f in A_2` gives the path `t -> f(t)` from `iota_1(p)` to `iota_2(q)`. Its endpoints are not 0 or 1, because
`t -> ||f(t)||` and `t -> ||1 - f(t)||` are continuous and take values in {0, 1}. Conversely a homotopy
from (e) is a nontrivial projection in `A_2`. Square.

## 2. What the halving map does to the component group

**Proposition 2.** Let A be unital with a Cuntz pair, `G = U(A)/U^0(A)`, and `phi([w]) = [C(w)]`.
1. phi is a group endomorphism of G, and `phi o phi = phi`.
2. `ker phi = N := ker(G -> K_1(A))`.
3. phi maps G onto a subgroup isomorphic to `K_1(A)`, so `G = N ⋊ phi(G)` with `phi(G) ≅ K_1(A)`.
4. A is K1-injective iff `phi = id` iff `N = 1`. The halving homotopy (b) says exactly that `phi = id` on
   every such A.

*Proof.* `C(w)C(w') = C(ww')`, so phi is a homomorphism. Next,
`C(C(w)) C(w)^* = s_1 C(w) w^* s_1^* + s_2 s_2^* = C(C(w) w^*)`. Now `[C(w) w^*] = 0` in `K_1(A)`, because
C is implemented by the unitary row `(s_1, s_2)`. The unitary `C(C(w)w^*)` commutes with `p = s_1 s_1^*`,
and p and `1 - p` are equivalent to 1, hence properly infinite and full. BRR Lemma 2.4(ii) puts it in
`U^0(A)`, so `phi^2 = phi`. The same lemma gives `N ⊆ ker phi`. Conversely `[C(w)] = [w]` in `K_1`, so
`ker phi ⊆ N`. The algebra A is properly infinite, so `G -> K_1(A)` is onto (Cuntz), and it restricts to a
bijection on `phi(G)`. Item 4 follows, since an idempotent endomorphism with trivial kernel is the identity.
Square.

## 3. A route that cannot work: homotopy of O_2-embeddings

BRR Proposition 5.4 proves that any two unital embeddings of `O_infty` into a K1-injective properly infinite
algebra are homotopic. It would be natural to try to prove (d) by connecting the embeddings
`iota: s_k -> s_k` and `Ad z o iota: s_k -> z s_k z^*` of O_2 into U. That fails for a K-theoretic reason,
whatever the answer to (d).

**Proposition 3.** `iota` and `Ad z o iota` are not homotopic as unital \*-homomorphisms `O_2 -> U`.

*Proof.* Fix the base pair `s`. The map `V -> (V s_1, V s_2)` is a homeomorphism from `U(A)` onto the space
of Cuntz pairs in A, with inverse `(t_1, t_2) -> t_1 s_1^* + t_2 s_2^*`. So homotopy classes of unital
embeddings of O_2 are `U(A)/U^0(A)`. For `t_k = z s_k z^*` the unitary is
`V = sum_k z s_k z^* s_k^* = z rho(z^*)`, with `rho(x) = s_1 x s_1^* + s_2 x s_2^* = Theta(diag(x, x))`.
In `K_1(U) = Z[z]` (Germain's six-term sequence for full free products, as in Blanchard 0804.4624,
proof of Proposition 4.6(i)), `[V] = [z] - 2[z] = -[z] ≠ 0`. So V is not in `U^0(U)`. Square.

So O_2 differs from O_infty here. The embeddings carry a `K_1` class, and BRR Lemma 5.3 has no O_2 analogue.
The halving homotopy concerns the range projections only. Any proof has to move `e_1` to `e_2` by a unitary
`u in U^0(U)`, and then `z = u w` with w commuting with `e_1` and `[w] = [z]`.
