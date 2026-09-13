# Braided V is Hopfian (Zaremsky Problem 2.10, first part)

Lane z2-10-bv-hopfian, 2026-09-13. Status: complete argument, UNREVIEWED (sent to z-verify-groups).

## 0. Setting and sources (read verbatim)

`V_br` is the Brin–Dehornoy braided Thompson group (Brin, J. Group Theory 10 (2007); Dehornoy,
Adv. Math. 205 (2006)). Elements are braided paired tree diagrams `(T_-, b, T_+)`, with `b` a braid on
`n` strands and `T_±` trees with `n` leaves. They are taken modulo expansions, and an expansion bifurcates a
strand into two parallel clones. `pi: V_br -> V` forgets the braid down to its permutation.
`P_br = ker pi = {(T, p, T) : p in PB_n(T)}` is the direct limit of the copies `PB_T` of the pure braid groups
under cloning.

- [Z] M. C. B. Zaremsky, *On normal subgroups of the braided Thompson groups*, arXiv:1403.8132v2
  (Groups Geom. Dyn.). The following were read from the PDF:
  - Corollary 2.8: "Any proper normal subgroup of V_br is contained in P_br."
  - Theorem 2.1: "Let N be a normal subgroup of F_br. Then either N ≤ P_br or else [F_br, F_br] ≤ N."
  - Question 4.7: "Are F_br and/or V_br Hopfian?"
  - Proposition 4.8: "The group P_br is not Hopfian." Its surjection `phi_L` forgets strands and is not
    `V_br`-equivariant.
  - p. 1 recalls that V is simple and that any proper quotient of F is abelian.
  - Lemma 4.2 and the proof of Lemma 4.3 give conjugation in triples:
    `(S,b,T)(T,p,T)(T,b^{-1},S) = (S, b p b^{-1}, S)`.
  - Example 4.5 records cloning on `H_1(PB_n)`: `e_{ij}` goes to the sum of `e_{ab}` over the clones `a` of
    `i` and `b` of `j`.
- [SS] S. Sam and A. Snowden, *Gröbner methods for representations of combinatorial categories*,
  arXiv:1409.1670v3 (J. Amer. Math. Soc. 30 (2017)). The following were read from the PDF:
  - §3.1: "An object of Rep_k(C) is noetherian if every ascending chain of subobjects stabilizes ... The
    category Rep_k(C) is noetherian if every finitely generated object in it is."
  - §8.1: FS is the category of nonempty finite sets with surjective functions.
  - Corollary 8.1.3: "If k is left-noetherian then Rep_k(FS^op) is noetherian."
- Classical inputs:
  - Artin's representation `PB_n -> Aut(F_n)` is faithful, and a pure braid sends each `x_i` to a
    conjugate of `x_i`, so the image lies in `IA_n`.
  - Free groups are residually nilpotent (Magnus).
  - Andreadakis: `A_c = ker(Aut F_n -> Aut(F_n / gamma_{c+1} F_n))` satisfies `[A_1, A_c] <= A_{c+1}`.

## 1. Lemma A: surjective endomorphisms preserve the pure part

Let `phi: V_br -> V_br` be surjective. Then `phi^{-1}(P_br) = P_br`, `phi(P_br) = P_br` and
`ker phi <= P_br`.

*Proof.*
1. `M := phi^{-1}(P_br)` is normal. It is proper: if `M = V_br`, surjectivity would give `V_br = P_br`.
   By [Z, Cor. 2.8], `M <= P_br`.
2. `phi` induces an isomorphism `V_br / M -> V_br / P_br = V`, so `V_br / M` is simple.
3. The natural projection `V_br / M -> V_br / P_br` is onto a nontrivial group, so its kernel `P_br / M` is a
   proper normal subgroup of a simple group. Hence `M = P_br`.
4. So `ker phi <= M = P_br` and `phi(P_br) <= P_br`. For `y` in `P_br`, write `y = phi(x)`; then `x` lies in
   `phi^{-1}(P_br) = P_br`.

## 2. Lemma B: `P_br` is residually nilpotent, compatibly with the finite stages

For every tree `T`, `PB_T ∩ gamma_c(P_br) = gamma_c(PB_T)`, and `∩_c gamma_c(P_br) = 1`.

*Proof.*
1. Cloning strand `k` is an injective homomorphism `PB_n -> PB_{n+1}`. Deleting clone `k+1` is a
   homomorphism `PB_{n+1} -> PB_n` and a left inverse. So for `T <= T'` the inclusion `PB_T -> PB_{T'}` has a
   left-inverse homomorphism `r`.
2. If `x` is in `PB_T ∩ gamma_c(PB_{T'})`, then `x = r(x)` lies in `gamma_c(PB_T)`.
3. `P_br` is the directed union of the `PB_T`, so `gamma_c(P_br) = ∪_{T'} gamma_c(PB_{T'})`. This gives the
   first claim.
4. `PB_n` is residually nilpotent: induction with `[A_1, A_c] <= A_{c+1}` gives `gamma_c(IA_n) <= A_c`, and
   `∩_c A_c = 1` by Magnus. Artin's representation is faithful with image in `IA_n = A_1`.
5. An element of `∩_c gamma_c(P_br)` lies in some `PB_T`, hence in `∩_c gamma_c(PB_T) = 1`.

*Related work.* Residual nilpotence of `PB_n` is classical and commonly credited to Falk–Randell; that
source was not re-read. Burillo–González-Meneses (arXiv:math/0608646v1) handle the same direct limit
`PBV = P_br`:
- their Lemma 3.1 proves that strand doubling preserves the Kim–Rolfsen bi-order, via the lower central
  series of `F_n`;
- Corollary 3.2 proves that `PBV` is bi-orderable, and Theorem 3.3 that `BF` is.
They do not state Lemma B, but their mechanism is closely related.

## 3. Graded pieces form a finitely generated FS^op-representation

For `c >= 1` put `L_c(n) := gamma_c(PB_n) / gamma_{c+1}(PB_n)`, a finitely generated abelian group.

*The functor.* Take a surjection `f: [m] -> [n]`. Replace strand `i` by `|f^{-1}(i)|` parallel clones,
with the fibres placed consecutively, and conjugate by a permutation braid moving the clones to the positions
`f^{-1}(i)`. This gives a homomorphism `PB_n -> PB_m`. The induced map `L_c(f)` is determined in degree 1 by

`A_{ij} ↦ sum_{a in f^{-1}(i), b in f^{-1}(j)} A_{ab}`.

This agrees with [Z, Ex. 4.5]; different choices of permutation braid only permute the clones within a
fibre, which fixes the formula. `gr(PB_n)` is generated in degree 1 as a Lie ring, and all these maps are
Lie-ring homomorphisms, so `L_c(f)` is well defined and functorial. Thus `L_c` is a representation of
`FS^op` over `Z`.

*Lemma C.* `L_c` is generated by `L_c([j])` for `j <= 2c + 1`.

*Proof.*
1. `L_c(m)` is spanned by `c`-fold brackets of classes `A_{ab}`. Such a bracket involves at most `2c` strands
   `s_1 < … < s_r`.
2. If `r = m` there is nothing to do. Otherwise let `f: [m] -> [r+1]` send `s_i ↦ i` and every other strand to
   `r+1`.
3. The fibres over `1..r` are singletons, so `L_c(f)` sends the same bracket written in `A_{ij}` (`i, j <= r`)
   inside `L_c(r+1)` to the given bracket.

By [SS, Cor. 8.1.3] with `k = Z`, `L_c` is noetherian: every ascending chain of subrepresentations
stabilizes.

## 4. Lemma D: ACC for V-invariant subgroups of `gr_c(P_br)`

Put `gr_c(P_br) := gamma_c(P_br) / gamma_{c+1}(P_br)`.

1. By Lemma B each `L_c(PB_T) -> gr_c(P_br)` is injective (its kernel is
   `gamma_c(PB_T) ∩ gamma_{c+1}(P_br) = gamma_{c+1}(PB_T)`), and `gr_c(P_br)` is their directed union.
2. `V_br` acts on `gr_c(P_br)` by conjugation. `P_br` acts trivially, because
   `[gamma_1, gamma_c] <= gamma_{c+1}`, so `V` acts.

*Claim.* Ascending chains of V-invariant subgroups of `gr_c(P_br)` stabilize.

*Proof.*
1. For a V-invariant subgroup `N` and `n >= 1`, let `N(n)` be the image in `L_c(n)` of
   `N ∩ L_c(PB_T)` for a tree `T` with `n` leaves.
2. `N(n)` does not depend on `T`: `(T_2, 1, T_1)` conjugates `(T_1, q, T_1)` to `(T_2, q, T_2)`.
3. `N(n)` is invariant under the bijections `[n] -> [n]`: `(T, b, T)` acts on `L_c(PB_T)` by the permutation
   of `b`.
4. For a surjection `f: [m] -> [n]`, split leaf `i` of `T` into `|f^{-1}(i)|` leaves to get `T'`. The same
   element reads `(T', κ(q), T')`, where `κ` clones along consecutive fibres. Conjugate by `(T', b, T')` with
   `b` a permutation braid; the result realizes `L_c(f)`. So `L_c(f)(N(n)) <= N(m)`, and `n ↦ N(n)` is a
   subrepresentation of `L_c`.
5. The map `N ↦ (N(n))_n` preserves strict inclusion: an element of `N' \ N` lies in some `L_c(PB_T)`.
6. An ascending chain of V-invariant subgroups therefore gives an ascending chain of subrepresentations of
   the noetherian representation `L_c`, which stabilizes.

## 5. Theorem: `V_br` is Hopfian

*Proof.*
1. Let `phi` be a surjective endomorphism, and let `psi = phi|P_br`. By Lemma A, `psi` is a surjective
   endomorphism of `P_br` with `ker psi = ker phi`.
2. Surjectivity gives `psi(gamma_c(P_br)) = gamma_c(P_br)`, so `psi` induces surjections
   `psi_c: gr_c(P_br) -> gr_c(P_br)`.
3. From `psi(x p x^{-1}) = phi(x) psi(p) phi(x)^{-1}`, each `K_j := ker(psi_c^j)` is invariant under
   conjugation by all of `V_br`, hence V-invariant.
4. By Lemma D the chain `K_1 <= K_2 <= …` stabilizes, say `K_j = K_{j+1}`. For `v` in `K_1`, write
   `v = psi_c^j(w)`. Then `psi_c^{j+1}(w) = 0`, so `w` is in `K_{j+1} = K_j` and `v = 0`. So every `psi_c` is
   injective.
5. Let `p ≠ 1` in `P_br`. By Lemma B there is `c` with `p` in `gamma_c \ gamma_{c+1}`. Then `psi_c(p̄) ≠ 0`, so
   `psi(p) ≠ 1`.
6. Hence `ker phi = 1`. ∎

This answers the first question of Problem 2.10 and the V_br half of [Z, Question 4.7] affirmatively, and it
is consistent with [Z, Prop. 4.8]. The proof only uses surjective endomorphisms of `P_br` that are twisted
equivariant for the V-action, and `phi_L` of [Z, Prop. 4.8] is not.

## 6. Second question: is every quotient of V_br finitely presented?

- `V_br` is finitely presented (Brin, Dehornoy). A quotient `V_br / N` is finitely presented iff `N` is the
  normal closure of finitely many elements. So the question is exactly max-n: ACC on normal subgroups.
- *Bounded depth (proved).* Fix `c`. Ascending chains of normal subgroups of `V_br` that contain
  `gamma_c(P_br)` stabilize.
  - Every proper such `N` lies in `P_br` [Z, Cor. 2.8].
  - `N^{(k)} := (N ∩ gamma_k) gamma_{k+1} / gamma_{k+1}` is a V-invariant subgroup of `gr_k(P_br)`.
  - For `k < c` these stabilize along the chain (Lemma D).
  - Downward induction on `k` gives equality: if `H <= H'` both contain `gamma_c`, agree in all
    `N^{(k)}` and satisfy `H ∩ gamma_{k+1} = H' ∩ gamma_{k+1}`, then any `x` in `H' ∩ gamma_k` has some `y` in
    `H ∩ gamma_k` with `x y^{-1}` in `H' ∩ gamma_{k+1} = H ∩ gamma_{k+1}`.
  - *Consequence:* every quotient of `V_br` by a normal subgroup containing `gamma_c(P_br)` is finitely
    presented iff `V_br / gamma_c(P_br)` is. For `c = 1` this is `V`.
- *Open.* Whether `V_br / [P_br, P_br]` is finitely presented, and whether max-n holds. Lemma D does not give
  max-n: a chain can differ only in unbounded depth `c`.

## 7. Remark on F_br

Lemma A holds for `F_br` via [Z, Thm 2.1]: a surjective endomorphism `phi` has `M = phi^{-1}(P_br)` normal.
If `[F_br, F_br] <= M`, then `F_br / M ≅ F` is abelian, which is false. So `M <= P_br`, and `F` is Hopfian
because its proper quotients are abelian, which forces `M = P_br`.

`F_br` can conjugate only by order-preserving relabellings. The subgroups `N(n)` are then subrepresentations
for the opposite category of order-preserving surjections, and we have not checked noetherianity for that
category. `F_br` Hopfian stays open here.
