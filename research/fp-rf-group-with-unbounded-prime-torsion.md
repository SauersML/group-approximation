---
rg: 2
id: fp-rf-group-with-unbounded-prime-torsion
kind: claim
title: Some finitely presented residually finite group has elements of prime order for infinitely many primes
distinct_from:
  cycle-transposition-lef-group-has-no-regular-tree-action: that is a finitely generated residually finite group, not known to be finitely presented, with elements of every prime order at least 5; this asks for a finitely presented one.
  kms-arbitrarily-hard-fp-rf-groups: that realizes arbitrarily hard word problems by finitely presented residually finite groups whose torsion involves boundedly many primes; this asks for torsion of infinitely many prime orders.
---

**OPEN.** There is a finitely presented residually finite group `G` such that
infinitely many primes occur as orders of elements of `G`.

**Why it matters.** By `regular-tree-torsion-orders-have-primes-at-most-degree`,
such a `G` embeds in `Aut(T_d)` for no `d`. So it refutes
`every-fp-rf-group-embeds-in-fp-self-similar-group`, through the route
`fp-rf-tree-obstruction-via-unbounded-torsion`.

**Literature status.** Not checked. This session ran no literature search, so
whether such a group is already known is open here.

## Attempts

1. **Linear groups.** *Dies.* Let `G` be a finitely generated subgroup of
   `GL_n(K)`.
   - *Characteristic zero.* `G` has a torsion-free normal subgroup `N` of finite
     index `i` (Selberg). A torsion element meets `N` trivially, so its order
     divides `i`.
   - *Characteristic `p`.* The field of entries contains only a finite field
     `F_q` of algebraic elements. Write a torsion element's order as `p^a m'`
     with `m'` coprime to `p`. Its `p^a`-th power is semisimple of order `m'`,
     with eigenvalues in extensions of `F_q` of degree at most `n`. So `m'`
     divides `lcm_(j <= n) (q^j - 1)`.

   Either way only finitely many primes occur.
2. **Abelian-by-polycyclic groups, including finitely generated metabelian
   groups.** *Dies.* Let `A` be the abelian normal subgroup and `P = G/A`.
   - `A` is a Noetherian `Z[P]`-module (P. Hall), so its torsion submodule is
     finitely generated and has finite exponent `e`.
   - `P` is virtually torsion-free, so its torsion orders divide some `e'`.
   - Every torsion order in `G` divides `e*e'`.
3. **Groups acting properly and cocompactly on CAT(0) spaces, and hyperbolic
   groups.** *Dies.* They have finitely many conjugacy classes of finite
   subgroups. This is standard and was not rechecked against a source here.
4. **Kharlampovich--Myasnikov--Sapir groups.** *Dies for torsion.* By
   arXiv:1204.6506 §1.6 and §4 (Lemma 4.14, Theorem 4.17), `G(M)` is a split extension of an elementary
   abelian group of prime exponent `p` by a metabelian group. By attempt 2, only
   finitely many primes occur.
5. **Finitely presented groups that are not residually finite.** Thompson's `V`
   contains every finite group, but it is simple and infinite. Houghton's `H_3`
   contains the finitary symmetric group. Neither is residually finite.
6. **Finitely generated examples, and why block-diagonal ones resist finite
   presentation.** The group of
   `cycle-transposition-lef-group-has-no-regular-tree-action` has every prime
   order `p >= 5`. Let `G <= prod_m F_m` be finitely generated, with every
   `F_m` finite, and suppose the restricted part `K = G ∩ (+)_m F_m` is
   infinite. Two facts constrain such a `G`.
   - **`G/K` is not finitely presented.** Otherwise, since `G` is finitely
     generated, `K` would be the normal closure in `G` of finitely many elements.
     Each of those has finite support, and conjugation in `prod_m F_m` preserves
     supports, so `K` would be finite.
   - **If `G` is finitely presented, then `G/K` is of type `FP_2` over `Q`.**
     `K` is locally finite, so `Q[K]` is von Neumann regular, every
     `Q[K]`-module is flat, and `Tor_i^(Q[K])(Q, Q) = 0` for `i > 0`. Take a
     projective resolution of `Q` over `Q[G]` that is finitely generated in
     degrees at most `2`, and apply `Q ⊗_(Q[K]) -`. The result is such a
     resolution over `Q[G/K]`.

   For the group above, `G/K` is `FSym(Z) x| Z`: it is the permutation of `Z`
   read off from large coordinates, and step 2 of
   `cycle-transposition-lef-group-proof` shows that this is a well-defined
   homomorphism with kernel `K`. That quotient is Houghton's `H_2`. It is not
   finitely presented, as the first fact confirms. It is not `FP_2` over `Q`
   either (`houghton-h2-is-not-fp2-over-q`), so the group itself is not
   finitely presented (`cycle-transposition-lef-group-is-not-finitely-presented`,
   2026-09-13).

   A finitely presented residually finite overgroup would suffice. That is the
   route `unbounded-prime-torsion-via-rf-higman-embedding`, whose open clause
   is `rf-higman-embedding-for-decidable-groups`.
7. **Frames of products of finite groups (2026-09-13).** *Dies when infinitely
   many factors have nonzero Schur multiplier.*
   - A group `G <= prod_n S_n` containing `(+)_n S_n` retracts onto every finite
     subproduct. So `H_2(G; Z)` contains `(+)_(n <= m) H_2(S_n)` for every `m`
     (`products-of-finite-groups-with-schur-factors-not-fp`).
   - Hence the Kassabov--Nikolov frames of products of alternating groups
     (arXiv:math/0602446), which do have torsion of every prime order, are not
     finitely presented (`kassabov-nikolov-alternating-frames-are-not-fp`).
   - The obstruction is blind to factors with trivial multiplier. Kassabov's
     `EL_3(R) <= prod_n SL_(3n)(F_p)` (their Proposition `g0`) contains
     `(+)_n SL_(3n)(F_p)`, so it has unbounded prime torsion.
   - **It is not finitely presented either** (`kassabov-g0-is-not-finitely-presented`,
     2026-09-13), for a different reason.
     - Weight one edge of the cycle `a_n` by a scalar `λ ≠ 0, 1`.
     - The resulting marked groups satisfy every relation of `EL_3(R)` of length
       below about `n/2`.
     - They break the relation `e_(1,2)((q a^n q)^2 - q a^n q) = 1` with `q = bc`,
       which holds in `EL_3(R)`.
   - The descent criterion `fp2-over-q-descends-along-locally-finite-kernels` was
     not needed. It could not have decided this at the level of `SL_3`. The
     quotient by `(+)_n SL_(3n)(F_p)` is `EL_3` of the ring generated on
     `F_p^(Z)` by the bilateral shift and two matrix units. Modulo a locally
     finite congruence kernel, that is `SL_3(F_p[t^(±1)])`. That is a sketch
     from this lane, not written up as a node, and main decides no `FP_2`
     property for either group.
8. **Other standard classes.** *Die, by standard facts not rechecked here.*
   - *Virtually residually-`p` groups*, including Golod--Shafarevich constructions.
     If `N` has index `i` and is residually `p`, an element of prime order `q`
     outside `N` forces `q | i`. Inside `N` it survives in a finite `p`-quotient,
     so `q = p`.
   - *Finite graphs of finite groups.* Finite subgroups fix a vertex of the
     Bass--Serre tree, so torsion orders divide vertex group orders.
   - *Lattices in products of trees* act properly and cocompactly on a CAT(0)
     space (attempt 3).
   - *S-arithmetic groups over function fields* are linear (attempt 1).
9. **Steinberg groups over a finitely presented residually finite ring with
   every additive order (2026-09-17, swarm-0917-w6-w6-z-last2).** *Reduced to one
   open hole; not dead.*
   - **The ring.** Let `R_count = Z<u,x,e | xu-ux-x, ue, eu>` and
     `r_n = e x^n e`. Since `x^n u = (u+n) x^n`, we get `n r_n = 0`.
     `counting-ring-is-residually-finite-with-every-additive-order` proves that
     `r_n` has order exactly `n` and that `R_count` is residually finite. The
     proof uses a tensor-ring normal form and block shift representations, and
     it avoids the Noetherian obstruction to unbounded torsion.
   - **The group.** `counting-ring-steinberg-group-has-every-torsion-order` uses
     Krstić--McCool and Ershov--Jaikin-Zapirain. It shows that `St_m(R_count)`,
     for `m >= 4`, is finitely presented with (T). Its finite residual lies in
     `K_2(m, R_count)`, and its largest residually finite quotient contains
     `x_12(r_n)` of order `n` for every `n`.
   - **The route.** `unbounded-prime-torsion-via-counting-ring-steinberg` needs
     only `counting-steinberg-residual-finitely-normally-generated`.
     That claim has two independent sufficient mechanisms: residual finiteness
     of `St_m(R_count)`, or finite presentability of `E_m(R_count)`.
   - **Why this avoids attempts 1--8.** The group is not linear over a field. It
     has (T), so it is not amenable-by-anything-small. It is not virtually
     residually-`p`. The torsion comes from the additive torsion of a
     non-Noetherian ring, not from finite vertex groups or a product of finite
     groups.
