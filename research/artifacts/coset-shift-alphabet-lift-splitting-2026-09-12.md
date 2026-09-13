# Coset shifts split off full shifts at lifted alphabets (2026-09-12)

Lane w7-coset-shared-prime, after w6-free-pos-d (`finite-stabilizer-coset-shift-transfer-2026-09-12.md`).
Target: `finite-stabilizer-coset-shifts-inherit-surjunctivity` at a shared prime `p | gcd(m, |H|)`.
Everything here is **unverified**; verification requested from w4-vf-positive-b. Decisions stay OPEN.

Conventions follow the transfer artifact:
- `G` is any group and `H <= G` is finite.
- `G` acts on the left, `(g.z)(x) = z(g^-1 x)`.
- `Y = {y in A^G : y(kh) = y(k)}` is identified with `A^(G/H)`, with `|A| = m`.

## 0. Summary

1. **Theorem A (lifted splitting).** Let `j = 1 + max ceil(v_q(|H|) / v_q(m))` over the primes `q | gcd(m, |H|)`,
   with `j = 1` when `gcd(m, |H|) = 1`, and let `|A'| = m^j`.
   - There is a twisted coset shift `Z` (depending on `H` and `m`, not on `tau`) with a topological
     `G`-conjugacy `Theta : Y x Z -> A'^G`.
   - For every self-map `tau` of `Y`, `Theta (tau x id) Theta^-1` is an automaton with memory `FH ∪ H`.
     It is injective iff `tau` is, and surjective iff `tau` is.
   - So a group surjunctive at size `m^j` has every finite-stabilizer coset shift at size `m`
     surjunctive, at every prime. For `H = Z/p` and `m = p` this is `j = 2`, size `p^2`.
2. **Obstruction at the same size (Proposition B).**
   - The blockwise splitting at size `m` exists iff `m` divides every orbit-type count of
     `Map(H, A)`.
   - At `H = Z/p`, `m = p` it fails by the mark congruence `|W| = |W^H| mod p`, since
     `p^(p-1) != 1 mod p`.
   - Proposition C: when `H` is normal of order `p` and avoided by a finite-index normal subgroup, no
     subshift `Z` at all gives `Y x Z ≅ A^G` at size `p`.
3. **Linear Question 9.**
   - It holds, using only stable finiteness, whenever `H` injects into a finite quotient
     (Proposition D). At `D_inf` the restriction to `<ab>` makes `F_2[G/H]` a free `F_2[<ab>]`-module
     of rank one.
   - It reduces to multi-orbit modules with stabilizers inside `Res_fin(G)` (Proposition E).
   - A failure over `F_p` makes `G` non-surjunctive at a `p`-power size (Proposition F).
4. **Mixed primes.** Theorem A covers `m = 6`, `H = S_3` at size 36 with no new idea. At fixed size 6 the
   Sylow reduction and the CRT split both give nothing (Section 4).
5. **Where it stops.** The fixed-size claim at a shared prime is exactly alphabet descent from `m^j` to
   `m`, for the product automata of Theorem A.

## 1. Orbit colourings and the twisted coset shift

**Blocks.** For `z in A'^G` and `k in G`, put `b_k(z) in Map(H, A')`, `b_k(z)(h) = z(kh)`. The group `H`
acts on `Map(H, A')` from the right by `(f.h')(h) = f(h'h)`. Then `b_(kh')(z) = b_k(z).h'`.

**Orbit types.** For `S <= H`, the functions with stabilizer containing `S` are those constant on the
right cosets `Sx`, so there are `x^[H:S]` of them, where `x = |A'|`.
- Möbius inversion gives the number with stabilizer exactly `S`:
  `e_S(x) = sum_(T >= S) mu(S, T) x^[H:T]`.
- An orbit of type `(S)` has `[H:S]` points, and `[N_H(S) : S]` of them have stabilizer exactly `S`.
- So the number of orbits of type `(S)` is `N_S(x) = e_S(x) / [N_H(S) : S]`, an integer for every `x`.

**Lemma 1 (colouring).** Suppose `m | N_S(x)` for every `S <= H`. Then there is an `H`-invariant map
`c : Map(H, A') -> A` whose fibres are pairwise isomorphic right `H`-sets.

*Proof.* Split the `N_S(x)` orbits of each type `(S)` into `m` classes of equal size, and let `c` send an
orbit to its class. Each fibre then has `N_S(x)/m` orbits of type `(S)` for every `S`, so all fibres
are isomorphic. `□`

Fix such a `c` and a right `H`-set `W` isomorphic to every fibre, with isomorphisms
`beta_a : W -> c^-1(a)`. Put `beta(a, w) = beta_a(w)`. This is an `H`-equivariant bijection
`A x W -> Map(H, A')`, with `H` acting trivially on `A`.

**Twisted coset shift.** `Z = {w in W^G : w(kh) = w(k).h for all k in G, h in H}`.
- `Z` is closed and `G`-invariant, since left translation commutes with the right `H`-structure.
- It is of finite type with memory `H`.
- It is nonempty: on each left coset `kH` put `w(kh) = w_0.h`, which is well defined because `H` acts
  freely on `kH`.
- It has `G`-fixed points `w = w_0` for `w_0 in W^H`, and `|W^H| = |A'|/m >= 1`.

**Lemma 2 (splitting).** `Theta(y, w)(k) = beta(y(k), w(k))(1)` is a topological `G`-conjugacy
`Y x Z -> A'^G`.

*Proof.*
- **Blocks.** `b_k(Theta(y,w))(h) = beta(y(kh), w(kh))(1) = beta(y(k), w(k).h)(1)`, which equals
  `(beta(y(k), w(k)).h)(1) = beta(y(k), w(k))(h)`. So `b_k(Theta(y, w)) = beta(y(k), w(k))`.
- **Inverse.** `y(k) = c(b_k z)` and `w(k) = beta_(y(k))^-1(b_k z)`.
  - `y(kh) = c(b_k(z).h) = y(k)` by invariance of `c`.
  - `w(kh) = w(k).h` by equivariance of `beta_a`.
  - So the inverse lands in `Y x Z`, and both composites are the identity blockwise.
- **Equivariance.** `Theta(g.y, g.w)(k) = Theta(y, w)(g^-1 k)`.
- **Continuity.** Both maps read one block, and compact to Hausdorff gives a homeomorphism. `□`

**Lemma 3 (divisibility).** With `x = m^j` and `j` as in Section 0, `m | N_S(x)` for every `S <= H`.

*Proof.* Fix a prime `q`. Every term of `e_S(x)` is a multiple of `x`, so `v_q(e_S(x)) >= j v_q(m)`.
We need `v_q(e_S(x)) >= v_q(m) + v_q([N_H(S) : S])`.
- *`q ∤ m`:* this is integrality of `N_S`.
- *`q | m`, `q ∤ |H|`:* the index term vanishes and `j >= 1`.
- *`q | m`, `q | |H|`:* `v_q([N_H(S):S]) <= v_q(|H|) <= (j-1) v_q(m)`. `□`

**Theorem A.** Let `j` be as in Section 0 and `|A'| = m^j`. For every continuous `G`-equivariant self-map
`tau` of `A^(G/H)`, `Phi = Theta (tau x id_Z) Theta^-1` is an automaton on `A'^G`.
- `Phi` is injective iff `tau` is, and surjective iff `tau` is, since `Z` is nonempty.
- If `tau` reads the cosets `kfH` for `f in F`, then `Phi` has memory `FH ∪ H`.
- **Corollary A1.** If `G` is surjunctive at size `m^j`, the node's claim holds at `(H, m)`.
- **Corollary A2.** A group surjunctive at every size has every finite-stabilizer coset shift surjunctive
  at every size. So a strict coset-shift automaton over a Gottschalk host is impossible at every prime.

*Proof.* Curtis–Hedlund–Lyndon holds over every group, and Lemmas 1–3 give `Theta`. `□`

**Remarks.**
- At `gcd(m, |H|) = 1`, `j = 1` and Theorem A reproves Theorem 1 of the transfer artifact at the same
  size, with no averaging and no group structure on `A`.
- Theorem A does not contradict Lemma 2 of the transfer artifact. `Y` is not a subshift of `A'^G`
  through `Theta` except along a fixed `w_0`, and `Phi` commutes with no group translation of `A'`.

## 2. The same-size obstruction

**Proposition B (blockwise criterion).** A splitting of the Section 1 shape at `|A'| = m`, i.e. an
`H`-equivariant bijection `A x W -> Map(H, A)`, exists iff `m | N_S(m)` for every `S <= H`.

*Proof.* The orbits of type `(S)` in `A x W` number `m` times those in `W`, which gives necessity.
Sufficiency is Lemma 1. `□`

- **`H = Z/p`, `m = p`.** There are `p` fixed points, and `(p^p - p)/p = p^(p-1) - 1` free orbits, which
  `p` does not divide. So the splitting fails.
  - Equivalently, `|W| = p^(p-1)` and `|W^H| = 1` break the mark congruence `|W| = |W^H| mod p`.
  - At size `p^2`, `W` has `p` fixed points and `p^(2p-2) - 1` free orbits.
- **Linear shadow (directive candidate 3).** `F_p[Z/p] ≅ F_p[u]/(u^p)` with `u = h - 1` is uniserial.
  - The fixed line `(u^(p-1))` has no complement, so "invariant shift plus a free part of dimension
    `p - 1` over `F_p[h]`" does not exist even on one block.
  - `0 -> F_p -> F_p[Z/p] -> F_p[u]/(u^(p-1)) -> 0` represents a generator of
    `Ext^1_(F_p[Z/p])(F_p[u]/(u^(p-1)), F_p) ≅ F_p`. At `p = 2` this is the identity class in
    `H^1(Z/2; F_2) = Hom(Z/2, F_2)`.
  - Globally it is Lemma 8 of the transfer artifact: `F_p[G/H]` is not projective.
  - The set-level orbit decomposition `A^H = A ⊔ (free orbits)` does exist. What fails at size `m` is
    divisibility, not a linear splitting.
- **Frobenius-twisted retraction (directive candidate 2).** Suppose `r(z + c) = r(z) + phi(c)` for an
  additive bijection `phi` of `A`.
  - Lemma 2's input makes the window at `kh` equal to the window at `k` plus `a`.
  - Then `r(z)(kh) = r(z)(k) + phi(a)`, and output in `Y` forces `phi(a) = 0`, so `a = 0`. Excluded.
- **Fibered extension over the orbit map (directive candidate 1).**
  - The orbit map `X -> B^(G/H)`, with `B = A^H / H` and `|B| = p + p^(p-1) - 1`, is canonical, and
    `Y` sits inside it as the fixed symbols.
  - A lift of an extension of `tau` must choose torsor data at every output coset carrying a free symbol.
  - Not completed. Theorem A supersedes it at size `m^j`.
- **Defect-freezing extension (tried, fails).**
  - Construction: keep `z` on non-constant cosets, and on constant cosets apply `tau`'s rule to the min
    retraction `rho(z)`. This is an automaton with `Phi|_Y = tau` and `Phi^-1(Y) = Y`.
  - It is not injective. Take `G = Z x Z/2`, `H = Z/2` and `tau` the shift `w(n) -> w(n+1)`. Let `z, z'`
    have the same non-constant coset at `0`, be constant on every other coset, and differ only on
    coset `1`.
  - Only the output at `0` reads coset `1`, and that coset is frozen. So `Phi(z) = Phi(z')`.

**Proposition C (no same-size product splitting).** Let `H ⊴ G` have order `p` and `|A| = p`, and let
`N ⊴ G` have finite index with `N ∩ H = 1`. Then no subshift `Z` admits a `G`-conjugacy `Y x Z ≅ A^G`.

*Proof.* Restrict to `N`-fixed points and put `G_0 = G/N`. Then
`Fix_N(Y) x Fix_N(Z) ≅ A^(G_0)` as finite `G`-sets.
- **Full shift.** `h in H` acts freely on `G_0`, so `|A^(G_0)| = p^|G_0|` with `p^(|G_0|/p)` points fixed
  by `h`.
- **Coset shift.** `Fix_N(Y)` has `p^(|G_0|/p)` points, all fixed by `h`, because `H` is normal.
- **Quotient.** So `|Fix_N(Z)| = p^(|G_0| - |G_0|/p)` and `|Fix_N(Z)^h| = 1`.
- The mark congruence for the `Z/p`-set `Fix_N(Z)` reads `0 = 1 mod p`, a contradiction. `□`

Proposition C obstructs the product method, not the claim. A same-size proof at a shared prime needs a
`tau`-dependent construction that is not a product.

## 3. Linear Question 9

Let `char K = p` divide `|H|`, and put `M = K[G/H]`.
- **Q9-Hopf(G,H,K).** For every `n`, every surjective `K[G]`-endomorphism of `M^n` is injective. By
  Lemma 6 of the transfer artifact this is linear surjunctivity of `(K^n)^(G/H)`.
- **Q9-DF(G,H,K).** The Hecke algebra `End_(K[G])(M)`, with basis the double-coset sums, is stably finite.
- **Relation.** Q9-Hopf implies Q9-DF, since `fg = 1` with `gf != 1` makes `f` surjective and not injective.
  The converse is not automatic: `M` is not projective, so surjections need not split.
- **Question 9, precisely.** Does stable finiteness of `K[G]` imply Q9-Hopf(G,H,K)? Does it imply the
  weaker Q9-DF?

**Proposition D (separated stabilizers).** Let `N ⊴ G` have finite index with `N ∩ H = 1`, and suppose
`K[N]` is stably finite, e.g. because `K[G]` is. Then Q9-Hopf(G,H,K) holds, in every characteristic.

*Proof.*
- **Free restriction.** `N ∩ gHg^-1 = g(N ∩ H)g^-1 = 1`, so `N` acts freely on `G/H` with
  `r <= [G:N]` orbits. Hence `M ≅ K[N]^r` as left `K[N]`-modules.
- **Section.** A surjective `K[G]`-endomorphism `f` of `M^n` is a surjective endomorphism of the free
  module `K[N]^(rn)`, so it has a section `s` with `fs = 1`.
- **Direct finiteness.** `End_(K[N])(K[N]^(rn)) ≅ M_(rn)(K[N])^op` is directly finite, so `sf = 1` and
  `f` is injective. `□`

A subgroup with finitely many free orbits on `G/H` has finite index, since `G = ⋃_(i<=r) N g_i H` gives
`[G:N] <= r|H|`. So Proposition D is the whole free-orbit case.

**At `D_inf`.** Take `G = <a> * <b>`, `H = <a>` and `N = <t>` with `t = ab`, of index 2, so `N ∩ H = 1`.
- `G/H ≅ Z`, where `t` shifts and `a` reflects `n -> -n`.
- So `F_2[G/H] ≅ F_2[t^±1]` is free of rank one, and Proposition D uses only stable finiteness of
  `F_2[t^±1]`, not amenability.
- The Hecke algebra is `F_2[t^±1]^sigma = F_2[t + t^-1]`, where `sigma(t) = t^-1`. It is commutative.

**Proposition E (residual reduction).** Let `R = Res_fin(G)`.
- **Setup.** Since `H` is finite, some finite-index `N_0 ⊴ G` has `N_0 ∩ H = H ∩ R`. Take representatives
  `g_i` of `N_0 \ G / H` and put `H_i = g_i (H ∩ R) g_i^-1 <= R`.
- **Decomposition.** `N_0 g_i H / H ≅ N_0 / H_i`. So as `K[N_0]`-modules `M ≅ ⊕_i K[N_0/H_i]`, and as
  `N_0`-shifts `A^(G/H) ≅ A^(⊔_i N_0/H_i)`.
- **Consequence.**
  - Question 9 at `(G, H)` follows from its multi-orbit version over `N_0`, with stabilizers inside `R`.
  - The node's claim reduces the same way, since surjunctivity passes to subgroups at a fixed size.
  - With Prop 10 of the transfer artifact (normal Sylow), the open residue is non-normal `H` with
    `H ∩ Res_fin(G) != 1`.

**Proposition F (what a failure gives).** Let `K` be finite of characteristic `p`, and suppose Q9-Hopf
fails at `n`.
- **Linear strictness.** The transpose is a strict linear self-map of `(K^n)^(G/H)` at size `|K|^n`.
- **Nonlinear strictness.** By Theorem A, `G` carries a strict automaton at size `|K|^(nj)`, a power of `p`.
- **Refutation.** If `F_p[G]` is stably finite as well, this refutes
  `stable-finiteness-forces-prime-power-surjunctivity` and Gottschalk. It is a J_1-type lead: a
  non-projective module certificate that the corner routes do not see.
- **Converse.** `stable-finiteness-forces-prime-power-surjunctivity` implies Q9-Hopf for every finite `K` of
  characteristic `p`. This removes the size mismatch in Section 4 of the transfer artifact.
- **Hosts.**
  - Propositions D and E exclude every residually finite and every virtually torsion-free host.
  - What remains is `V` (simple, so `Res_fin(V) = V`), `E ⋊ V`, and Radu lattices with 2-torsion in the
    finite residual. I did not decide any of them.
  - For `V` with `H` a transposition, `j = 2` at `m = 2^n`, so a failure would make `V` non-surjunctive
    at size `4^n`.
  - Rank-function status of `F_2[V]`: lanes w7-yh-rank-firewall, w7-v-rank-split and w7-escape-set,
    not duplicated here.

## 4. Mixed primes: `m = 6`, `H = S_3`

- **Theorem A applies.** `j = 1 + max(1, 1) = 2` and `|A'| = 36`. The orbit counts of
  `Map(S_3, A')` are:
  - type `S_3`: 36;
  - type `C_3`: `(36^2 - 36)/2 = 630`;
  - type `C_2`: `36^3 - 36 = 46620`;
  - free: `(36^6 - 36 - 1260 - 3·46620)/6 = 362773530`.
  All four are divisible by 6.
- **The blockwise splitting fails at size 6.** Type `C_3` gives `(6^2 - 6)/2 = 15`, not divisible by 6.
- **The Sylow reduction gives nothing.** `[S_3 : C_3] = 2` and `[S_3 : C_2] = 3` are not units mod 6.
- **CRT.** `A = F_2 x F_3` gives `A^(G/H) = F_2^(G/H) x F_3^(G/H)`, but `tau` need not be a product
  map, so CRT reduces only product maps.
- **Verdict.** Mixed primes need no new idea for the lifted statement. At fixed size 6 they are the same
  descent problem as a single shared prime.

## 5. Where it stops, and the next lead

- **Descent.** At a shared prime every method here lifts the alphabet. The fixed-size claim needs
  surjunctivity at size `m` to reach the product automata `Theta (tau x id_Z) Theta^-1` at size `m^j`.
  - `strict-rule-pairs-pass-to-product-alphabets` moves strictness upward.
  - `surjunctivity-failure-descends-to-binary-alphabet` is the open group-level descent.
- **No product method.** Proposition C excludes product splittings at the same size. The defect-freezing
  extension fails on the shift over `Z x Z/2`.
- **Next lead.**
  - First choice: descent from `p^2` to `p` for the Theorem A automata at `H = Z/p`.
  - Otherwise: Q9-Hopf at `V` with `H` a transposition.
