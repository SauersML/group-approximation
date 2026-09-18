---
rg: 2
id: deligne-auxiliary-radical-transfer-proof
kind: route
title: Push the radical down to the residually finite base, use centrality of C_3 for the coinvariants, and flexibility of amenable images for the rest
target: deligne-auxiliary-radical-transfer-needs-rigid-image
requires: [mf-radical-functoriality, central-quotients-of-residually-finite-groups-are-mf, deligne-flexible-subgroup-restrictions-carry-exact-sector-models, deligne-triple-cover-mf-radical-dichotomy]
---

Notation of the target. `P` is closed under isomorphism and subgroups and contains every countable residually
finite group. Commutators are `[x,y] = x y x^-1 y^-1`.

**Step 0 (functoriality for `P`).** For every homomorphism `g : G -> G'`, `g(Rad_P G) <= Rad_P G'`.
- Let `pi : G' -> Q` with `Q in P`. Then `pi g(G)` is a subgroup of `Q`, so it lies in `P`.
- Hence `Rad_P(G) <= ker(pi g)`, that is `g(Rad_P G) <= ker pi`.
- Intersect over all `pi`.
- For `P = MF` this is `mf-radical-functoriality`. The argument is the same for every subgroup-closed `P`.

**Step 1 (the base is in `P`, hereditarily).** `Gamma = Sp_4(Z)` is countable and residually finite, since the
congruence maps `Gamma -> Sp_4(Z/m)` separate points. Every subgroup of `Gamma` is therefore a countable residually
finite group, so it lies in `P`. For `P = MF` this is the case of trivial central quotient in
`central-quotients-of-residually-finite-groups-are-mf`.

**(R1).** Let `f : H -> E_3`, `K = f(H)`, `N = Rad_P(H)`.
- `p f : H -> Gamma` has image `p(K)`, which lies in `P` by Step 1. So `N <= ker(p f)`, that is `f(N) <= ker p = C_3`.
- Step 0 applied to the surjection `f : H -> K` gives `f(N) <= Rad_P(K)`.
- `C_3` is central in `E_3`, since Deligne's cover is a central extension. So
  `f([N,H]) = [f(N), K] <= [C_3, E_3] = 1`, and `f|_N` factors through `N/[N,H]`.
- *Consequence.* Let `M` be normal in `H` with `M <= N` and `M = [M,H]`. Then `f(M) <= f(N) <= C_3` is central,
  so `f(M) = f([M,H]) = [f(M), K] = 1`.
  - A perfect `N` satisfies `N = [N,N] <= [N,H] <= N`.
  - For `H = EL_n(R)` with `n >= 3`, `EL_n(R,I)` is by definition the normal closure in `H` of the `e_ij(a)` with
    `a in I`. Choose `k` distinct from `i` and `j`. The Steinberg relation `e_ij(a) = [e_ik(a), e_kj(1)]` puts every
    generator in `[EL_n(R,I), H]`, which is normal in `H`. So `EL_n(R,I) = [EL_n(R,I), H]`.

**(R2).** Suppose `f(N) != 1`.
- `C_3` has prime order and `1 != f(N) <= C_3`. So `f(N) = C_3`, and `z in Rad_P(K)` by (R1).
- Suppose `A = p(K)` were Deligne-flexible. By (F1) of `deligne-flexible-subgroup-restrictions-carry-exact-sector-models`,
  its preimage `A~ = p^-1(A)` is residually finite.
  - `K <= A~` is countable, because `E_3` is finitely generated, and residually finite. So `K in P`.
  - Then `Rad_P(K) <= ker(id_K) = 1`, which contradicts `z in Rad_P(K)`.
  - So `A` is Deligne-rigid.
- `p f : H -> A` is surjective and kills `N`, because `f(N) <= C_3 = ker p`. So it factors through a surjection
  `Q_H = H/N -> A`.

**(R3).** By (R2) it suffices to show that `A = p(K)` is amenable, because (F3) of
`deligne-flexible-subgroup-restrictions-carry-exact-sector-models` says every amenable subgroup of `Gamma` is flexible.
`A` is a quotient of `Q_H` (R2), which gives two cases.
- *`Q_H` amenable.* Quotients of amenable groups are amenable.
- *`Q_H` satisfies a nontrivial law `w`.* Then so does its quotient `A`. The free group of rank two satisfies no
  nontrivial law, so `A` has no rank-two free subgroup. `A <= GL_4(Z)`, and the Tits alternative in characteristic
  zero makes `A` virtually solvable, hence amenable. The Tits alternative is recalled, not re-read, as in the proof
  of (F3).
- This covers the listed cases: trivial, abelian, solvable, nilpotent, and bounded exponent.

**(R4).** This is Step 0 applied to `j`. The containment `j(Rad_P(E_3)) <= Rad_P(H)` can show that `z` is *not* in
`Rad_P(E_3)`: that happens when `j(z)` is not in `Rad_P(H)`. It cannot show the converse, because nothing forces
`Rad_P(E_3)` to contain `j^-1(Rad_P H)`.

**Step H (the hyperlinear reading).** Take `P` to be the hyperlinear groups. This class is closed under subgroups
and finite direct products, and contains all residually finite groups. These standard facts are recalled, not
re-read.
- If `E_3` is hyperlinear, then `Rad_HL(E_3) <= ker(id) = 1`.
- Conversely, suppose `z notin Rad_HL(E_3)`. Choose `pi : E_3 -> Q`, `Q` hyperlinear, with `pi(z) != 1`.
  - Then `ker(pi, p) <= C_3 ∩ ker pi = 1`, because `C_3` has prime order.
  - So `E_3` embeds in `Q x Gamma`, which is hyperlinear, and `E_3` is hyperlinear.
- Hence `z in Rad_HL(E_3)` iff `E_3` is not hyperlinear. The MF version of this equivalence is
  `deligne-triple-cover-mf-radical-dichotomy`.

**What is and is not used.** Nothing about the cocycle beyond (F1) and (F3). No property (T), no operator norms, no
traces. The same proof works for any central extension `1 -> C -> E -> B -> 1` with `C` of prime order and every
subgroup of `B` in `P`, once "flexible" is read as "has residually finite preimage".
