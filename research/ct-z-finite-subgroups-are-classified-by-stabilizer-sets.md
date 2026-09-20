---
rg: 2
id: ct-z-finite-subgroups-are-classified-by-stabilizer-sets
kind: claim
title: Two embeddings of a finite group in Kohl's CT(Z) are conjugate iff they have the same point-stabilizer subgroups on Z; so torsion elements are conjugate iff they have the same cycle lengths, and the conjugacy problem of CT(Z) is decidable for pairs in which a given element has finite order (a promise algorithm; Kourovka 21.73, torsion case)
artifacts:
  - research/artifacts/gq-bh-bh-free-58-salo-source.md
---

**ESTABLISHED** (lane proof, not reviewed).
- **Proof.** Elementary. The only input is item 3 of
  `ct-p-z-is-a-one-vertex-k-graph-full-group` (a lane node): every piecewise canonical
  permutation of `Z` with `P'`-smooth moduli lies in `CT_P(Z)`. It is used only to put
  the conjugator into `CT(Z)`.
- **Priority.** None is claimed. Kohl's RCWA package documentation may discuss conjugacy tests in
  RCWA(Z); it was not read.
- **Scope.** This settles Kourovka 21.73 on pairs in which one element has finite order.
  The general problem is undecidable (`ct-z-conjugacy-problem-is-undecidable`, landed
  later). As "Consequences for 21.73" below predicts, its instances have infinite order.

## Setting

- **Primes.** `P` is a finite set of odd primes, `P' = P ∪ {2}`, and
  `Ẑ = ∏_{p ∈ P'} Z_p`. A *box* is `B(r, m) = r + mẐ`, with `m` `P'`-smooth.
- **Canonical box maps.** These are the affine maps `x ↦ r' + (m'/m)(x − r)` from
  `B(r, m)` onto `B(r', m')`.
- **Extension to `Ẑ`.** Every `g ∈ CT_P(Z)` extends to a homeomorphism `ĝ` of `Ẑ` that is
  piecewise a canonical box map, and `ĝ` restricts to `g` on the dense set `Z`. A class
  transposition extends in exactly this way, and extensions compose.
- **Stabilizer set.** For a homomorphism `ρ : F → CT(Z)` of a finite group, put
  `S(ρ) = { Stab_ρ(n) : n ∈ Z }`, a conjugation-invariant set of subgroups of `F`.

## Statement

1. **Classification.** Let `ρ_1, ρ_2 : F → CT(Z)` be homomorphisms of a finite group
   `F`. There is `c ∈ CT(Z)` with `c ρ_1(f) c^{-1} = ρ_2(f)` for all `f` iff
   `S(ρ_1) = S(ρ_2)`. The conjugator can be taken in `CT_P(Z)` for any `P` with
   `ρ_1(F), ρ_2(F) ≤ CT_P(Z)`.
2. **Torsion elements.** Two elements of finite order in `CT(Z)` are conjugate iff they
   have the same set of cycle lengths on `Z`. Every such element is conjugate into
   `CT_∅(Z) ≅ V`.
3. **Decidability (promise form).** An algorithm takes `g, h ∈ CT(Z)`, together with the
   promise that `g` has finite order, and decides whether they are conjugate. It must be told
   which input has finite order: without the promise the search for `ord(g)` need not halt, and
   torsion in `CT(Z)` is decided only on the positive-ray class
   (`ct-p-z-positive-ray-torsion-and-finiteness-are-decidable`). (Referee repair, bh-ref-d,
   e64cfcbeeb.)
   - Find `n = ord(g)` by testing `g^k = 1` for `k = 1, 2, …`.
   - Answer no unless `h^n = 1`.
   - Otherwise compare the cycle-length sets, which are computable by the proof of Lemma A.

## Proof

**Lemma A (clopen fixed sets).** If `φ ∈ CT_P(Z)` has finite order `k`, then `Fix(φ̂)` is
clopen in `Ẑ`, and `Fix(φ)` is the union of the classes on which the rcwa table of `φ` is
the identity.
- Let `φ̂(x) = x`. On a box `B ∋ x`, `φ̂` is canonical, say `A(y) = λy + μ` with
  `λ ∈ Q_{>0}`.
- By continuity at the fixed point there is a box `B_0 ∋ x` with `φ̂^j(B_0) ⊆ B` for
  `j < k`. So `φ̂^j = A^j` on `B_0`.
- Then `A^k = id` on `B_0`, so `λ^k = 1`. Hence `λ = 1`, and since `A(x) = x`, also
  `μ = 0`.
- So `A = id` on `B`, `x` is interior, and `Fix(φ̂)` is open. It is closed, being a fixed set.
- A non-identity affine piece has no interior fixed point, so it has none at all. This
  gives the rcwa description. ∎

**Lemma B (clopen sets are equivalent).** For nonempty clopen `U, V ⊆ Ẑ` there is a
piecewise canonical homeomorphism `β : U → V`, with `P'`-smooth moduli.
- `U` is a disjoint union of `a` boxes and `V` of `b` boxes.
- Since `B(r, m) = B(r, 2m) ⊔ B(r + m, 2m)`, either count can be raised one box at a
  time. So both can be made equal to `max(a, b)`.
- Map the boxes to each other canonically. ∎

**Lemma C (transversals).** Let a finite group `W` act freely on a clopen `X ⊆ Ẑ` by
homeomorphisms. Then there is a clopen `Y` with `X = ⊔_{w∈W} wY`.
- Each `x` has a clopen neighborhood `U_x` whose `W`-translates are pairwise disjoint.
  Cover `X` by finitely many, `U_1, …, U_r`.
- Put `Y_1 = U_1` and `Y_j = Y_{j−1} ∪ (U_j ∖ W·Y_{j−1})`. Each step adds a clopen set
  whose translates are disjoint from each other and from `W·Y_{j−1}`.
- `Y = Y_r` works. ∎

**Proof of 1.**
- **Necessity.** A conjugator `c` maps each `ρ_1`-stabilizer stratum of `Z` onto the
  `ρ_2`-stratum with the same stabilizer.
- **Strata.** Choose `P` as in the statement, and write `F` acting on `Ẑ` via `ρ̂_i`. For
  `K ≤ F`, the set `X^i_K = {x : Stab(x) = K}` is a Boolean combination of the clopen
  sets `Fix(ρ̂_i(f))` (Lemma A), so it is clopen.
- **Stabilizers seen on `Z`.** `X^i_K ≠ ∅` iff it contains an integer, since `Z` is dense and
  boxes contain integers, i.e. iff `K ∈ S(ρ_i)`.
- **Transversals.** Pick one `K` from each conjugacy class in `S = S(ρ_1) = S(ρ_2)`.
  `W = N_F(K)/K` acts freely on `X^i_K`. Take a clopen transversal `Y^i_K` (Lemma C),
  and a piecewise canonical `β_K : Y^1_K → Y^2_K` (Lemma B).
- **Orbit structure.** The map `F/K × Y^i_K → F·X^i_K`, `(fK, y) ↦ ρ̂_i(f)y`, is a
  bijection:
  - onto, since `F·X^i_K = F·N(K)·Y^i_K`;
  - one-to-one, since `ρ̂_i(f)y = ρ̂_i(f')y'` forces `f^{-1}f' ∈ N(K)`, then `y = y'`, then
    `f^{-1}f' ∈ K`.
  The sets `F·X^i_K` partition `Ẑ` as `K` runs over the chosen representatives.
- **Conjugator.** Put `ĉ(ρ̂_1(f)y) = ρ̂_2(f)β_K(y)`.
  - It is well defined, because `Stab_2(β_K y) = K`.
  - It is bijective and `F`-equivariant.
  - On each clopen piece `ρ̂_1(f)Y^1_K` it equals `ρ̂_2(f) β_K ρ̂_1(f)^{-1}`, so it is
    piecewise canonical.
- **Membership.** Restricted to `Z`, `ĉ` is a piecewise canonical permutation with
  `P'`-smooth moduli. So `c ∈ CT_P(Z)` by item 3 of `ct-p-z-is-a-one-vertex-k-graph-full-group`. ∎

**Proof of 2.**
- **From 1.** Take `F = Z/n`. The stabilizer of a point is the subgroup of index equal to
  its cycle length.
- **Realization in `V`.** Any finite set `D` of cycle lengths is realized in `CT_∅(Z)`:
  split `Z` into `|D|` classes mod a power of 2, split the class for `d` into `d` boxes,
  and permute those boxes cyclically. So every torsion element is conjugate into `V`.
- **Decidability (3).** Lemma A computes `Fix(g^e)` for each `e | n` as a periodic set.
  The emptiness of Boolean combinations of periodic sets is decidable. ∎

## Consequences for 21.73

- **Where undecidability must come from.** Salo (arXiv:2011.07827, the 2V theorem of Section 4, label `thm:2V`,
  read at source) proves the conjugacy problem of `2V` undecidable. His yes-instances are pairs of
  finite-order elements, conjugate by an involution. By 2, no such pair in `CT(Z)` can
  encode anything, since its conjugacy is decided by the cycle-length sets. So an
  undecidability proof for 21.73 needs yes-instances of infinite order.
- **Why machines alone do not supply them.** For multiplicative counter-machine
  elements, "finite order" means uniform periodicity, which is decidable (Kari–Ollinger
  Thm 4). This is consistent with `ct-z-finite-cycle-problems-are-undecidable`.
- **A second obstruction: blind multiplication (heuristic sketch; referee bh-ref-d).**
  Multiplication by a rational is not itself a permutation of `Z`, so the steps below are a
  sketch, not a proof. Salo's blinkers are bits stored far from
  the head. Try the naive transfer of this idea to counter machines. Consider the counter-coded elements of `ct-z-finite-cycle-problems-are-undecidable`,
  where a bit is stored in the unit digits of a counter's `p`-adic coordinate.
  - Multiplying by a rational coprime to the machine primes changes those digits.
  - That multiplication commutes with the machine and is itself in `CT(Z)`.
  - So a conjugator can toggle the stored bit blindly: `(bit) ↦ (bit) ⊕ (dummy bit)` is a
    `CT(Z)` element conjugating Salo's `α` to `β`.
  - Positional markers therefore need additive (`V`-type) digit structure. Multiplicative
    counter moves scramble that structure.

## Lesson for general BH

**Homogeneity.** In the fp simple hosts `CT_P(Z)`, finite subgroups are homogeneous:
- An embedding of a finite group is determined up to conjugacy by the set of its point
  stabilizers.
- For free actions, all embeddings are conjugate.
- The mechanism is general. It needs:
  - torsion-free germs at fixed points, which gives clopen fixed sets;
  - clopen transversals;
  - `H_0`-trivial comparison, so that all nonempty clopen sets are equivalent.

**Uses for BH.**
- **Higman-style steps come for free.** Given an isomorphism `φ : A → B` of finite
  subgroups with matching stabilizer data, the host contains a stable letter `t` with
  `t a t^{-1} = φ(a)`. The induced map from the HNN extension to the host need not be
  injective. So finite subgroups never block the existence of stable letters.
- **The real difficulty lies elsewhere.** Hard embedding questions for such hosts concern
  infinite subgroups. The same holds for hard decision problems.
