# Malnormal exhaustion does not force finite cost: a calibration of the `Gamma_mal` methods

Date: September 17, 2026. Agent `b-p-fp3`, wave `swarm-0917`, role calibrator,
node `fpbs-fixed-price-non-amenably-generated-from-fg`.

## 0. Summary

The test group `Gamma_mal = U_n H_n` (with `H_n = <a, b_n>` and
`b_{n-1} = b_n a b_n^{-2}`) has recorded obstructions: no Gaboriau chain,
finite contacts, and no finitely generated wq-normal anchor. All three follow
from one subgroup-lattice property, **malnormal exhaustion**.

The world `W1 = F_inf = ker(F_2 -> Z)` has the same property, together with
every other lattice and extension feature of `Gamma_mal` used so far. Yet every
free action of `W1` has cost infinity. The world `W2 = Gamma_inf` (test case T5
of `research/artifacts/fpbs/docs/fixed-price-countable-passage.md`) has the
uniform rank bound `c* = 2` and fixed price 2, but its stages are not
malnormal.

So the two features of `Gamma_mal` split between a world of infinite cost and a
world of cost 2. The consequences:

- **Class kill (Proposition 2).** Consider an argument whose group-theoretic
  inputs about `Gamma_mal` are only lattice or extension data (the list (P1)–(P7)
  below), plus the hypothesis H. No such argument proves that free costs are
  finite. If one did, it would also prove that `W1` has finite cost and hence
  refute H.
- **Separating datum (Proposition 3).** Only the stage relations separate
  `Gamma_mal` from `W1`. For a stage pair `H <= G` and a new generator `t` with
  `<H, t> = G`, these relations are the kernel of `H * <t> -> G`. In `W1` this
  kernel is trivial at free-factor pairs `H < G` with `rank G = rank H + 1`
  (though `W1` also has malnormal pairs of equal
  rank with 3-letter relations, so what separates is relations at every step
  of a uniform-rank exhaustion). In `Gamma_mal` it is always nontrivial, and every
  nontrivial element has at least 3 `t`-letters, a bound that is attained.
- **What survives.** A proof for `Gamma_mal` must consume the stage relations.
  Among the recorded families, only detour packing (coset cycles) and the
  `L^2`/Fox computation do. Contact repair, chains, anchors, wq-normality,
  commensurators and descent from the cyclic overgroup do not.

## 1. The two calibration worlds

### W1: `F_inf = ker(F_2 -> Z)`

Take `F_2 = <a, b>` and the map `a -> 0`, `b -> 1`.

- **Basis.** Its kernel `W1` is free on `x_k = b^k a b^{-k}`, for `k` in `Z`
  (Reidemeister–Schreier). Put `S_n = <x_{-n}, ..., x_n>`.
- **(P1)** `W1` is locally free and not finitely generated.
- **(P2) Malnormal exhaustion.** Every finitely generated subgroup lies in some
  `S_n`, and each `S_n` is a free factor. Free factors of free groups are
  malnormal.
- **(P3) No finitely generated wq-normal anchor.** Let `L <= S` with `L`
  infinite and `S` malnormal. If `g` is not in `S`, then
  `L ∩ g L g^{-1} <= S ∩ g S g^{-1} = 1`. So `Q(L) <= S`. Applying this at every
  step of the transfinite chain, the wq-normal hull of `L` stays inside `S`. The
  same argument works verbatim in `Gamma_mal`.
- **(P4) No Gaboriau chain.** Nontrivial pairwise intersections of conjugates
  never leave a stage, by the same computation.
- **(P5) Finite contacts.** For an infinite anchor inside a stage, the
  first hull step `<Q(L)>` stays inside the stage, by (P3). So the
  finite-contact obstruction of
  `research/artifacts/fpbs-finite-contact-obstruction-2026-09-17.md` has the
  same hypothesis in `W1` as in `Gamma_mal`. That node,
  `fpbs-malnormal-subgroup-relations-finite-contacts`, is OPEN only because of
  its finite-`L` case, which is not used here.
- **(P6) Cyclic overgroup and shift.** `W1` is normal in the finitely generated
  `F_2` with quotient `Z`. Conjugation by `b` shifts `S_n` to `<x_{-n+1}, ..., x_{n+1}>`.
- **(P7) Finitely generated subgroups.** Every finitely generated subgroup is a
  finite-rank free group. So H gives it nothing that is not already
  unconditional.
- **Cost.** [G00] Prop VI.9 gives fixed price infinity, so every free action of
  `W1` has cost infinity.

A second version of (P6), with a cost-1 overgroup: `W1 x {1}` is normal in the
finitely generated group `F_2 x Z`. That group has fixed price 1, by [G00]
VI.24 (it has an infinite amenable normal subgroup), and the quotient is `Z^2`.
Upstream Attempts use `F_inf x Z` for the same purpose. That group has cost 1
but is not finitely generated.

### W2: `Gamma_inf` (T5)

`M = <a, b, t | t a t^{-1} = a b a^{-1}, t b t^{-1} = b^2>` and
`Gamma_inf = ker(M -> Z)`.

- `Gamma_inf` is locally free, with rank-2 stages `H_n = t^{-n} F_2 t^n`, so
  `c* = 2`.
- It is normal in a finitely generated group with quotient `Z`, and it has a
  shift.
- The stages are **not** malnormal: `A^{-1} H_0 A ∩ H_0 ⊇ <b>`. The resulting
  chain gives fixed price 2.

### `Gamma_mal`

- It satisfies (P1)–(P7), with the stages `H_n` in place of `S_n`. Malnormality
  of the stages is recorded in the node's Attempts.
- Like `W2`, it has `c* = 2`, rank-2 stages and `beta_1^(2) = 1`.
- By `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`, every free
  cost is 2 or infinity.

| feature | W1 = F_inf | Gamma_mal | W2 = Gamma_inf |
|---|---|---|---|
| locally free, not f.g. | yes | yes | yes |
| every f.g. subgroup in a malnormal f.g. stage | yes | yes | no |
| Gaboriau chain / f.g. wq-normal anchor | no | no | yes |
| normal in f.g. group, quotient `Z`, shift | yes | yes | yes |
| `c*` (uniform stage rank) | infinity | 2 | 2 |
| kernel of `H * <t> -> G` at stage pairs | always trivial | always nontrivial, >= 3 t-letters | nontrivial |
| free costs | all infinity | 2 or infinity (open) | all 2 |

## 2. Proposition 2 (lattice and extension data cannot prove finite cost)

**Statement.** Let `P` be any conjunction of (P1)–(P7). Then the implication
"`Lambda` satisfies `P` implies every free action of `Lambda` has finite cost"
is false. It is false even under H, unless H itself is false.

**Proof.** `W1` satisfies (P1)–(P7) and has cost infinity. H concerns only
finitely generated groups, and (P7) says those are free groups in `W1`. So an
argument from `H + P` to finite cost would show that `W1` has finite cost,
contradicting [G00] Prop VI.9 unconditionally. QED.

**What this kills.** It kills, as one class, every method for `Gamma_mal` whose
`Gamma_mal`-specific inputs lie in (P1)–(P7):

- contact or infinite-intersection repair of `E_a` from subgroup orbit
  relations;
- chain and wq-normal-anchor criteria, and commensurated or Proposition F
  anchors;
- descent from the cyclic overgroup `M = F_2 *_phi` using only its fixed price
  (in `W1` the overgroup is `F_2`);
- stage-by-stage bookkeeping that uses only malnormality of `H_n` in `H_{n+1}`
  and the shift.

These were already dead individually. The proposition gives the common reason:
each one is blind to `c*`. It also rules out patches that stay inside (P1)–(P7).

**What it does not kill.** Any argument that uses the uniform rank bound. That
bound is not a lattice property; the next proposition locates it.

## 3. Proposition 3 (the separating datum: forced stage relations)

**Setting.** Let `G` be a free group of finite rank. Let `H <= G` be malnormal
and finitely generated, and let `t` in `G \ H` satisfy `<H, t> = G`. Let
`pi : H * <t> -> G` be the natural map.

**(a) W1: the kernel is trivial.** If `rank G = rank H + 1`, then `pi` is
injective. For example, `H = S` is a free factor of `G = S'` with rank one
more.

- **Proof.** `H * <t>` is free of rank `rank H + 1 = rank G`. A surjection
  between free groups of the same finite rank is an isomorphism, because free
  groups of finite rank are Hopfian. QED.
- **Consequence.** No coset cycle through a `t`-edge exists. The detour
  families of `research/artifacts/fpbs/small-cancellation-family.md` §2 are
  empty.
- **Relative cost.** For every free action of `G`, `relC(R_G; R_H) >= 1`. Both
  `R_G` and `R_H` are treeable of cost equal to rank, and
  `C(R_G) <= C(R_H) + relC(R_G; R_H)`.
- **In W1.** Every generator for every stage pair has floor at least 1,
  whatever its length.

**(b) `Gamma_mal`: the kernel is nontrivial.** If `rank G <= rank H`, then `pi`
has nontrivial kernel.

- **Proof.** `H * <t>` has rank `rank H + 1 > rank G`. A free group of larger
  rank has no injection onto a free group of smaller rank, because the rank of
  a free group is an invariant. QED.
- **In `Gamma_mal`.** For `n < m`, `H_n` is malnormal in `H_m`, both have rank
  2, and `<H_n, t> = H_m`. So every such stage pair and generator has
  relations.

**(c) Every relation has at least 3 `t`-letters.** In setting (b), write a
nontrivial kernel element in cyclically reduced form,
`w = t^{e_1} h_1 t^{e_2} h_2 ... t^{e_k} h_k`, with `h_i` in `H \ {1}` and
`e_i` nonzero. Let `L(w) = sum |e_i|` be its number of `t`-letters. Then
`L(w) >= 3`.

- **Proof.** `H` embeds in `G`, so `k >= 1`. The cases with `L <= 2` are:
  1. **`t h = 1` or `t^2 h = 1` (`k = 1`).** Then `t^e` lies in `H` for some
     `e` in `{1, 2}`. Since `G` is torsion-free, `t^e` is nontrivial. It
     commutes with `t`, so `t^e` lies in `H ∩ t H t^{-1}`, and malnormality
     forces `t` into `H`, a contradiction.
  2. **`t^{±1} h_1 t^{∓1} h_2 = 1`.** Then `t^{±1} h_1 t^{∓1} = h_2^{-1}` is a
     nontrivial element of `H ∩ t^{±1} H t^{∓1}`. So `t` lies in `H`, a
     contradiction.
  3. **`t^{±1} h_1 t^{±1} h_2 = 1`.** Put `u = t^{±1} h_1`, which is not in
     `H`. Then `u^2 = t^{±1} h_1 t^{±1} h_1 = h_2^{-1} h_1`, which lies in `H`.
     In a free group `u` is nontrivial, so `u^2` is nontrivial. It commutes
     with `u`, so it lies in `H ∩ u H u^{-1}`, and malnormality forces `u` into
     `H`, a contradiction.

  QED.

**Sharpness.** For `H = H_{m-1} = <a, b_{m-1}>` inside `G = H_m`, with
`t = b_m`, the defining identity `b_{m-1} = b_m a b_m^{-2}` gives the relation
`t a t^{-2} b_{m-1}^{-1}`. It has exactly 3 `t`-letters.

**Packing reading.** In the detour lemma, a coset cycle through the `t`-edge at
`x` with `L` letters recovers that edge from the other `L - 1` `t`-edges. So
each detour needs at least 2 selected edges, and it contributes `q^{L-1} <= q^2`
to the divergence series (2.3)–(2.5). The floor `1` of world `W1` is what
remains when there are no detours. The positive floor
`fpbs-malnormal-coset-cycles-linear-perimeter` for a fixed `t` is what remains
when detours exist but grow only exponentially.

## 4. Where this leaves the node

- The claim for `Gamma_mal` is exactly finiteness of free costs, and the rank
  bound `c* = 2` is the only input separating it from `W1`. Proposition 3
  identifies the rank bound, at the level of a single stage pair, with the
  nontrivial kernel of `H_n * <t> -> H_m`, whose elements have at least 3
  `t`-letters.
- Hence any successful method must turn this kernel into cost. Two recorded
  families do this:
  1. detour packing, including the open `fpbs-mal-long-generator-packing-growth`;
  2. the `L^2`/Fox computation, which gives only the lower bound
     `beta_1^(2) = 1`.
- An upper-bound method that consumes relations and does not route through
  pseudocost would be new.
- **Calibration test for any new proposal.** Run it on `W1`, where its
  relation input is empty, and on `W2`, where its malnormality input fails.
  A proposal that returns finite cost on `W1` is wrong. A proposal that needs a
  chain does not apply to `Gamma_mal`.

The node stays OPEN. Nothing here proves finiteness of free costs for
`Gamma_mal`.

## References

- [G00] D. Gaboriau, *Coût des relations d'équivalence et des groupes*, Invent.
  Math. 139 (2000). Prop VI.9 (free groups have fixed price equal to rank,
  including infinity) and VI.24 (an infinite amenable normal subgroup gives
  fixed price 1).
- `research/artifacts/fpbs/docs/fixed-price-countable-passage.md`, test cases
  T1 and T5.
- `research/artifacts/fpbs/small-cancellation-family.md`, §2.
- `research/artifacts/fpbs-finite-contact-obstruction-2026-09-17.md`.
