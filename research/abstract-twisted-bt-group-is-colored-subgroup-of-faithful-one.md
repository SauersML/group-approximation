---
rg: 2
id: abstract-twisted-bt-group-is-colored-subgroup-of-faithful-one
kind: claim
title: Every abstract twisted Brin--Thompson group is the subgroup of S-colored elements of a faithful twisted Brin--Thompson group, obtained by adding a free orbit to the action
distinct_from:
  abstract-btb-pairs-fp-and-relatively-simple: that imports finite presentation and relative simplicity of the abstract group from FFWZ; this realizes the abstract group concretely as a group of homeomorphisms inside a faithful twisted Brin--Thompson group.
  ffwz-nonfaithful-stein-stabilizers-contain-canonical-kernel: that shows the quotient action on the Stein complex of SV_(G/K) has the wrong stabilizers; this supplies a faithful ambient groupoid whose S-colored Stein complex has the right ones.
---

**ESTABLISHED** by `abstract-twisted-bt-colored-subgroup-proof` (lane proof, elementary).
Referee a (proof gaps): **PASS**,
`research/artifacts/gq-referee-a-abstract-twisted-bt-type-fn-criterion.md` (efa4f3b5c), nits
applied. Referee c (independent second pass): **PASS**,
`research/artifacts/gq-referee-c-abstract-twisted-bt-type-fn-criterion.md` (72d2941ac).
Citation pass (gq-referee-b) requested. No priority claimed.

## Statement

Let a group `G` act on a non-empty set `S`, with kernel `K`, possibly non-trivial. Let
`S' = S ⊔ G`, with `G` acting on the second summand by left multiplication, so `G ↷ S'` is
faithful.
- Let `S'V_G` be the (faithful) twisted Brin--Thompson groupoid of Belk--Zaremsky,
  arXiv:2001.04579, acting on the Cantor cubes `C^{S'}(n) = (C^S × C^G)(n)`.
- Let `SV_G^{abs}` be the abstract twisted Brin--Thompson groupoid of
  Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, Section 2.3.

Then:
1. The assignment that is the identity on multicolored forests in the colors `S`, on
   permutations and on `G`-twists extends to an **injective** groupoid homomorphism
   `Ψ: SV_G^{abs} → S'V_G`.
2. Its image is the **`S`-colored subgroupoid**: elements `f_2^{-1} t f_1` with `f_1, f_2`
   multicolored forests using only colors in `S` and `t` a `G`-twist. Restricting to rank and
   corank one, the abstract twisted Brin--Thompson group `SV_G` is isomorphic to the
   subgroup `Σ ≤ S'V_G` of `S`-colored elements.
3. The canonical kernel `SK_G` (elements `[T, id, (k_i), T]`, `k_i ∈ K`) maps to
   homeomorphisms that fix every `S`-coordinate and permute the `C^G` coordinates. The
   quotient `SV_G → SV_(G/K)` is "forget the `C^G` factor".

## Lesson for general BH

A non-faithful action is a faithful action with invisible coordinates. Every statement about
abstract twisted Brin--Thompson groups can be read inside a faithful groupoid of Cantor
homeomorphisms, where the Belk--Zaremsky machinery applies (splits, partitions, twisted
permutations, stabilizers of Stein cells). This is what repairs the non-faithful finiteness
theory (`abstract-twisted-bt-type-fn-criterion`) and with it the relative permutational
route.
