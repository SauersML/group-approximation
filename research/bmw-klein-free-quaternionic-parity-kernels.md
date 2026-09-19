---
rg: 2
id: bmw-klein-free-quaternionic-parity-kernels
kind: claim
title: 31_30 #26 and 31_31 #12 embed in a quaternion division algebra over F_2(t), so their parity kernels have no Klein pair of any length and admit no Klein-power chain, yet a three-split cone certificate refutes left orders
distinct_from:
  bmw-census-klein-power-chain-certificates: that certifies classes by cycles containing a Klein step and proves that every Klein pair is conjugate to a pure pair; this proves that for #26 and #12 no Klein pair exists at all, so no such cycle can exist
  bmw-klein-frame-chain-certificates: that shows by finite search that #26 and #12 have no pure Klein pair with |A| < 18, |B| < 16; this removes the length bound by a faithful linear representation
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that refutes left orders on these two parity kernels with a SAT solver; this gives a solver-free cone certificate and the reason Klein chains fail
artifacts:
  - experiments/bmw-klein-free-2026-09-18/README.md
  - experiments/bmw-klein-free-2026-09-18/verify_quat_rep.py
  - experiments/bmw-klein-free-2026-09-18/verify_quat_rep.log
  - experiments/bmw-klein-free-2026-09-18/findquat.py
  - experiments/bmw-klein-free-2026-09-18/quat.py
  - experiments/bmw-klein-free-2026-09-18/gf2poly.py
  - experiments/bmw-klein-free-2026-09-18/dtree.py
  - experiments/bmw-klein-free-2026-09-18/verify_cone.py
  - experiments/bmw-klein-free-2026-09-18/tree_31_30_26.json
  - experiments/bmw-klein-free-2026-09-18/tree_31_31_12.json
  - experiments/bmw-klein-free-2026-09-18/verify_cone.log
  - experiments/bmw-klein-free-2026-09-18/levels.py
  - experiments/bmw-klein-free-2026-09-18/tori.py
  - research/bmw-klein-free-quaternionic-parity-kernels-proof.md
---

**ESTABLISHED.** The proof is in `bmw-klein-free-quaternionic-parity-kernels-proof`. Its finite
inputs (about 40 polynomial identities, and a 6-leaf cone tree per class) are checked exactly by
`verify_quat_rep.py` and `verify_cone.py`.

Let `Γ` be the BMW group of class `31_30` #26 or `31_31` #12 (`census_31_30.json`,
`census_31_31.json` in `experiments/bmw-census-left-orders-2026-09-17/`), and `Γ^+` its parity kernel.
These are the two classes for which no Klein-type certificate was found
(`bmw-census-klein-power-chain-certificates`, `bmw-klein-frame-chain-certificates`).

## Statement

Let `K = F_2(t)` and `D = [t, t²+t+1)`, the quaternion algebra with `i² = i + t`, `j² = t²+t+1` and
`j i = (i+1) j`. It is a division algebra, ramified exactly at `t²+t+1` and `∞`.

1. **Faithful representation.** An explicit `ρ : Γ → D^*/K^*` sends each letter to an element with
   coordinates of degree at most 2. It is injective. It turns the action of `Γ` on `T_3 × T_3` into
   the action of `D^*/K^*` on the product of the Bruhat–Tits trees of `PGL_2(F_2((t)))` and
   `PGL_2(F_2((t+1)))`. The Γ-equivariant map between the two products is an isomorphism.
   - `31_30` #26: `h_0 = t+i+j`, `h_1 = (t+1)+i+j`, `h_2 = t+j`, `v_0 = ij`,
     `v_1 = (t²+t+1)+(t+1)j`, `v_2 = j+ij`.
   - `31_31` #12: the same `h_0, h_1, h_2`, and `v_0 = 1+i`, `v_1 = i`, `v_2 = (t+1)+j`.
2. **Irreducible.** `⟨A⟩` acts faithfully on the vertical tree, so `Γ` is irreducible.
3. **No Klein pair, of any length.** If `a, b ∈ Γ` with `b ≠ 1` and `a b a^{-1} = b^{-1}`, then `a² = 1`
   or `b² = 1`. Hence `Γ^+`, which is torsion-free, has no Klein pair. More generally, if `b ∈ Γ^+ \ {1}`,
   `a ∈ Γ^+` and `a b^p a^{-1} = b^q` with `p, q ≠ 0`, then `p = q`. So `Γ^+` contains no Klein-bottle
   group and no Baumslag–Solitar group `BS(p,q)` with `p ≠ q`.
4. **Class-killing obstruction.** No Klein-power chain (Corollary 3 of
   `bmw-census-klein-power-chain-certificates-proof`) exists for `Γ^+`, or for any torsion-free
   subgroup of `Γ`. Every such chain needs a (K) step. The conjugate-frame and pure-word searches of the
   earlier nodes were therefore empty for a structural reason, at every length.
5. **A non-Klein certificate.** `Γ^+` is still not left-orderable. For each class there is a
   cone-propagation tree, found by `dtree.py`:
   - three nested sign choices, six leaves;
   - every leaf closes by multiplying positive elements of the radius-4 ball until `x y = 1`;
   - there are 54 product identities per class, and the second half of each tree mirrors the first
     under `P ↔ P^{-1}`.

   `verify_cone.py` checks it with its own rewriting normal form. No SAT solver is involved.

## Why it matters for the method

The Klein-power method orders elements through relations `a b a^{-1} = b^{-1}` and powers
`x = r^e`, `y = r^f`, and it needs at least one Klein step to get a strict inequality. The lemma behind
part 3 holds in `PGL_2(F)` for every field `F`:
- if `a b a^{-1} = b^{-1}` and `b ≠ 1`, then `a² = 1` or `b² = 1`;
- a semisimple `b` can only be inverted by swapping its two eigenlines;
- a unipotent `b` is inverted only by a trace-zero `a`, or is itself an involution in characteristic 2.

So the obstruction holds for every BMW class whose `Γ` embeds in some `PGL_2(F)`: its parity kernel
has no Klein-power chain. Certificates for such linear lattices need genuinely non-abelian cone
arguments, like the trees in part 5.

## Attempts

- (w9-107, 2026-09-18) Parity phenomenon first (`tori.py`): in the fixed-letter graph every inverter
  of a pure word has odd length, and the shortest ones are single involution letters (e.g. `h_2`
  inverts `v_0v_1v_0v_2v_0v_2` in #26). Part 3 explains this, since every inverter is an involution.
- (w9-107) The level orders of `⟨A⟩` on `T_v` for #26 are `6, 48, 384, 1536, 12288, 49152`
  (`levels.py`). They grow like `|PGL_2(F_2[t]/t^n)|` up to a factor `2^{⌊(n−2)/2⌋}`, which suggested
  a characteristic-2 congruence structure. A split algebra is impossible because the lattice is
  cocompact. `findquat.py` then searched `D = [t, t²+t+1)` with coordinates of degree at most 1 (#12) or 2 (#26), and
  found the representations above. For #12 there are two with the h-tree at `t+1` and two with the
  h-tree at `t`. For #26 there are two with the h-tree at `t+1` and none with the places swapped.
