---
rg: 2
id: fp-annular-germ-groups-are-hnn-recursive
kind: claim
title: If an annular host over V is finitely presented, its germ group at the singular point is an HNN extension over a finitely generated group of depth-sequences, with associated isomorphism the depth transport; so every input there lies in a finite tree of copies of one fg group of V-sequences
distinct_from:
  annular-hosts-with-free-zoom-germs-are-not-finitely-presented: that proves the window lemma and kills the free-zoom extreme; this gives the general shape of every fp annular germ group (Bieri–Strebel), of which free zoom (trivial associated subgroups), normal zoom and ascending zoom are special cases.
  dynamically-v-separated-groups-satisfy-boone-higman: that is the ascending case L_1 = L, where the host is fp; this shows every fp annular host is of HNN type, ascending or not.
  block-power-germ-schedules-with-fp-germ-group-are-exponential: that applies Bieri–Strebel to one metabelian germ group; this applies it to every annular germ group.
---

**ESTABLISHED** (lane proof, elementary given the cited inputs; not reviewed; no priority claimed).

**Setting.** Let `E = ⟨V, x_1, …, x_k⟩ ≤ Homeo(C)` be an annular host at `p = 0^∞`. Each `x_i`
fixes `p`, is V-local off `p`, and maps every annulus `A_n = 0^n 1 C` (n ≥ n_0) to itself. Let
`E_p` be the germ group and `B_p ≤ E_p` the germs preserving all deep annuli. Then
`B_p ↪ ∏_n V / ⊕_n V`, via each germ's action on `A_n ≅ C`.

**Theorem.** Suppose `E` is finitely presented. Then:
1. `E_p` is finitely presented, and `deg: E_p → Z`, the annulus shift, is a surjective
   homomorphism with kernel `B_p`.
2. (**HNN-recursive form**) There are finitely generated subgroups `L_1, L_2 ≤ L ≤ B_p`, an
   isomorphism `θ: L_1 → L_2` and an element `s = t b` (`b ∈ B_p`) such that
   `E_p = ⟨L, s | s^{-1} ℓ s = θ(ℓ), ℓ ∈ L_1⟩` (HNN extension).
3. (**Depth transport**) For `ℓ ∈ L_1` and all large `n`, the depth-`(n+1)` datum of `ℓ` equals
   the depth-`n` datum of `θ(ℓ)`, conjugated by `b(n)`.
4. Every finitely generated `P ≤ B_p`, in particular every input placed in `B_p`, lies in the
   finite tree of groups `⟨s^j L s^{-j} : |j| ≤ J⟩` for some `J`. By Britton's lemma, this is an
   iterated amalgam of copies of `L` along `L_1 ≅ L_2`.
5. Every finitely presented subgroup of `B_p` is residually V.

**Proof.**
1. The first statement is `fp-germ-extensions-of-locally-moving-bases-have-fp-germ-groups`,
   base `V`. For `deg`: `V`-germs at `p` are powers of the zoom `t`, which has shift 1. The
   `x_i` have shift 0. A product of germs shifts deep annuli by the sum, so `deg` is a
   homomorphism with kernel `B_p`.
2. This is Bieri–Strebel (1978; cited, not re-read): a finitely presented group with an
   epimorphism onto `Z` is an HNN extension with finitely generated base and associated
   subgroups inside the kernel, and stable letter mapping to 1.
3. Write `s = t b` and read `s^{-1} ℓ s = θ(ℓ)` coordinatewise, using
   `(t^{-1} y t)(n) = y(n+1)`.
4. `B_p` is the normal closure of `L` in `E_p`, i.e. the union of the `s^j L s^{-j}`. A finite
   generating set of `P` uses finitely many `j`.
5. A finite presentation of `P` has finitely many relators. They hold at every depth
   `n ≥ n_1`, where each coordinate is then a homomorphism `P → V`. A nontrivial element is
   nontrivial at infinitely many depths.

**Special cases.**
- `L_1 = 1`: the free-zoom germ group `L * ⟨s⟩`. It is never realized by an fp host
  (`annular-hosts-with-free-zoom-germs-are-not-finitely-presented`).
- `L_1 = L`: the ascending case, realized by fp hosts
  (`dynamically-v-separated-groups-satisfy-boone-higman`).
- The Bishop–Schesler depth-disjoint host is `H ≀ Z`, which is not fp at all
  (`depth-disjoint-spinal-hosts-have-wreath-germ-groups`).

## Lesson for general BH

Every finitely presented one-point germ host over `V` computes its deep data by **one partial
isomorphism**. `θ: L_1 → L_2` transports depth `n+1` to depth `n` on a finitely generated
subgroup, and everything else is assembled from finitely many seed sequences. That is the
algebraic form of the local rigidity principle at one point. The design space for
Boone–Higman through such hosts is exactly the triples `(L, L_1, θ)` of finitely generated
groups of V-sequences with shift-compatible `θ`. Ascending `θ` is the self-similar /
dynamically-separated case. **Non-ascending `θ` with `L_1` of infinite index**, a transport
defined on only part of the data, is the unexplored regime. It is where a machine-like
compiler would have to live (open target `fp-rf-groups-embed-in-hnn-recursive-annular-germ-groups`).
Items 4–5 also show that such hosts reach only inputs that are locally embeddable into V. A
finitely presented one is residually V. Since V has only finite Kazhdan subgroups, no infinite
finitely presented Kazhdan group placed in `B_p` survives. This is consistent with
`zero-set-confinement-unifies-host-obstructions`.
