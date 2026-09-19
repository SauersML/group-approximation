---
rg: 2
id: machine-labelled-lamp-products-are-nv-centralizers
kind: claim
title: For any subgroup K of a Brin-Thompson group, a product over Z of centralizer subgroups of K chosen position by position by a nondeterministic linear-time labelling is a centralizer in an embedding of K wr Z into a larger Brin-Thompson group, so identity-edge combinations over it lie in B_A
distinct_from:
  nv-machines-realize-linear-time-lamp-centralizers: that is the case K = Z/2 with one label, where the realized subgroups are the lamp subgroups U_A of the lamplighter; this allows any subgroup K of a Brin-Thompson group as lamp group, several labels, and a different realizable subgroup of K at each position, with membership decided along the orbit of one machine.
  centralizer-realizable-subgroups-are-pullback-closed: that realizes subgroups pulled back from B_A quotients, and finite intersections; the subgroups here are infinite products over computable labellings, and when D(t) varies without periodicity no pullback along a homomorphism to a B_A group produces them in general.
---

**ESTABLISHED** by `machine-labelled-lamp-products-are-nv-centralizers-proof` (lane proof,
bh-invent-11, 2026-09-18; not reviewed; no priority claimed).

## Setting

- `K ≤ n'V` is any subgroup, not necessarily finitely generated.
- For `j = 1, ..., r`, let `S_j ⊂ n'V` be finite, and put `D_j = C_K(S_j)`.
- A **labelling** is a map `Φ : Z → {subsets of {1..r}}` with `Φ(0) = ∅` such that, for each `j`,
  both `{s >= 1 : j ∈ Φ(s)}` and `{s >= 1 : j ∈ Φ(-s)}` are NLIN₁, in the sense of
  `nv-machines-realize-linear-time-lamp-centralizers`.
- Put `D(t) = ⋂_(j ∈ Φ(t)) D_j`, with `D(t) = K` when `Φ(t) = ∅`.
- In `K ≀ Z = (⊕_Z K) ⋊ ⟨a⟩`, the **machine-labelled product** is `C_Φ = ⊕_(t ∈ Z) D(t)`: the
  finitely supported `f` with `f(t) ∈ D(t)` for every `t`.
- Assume `D(·)` is **not eventually periodic**: for every `p ≠ 0`, `D(t) ≠ D(t+p)` for infinitely
  many `t`.

## Statement

There are an embedding `K ≀ Z ↪ NV`, with `N = n' + O(1)` depending on the verifiers, and an
element `m ∈ NV` with

```text
C_(K ≀ Z)(m) = C_Φ .
```

Hence `C_Φ` is centralizer-realizable in `K ≀ Z`, because `NV ∈ B_A`. By
`pbh-coset-wreaths-iff-identity-edge-hnns`, the following all lie in `B_A`:
- the coset lamplighter `Z/2 ≀_((K≀Z)/C_Φ) (K ≀ Z)`;
- the identity-edge HNN extension `⟨K ≀ Z, t | [t, c] = 1 (c ∈ C_Φ)⟩`;
- the double `(K ≀ Z) *_(C_Φ) (K ≀ Z)`.

They have solvable word problem when `K` is finitely generated, and they embed in finitely
presented simple groups.

## Scope

- **Lamp groups covered.** `K` ranges over all subgroups of Brin–Thompson groups. By
  `permutational-boone-higman-iff-full-cantor-hosts`, these include every virtually special group,
  every cubulated hyperbolic group, and `Q`.
- **Position subgroups covered.** Each `D(t)` is a finite intersection of centralizers of finite
  subsets of `n'V`. So it can be trivial, a clopen-support centralizer, or `K` itself.
- **How membership is decided.** For `f ∈ K ≀ Z`, deciding `f ∈ C_Φ` has two parts:
  - one run of the labelling machine for each position in `supp f`, which is linear in that
    position;
  - one centralizer test in `n'V` for each position.

  This is the sense in which membership is "computed along a machine orbit".

## Lesson for general BH (and for CAP)

**One host compiles.** A single finitely presented full host can decide, position by position
along the orbit of one machine element, which realizable subgroup a lamp must lie in. Commuting
with the detector `m` is exactly passing that test.
- So identity-edge permanence of `B_A` over machine-coded subgroups costs no new host.
- The subgroups are read off a computable orbit, with membership decidable, which is the shape
  that the SEED synthesis asks for with "seed-coded associated subgroups".

**The flip side for CAP.** Inside one host the compiler is capped.
- The labelling has linear time in the position, because a lamp at position `t` has only `t` steps
  of the machine.
- The detector test is in coNP of `NV`.
- By Britton's lemma, the word problem of one such HNN stage is polynomial time relative to those
  tests. So a tower whose every stage is compiled inside one fixed host keeps word problems in
  one fixed class, if such towers exist (see Open). The in-host compiler gives CAP-true behaviour
  on its own rung.
- Breaking a complexity cap needs hosts that vary with the input, or clopen orbits whose time per
  lamp index is unbounded. A fixed full host has neither, since time is the index.

**Open.**
- Does the identity-edge HNN embed back into some `NV`? That would let the compiler iterate inside
  Brin–Thompson groups.
- Can time be two-dimensional, i.e. lamp groups over `Z^2` with commuting machines? The proof uses
  that the orbit of one element is linearly ordered by time.
