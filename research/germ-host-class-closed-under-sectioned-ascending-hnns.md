---
rg: 2
id: germ-host-class-closed-under-sectioned-ascending-hnns
kind: claim
title: A class of cone-closed Thompson-like germ hosts contains all bounded Röver–Nekrashevych groups, embeds in finitely presented simple groups, and is closed under cone-sectioned ascending HNN extensions with F_infinity tail
distinct_from:
  f-infinity-tail-ascending-hnns-satisfy-boone-higman: that is one ascending HNN step over a bounded Röver–Nekrashevych group, under hypothesis (H0); this makes the step a closure operation on a host class (so it iterates), removes (H0) by a block-ray choice, and allows the base group to be any member of the class.
  hyperbolic-groups-satisfy-boone-higman: BBMZ's full contracting RSGs have virtually cyclic germ groups at rational points; the class here allows germ groups that are ascending HNN extensions of arbitrary F_infinity groups, e.g. Z[1/2]^2 ⋊ Z.
requires:
  - f-infinity-tail-ascending-hnns-satisfy-boone-higman
---

**ESTABLISHED** (lane proof `germ-host-class-hnn-closure-proof`; not reviewed; no priority
claimed).

## The class `𝓒_d`

Let `C = X^N` with `|X| = d ≥ 2` and last letter `L`. For `f ∈ Homeo(C)` and a word `α`, let
`f^{(α)}` act on the cone `αC` by `αw ↦ αf(w)` and fix everything else. `𝓒_d` is the class of
**full** groups `W ≤ Homeo(C)` satisfying:

- **(C1) Cone-closed.** `V_d ≤ W`, and `f^{(α)} ∈ W` for all `f ∈ W` and all words `α`.
- **(C2) Rational singularities.** The points where some element of `W` does not locally agree
  with `V_d` lie in finitely many tail classes of rational points.
- **(C3) `F_∞` stabilizer package.** For every nonempty clopen `U` and every finite set `M` of
  rational points outside `sing(W)`, the group `Fix_{W_U}(M)` has type `F_∞`. Here `W_U` is the
  set of elements of `W` supported in `U`.

## Theorem

1. **Seeds.** `V_d S ∈ 𝓒_d` for every bounded automata group `S ≤ Aut(T_d)`.
2. **Hosts.** Every `W ∈ 𝓒_d` is `F_∞`. It acts faithfully and highly transitively on a
   rational tail class outside `sing(W)`, with `F_∞` stabilizers of finite sets. So `W` embeds
   in the finitely presented simple group `SV_W`, and every subgroup of `W` satisfies
   **Boone–Higman** and lies in **`B_A`**.
3. **Closure.** Let `W ∈ 𝓒_d`, let `K ≤ W`, and let `φ: K → K` be injective and
   **cone-sectioned**: `φ(g)` preserves `LC` and acts there as `g^{(L)}`. Put
   `ψ(g) = φ(g)|_{C∖LC}` and define the **tail group**
   `E_φ(K) = image of g ↦ (ψ(φ^k(g)))_{k≥0}`. If `E_φ(K)` is `F_∞`, then `K*_φ` embeds in some
   `W' ∈ 𝓒_d`, with `sing(W') = sing(W) ∪` (one new rational tail class).

**Corollary (towers).** Start from a bounded automata group and apply finitely many
cone-sectioned ascending HNN steps with `F_∞` tails, each to a subgroup of the current host.
Every group obtained this way satisfies BH and PBH. This includes all instances of
`f-infinity-tail-ascending-hnns-satisfy-boone-higman` (Grigorchuk–Lysenok, the supergroup,
Fabrykowski–Gupta, Basilica). (H0) is not needed.

## When is an endomorphism cone-sectioned?

For `K ≤ Aut(T_d)` self-similar, `φ` is cone-sectioned exactly when `φ(K) ≤ St_K(L)` and the
section map `π = (·)|_L` satisfies `π∘φ = id`.

So `φ` must be a right inverse of a **virtual endomorphism** (a homomorphism `π` from a
finite-index subgroup `D ⊇ φ(K)` to `K`) whose self-similar action is faithful and lands in a
member of `𝓒`. The theorem thus converts BH for `K*_φ` into two checks:
- a self-similar realization in which `φ` splits a virtual endomorphism;
- a finiteness computation for the tail group.

## Lesson for general BH

`𝓒` is an **inductive host class for BH**: it has explicit seeds, its members are BH-hosts, and
it is closed under an operation that creates Baumslag–Solitar-type dilation dynamics. Neither
contracting RSGs nor Röver–Nekrashevych groups have this closure, since their germ groups at
rational points are virtually cyclic.

The mechanism is local: a new ascending HNN letter adds one singular tail class. At that class
the germ group is itself an ascending HNN extension, of the tail group. BHM's Appendix A
induction then turns "tail group `F_∞`" into "all SingFix groups `F_∞`". A route toward general
BH is to find more closure operations for `𝓒`, and to decide which decidable groups have
cone-sectioned self-similar realizations.
