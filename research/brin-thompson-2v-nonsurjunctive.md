---
rg: 2
id: brin-thompson-2v-nonsurjunctive
kind: claim
title: The Brin–Thompson group 2V carries an injective non-surjective cellular automaton
distinct_from:
  thompson-v-nonsurjunctive: that names Thompson's V; this names the Brin–Thompson group 2V, which contains V, so that claim implies this one and not conversely.
  leavitt-unit-group-nonsurjunctive: that names the unit group of L_(F_2)(1,2); this names 2V, the product-cylinder permutation units of L_(F_2)(1,2) ⊗ L_(F_2)(1,2).
artifacts:
  - research/artifacts/brin-thompson-2v-gottschalk-host-2026-09-12.md
  - research/artifacts/brin-thompson-2v-obstruction-state-profile-2026-09-12.md
---

**OPEN.** Let `C = {0,1}^N` and let `2V` be the Brin–Thompson group: the homeomorphisms of `C × C` that cut
`C × C` into finitely many product cylinders `[α] × [γ]` and send each onto another product cylinder by prefix
replacement in both coordinates. Exhibit a finite alphabet `A` and a cellular automaton on `A^(2V)` that is
injective and not surjective.

**Consequences.** A proof refutes `gottschalk-surjunctivity-conjecture` and shows that `2V` is not sofic
(`sofic-groups-are-surjunctive`).

**Why this host.**
- `V <= 2V`, so `thompson-v-nonsurjunctive` implies this claim
  (`thompson-v-nonsurjunctivity-ascends-to-brin-thompson-2v`). The linear gate for `2V` is implied by the
  gate for `V` (artifact Corollary 2.2).
- The binary Theorem B (`binary-cyclic-corner-full-iff-complement-corner-has-no-state`) holds for `F_2[2V]`
  (artifact Proposition 2.1). Its scope paragraph covers only subgroups of the units of `L_(F_2)(1,2)`. Its proof
  uses three inputs, and each holds in `2V`:
  - the identities among `g`, its halvings and the nine-cylinder units;
  - an injective halving endomorphism `D` of the host;
  - `D(h)` commuting with `g`.
- `2V` contains the ternary baker unit `u = Σ_i s_i ⊗ t_i`, which conjugates `V ⊗ 1` onto `D(V) ⊗ 1`. So the
  halving endomorphism of Theorem B is inner in `2V`. No element of `V` conjugates `V` into `D(V)`
  (artifact Lemma 2.3).

## Attempts
* **Theorem B transfer (w6-free-neg-d, 2026-09-12; artifact Sections 1–2).** Worked in the unit model of `2V`
  inside `L_(F_2)(1,2) ⊗ L_(F_2)(1,2)`. Put `e = 1 + [g ⊗ 1] + [g² ⊗ 1]` and `T = (1 - e) F_2[2V] (1 - e)`. If
  `(K_0(T), [T])` has no state, then `e` is full (`brin-thompson-2v-order-three-averaging-idempotent-is-full`),
  `F_2[2V]` is not directly finite, and this claim holds. The corresponding condition for `V` implies it. Status:
  the reduction is on paper and awaits verification. The gate is open.
* **Baker unit and product tower (w6-free-neg-d, 2026-09-12; artifact Propositions 2.4–2.5).** Conjugation by
  `u` turns the halving homomorphism `ψ(x) = e D(x)` on `F_2[V ⊗ 1]` into multiplication by
  `1 + [1 ⊗ g] + [1 ⊗ g²]`, and the tower idempotents `E_k` into external products `E_(k-j) ⊗ E_j`. A state of
  `K_0(F_2[2V])` gives the four products of `e ⊗ 1`, `f ⊗ 1` with `1 ⊗ e`, `1 ⊗ f` the values `a, b, b, 2b`, with
  `a + 4b = 1`. Where it stopped: `b = 0` (augmentation) and `b = 2/9` (independent product of the regular
  values) satisfy every relation coming from finite subgroups and `u`. An obstruction must use elements of
  infinite order that mix the two coordinates.
* **The baker subgroup reduces to V (w6-free-neg-d, 2026-09-12; artifact Section 4).** `H_u = ⟨V ⊗ 1, u⟩` is the
  ascending HNN extension of `V` along `D`, and a ternary shift index in the second coordinate detects the stable
  letter. `H_u` is sofic iff `V` is (`sofic-kernel-amenable-quotient-permanence`). Every idempotent and relation of
  the previous attempt lies in `F_2[H_u]`. So a fullness proof built from that lever alone would show `V` is not
  sofic. Where it stopped: `(V ⊗ 1) × (1 ⊗ V)`, `H_u` and `⟨1 ⊗ V, u⟩` each contain `g ⊗ 1` and are sofic iff `V`
  is. A proof specific to `2V` needs `b` and `c` whose supports do not lie together in any one of them, for
  example inside `⟨V ⊗ 1, 1 ⊗ h, u⟩`.
* **The gate reduces to one value (w7-2v-mixed-support, 2026-09-12; artifact
  `brin-thompson-2v-obstruction-state-profile-2026-09-12.md`).**
  - Tower positivity bounds `b` by `2/9`, and a state with `b > 0` yields one with `b = 2/9`. So the linear gate
    for `2V` holds iff no state of `K_0(F_2[2V])` gives `e` the value `1/3`.
  - Such a state has the profile `(1/9, 2/9, 2/9, 4/9)`. The augmentation (`b = 0`) cannot be killed and does not
    matter.
  - In `⟨V ⊗ 1, 1 ⊗ h, u⟩`, `1 ⊗ h = (1 ⊗ k)(1 ⊗ g)(1 ⊗ k)^(-1)` for an explicit `k` in `V`, so it adds no torsion
    class.
  - Where it stopped:
    - An obstruction must use a relation that is not a conjugation and does not live in `L_3`.
    - A relation living in `V_1 × V_2`, `H_u` or `⟨V_2, u⟩` would already show that `V` is not sofic.
    - A firewall needs one state with `s[e] = 1/3`.
    - Partial-support torsion does not exclude the profile (artifact Section 6). Order-three elements of `V` form
      two conjugacy classes. At the profile, the class with a fixed point takes a value `y` in `[1/3, 5/9]`. The
      regular values (`1/|F|` on each finite subgroup `F`) satisfy every finite-subgroup identity.
  - Status: `w3-vf-nonlinear` re-derived the artifact and PASSED it (verification artifact Section 31,
    83970f5256). Nothing about the gate is decided, and this claim stays OPEN.
