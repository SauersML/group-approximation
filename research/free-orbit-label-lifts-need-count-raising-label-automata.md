---
rg: 2
id: free-orbit-label-lifts-need-count-raising-label-automata
kind: claim
title: A strict automaton that commutes with a free fibre action and lifts a label automaton forces the label automaton never to lower, and sometimes to raise, the number of active sites
distinct_from:
  one-rest-donor-covering-strict-automata-raise-the-count: that assumes relays (D1, D2) on an injective label automaton and reads off the count; this assumes only that some strict equivariant lift exists, with arbitrary phase rules and a label automaton that need not be injective, and gets the same count behaviour from a fibre count.
  donor-covering-strict-automata-descend-to-two-symbols: that builds lifts from donors; this is a necessary condition for every lift through free orbits with one fixed symbol, donor-based or not.
  binary-shifts-over-odd-fibers-split-off-the-augmentation-shift: that turns binary witnesses over G × C_q into ζ-homogeneous automata on R_q^G; this constrains the ζ-homogeneous automata whose orbit labels evolve on their own.
  passive-fixing-injective-automata-are-surjective: that kills designs keeping reserved symbols in place; this kills lifts over label automata that lose active sites on balance, whatever they do at single sites.
artifacts:
  - experiments/affine-relay-lifts-2026-09-17/check.py
---

**ESTABLISHED** by `free-orbit-label-lift-fibre-count-proof`. Elementary given the charge theorem.

**Setting.** `G` is a group and `F` a finite group with `|F| >= 2`. `C` is a finite `F`-set with exactly one
`F`-fixed symbol `0`, on which `F` acts freely off `0`. `L = C/F = {0} ⊔ B`, with orbit map `σ: C → L`, applied
sitewise. For a configuration with finitely many non-`0` sites, `|ℓ|` is their number.

**Theorem.** Let `θ` be an injective automaton on `C^G` that commutes with the symbolwise `F`-action. Suppose
`σ∘θ = τ∘σ` for an automaton `τ` on `L^G` (the orbit labels of the output depend only on the orbit labels of the
input). Then:
1. `θ(0^G) = 0^G`, `τ(0^G) = 0^G`, and `τ` maps finite label configurations to finite ones;
2. for every finite label configuration `m`, `Σ_{ℓ finite, τ(ℓ) = m} |F|^|ℓ| <= |F|^|m|`; in particular
   `|τ(ℓ)| >= |ℓ|` for every finite `ℓ`;
3. if `θ` is not surjective, then `|τ(ℓ)| > |ℓ|` for some finite `ℓ`.

**Consequence: a class kill.** Every route to a binary witness over `G × C_q` of the form "take a label automaton
`τ` with one rest symbol and lift it equivariantly through the free orbits of `R_q`" dies at item 2 or 3 unless `τ`
is a *one-rest Hilbert hotel*: it never lowers the finite active count and raises it somewhere. This covers every
phase rule, including rules in which output phases are arbitrary equivariant functions of the input phases in the
window, and label automata that are not injective. In particular:
- The label automaton `β^k` of a strict `β` (with `k` chosen so that `β^k` fixes all constants, one constant symbol
  declared rest and all others active) has no strict lift unless it is count-monotone. That depends on `β`, not on the
  lift.
- A reclassification of `β × id` with one rest symbol dies wherever the count drops. Single-site deaths matched by
  births elsewhere are not excluded by this theorem, but they are by D2. The gap between the two is recorded in
  `affine-relay-label-lifts-descend-to-two-symbols`.

**Scope.** Only lifts are covered. A general `ζ`-homogeneous automaton on `R_q^G` may let output labels depend on
relative input phases, and then no label automaton `τ` exists.
