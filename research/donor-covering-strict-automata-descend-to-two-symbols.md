---
rg: 2
id: donor-covering-strict-automata-descend-to-two-symbols
kind: claim
title: A strict automaton whose active sites each relay to an output site descends to a binary one over G × C_p once it has at most two rest symbols, and with two rest symbols this is equivalent to universal binary descent
distinct_from:
  binary-shifts-over-odd-fibers-split-off-the-augmentation-shift: that reduces a binary witness over G × P to a P-equivariant strict automaton on the augmentation shift; this builds such equivariant automata from label-level data, a donor-covering strict automaton on the orbit alphabet, with no condition on phases.
  passive-fixing-injective-automata-are-surjective: that proves designs keeping reserved symbols in place are surjective; this allows rest symbols to be rewritten and active sites to be created, and requires only that no active site is lost without a relay.
  local-passivity-preserving-injective-automata-are-surjective: that kills designs which fix locally passive sites and create no active site; this is a positive transfer theorem for automata that may create active sites, where the obstruction is the number of rest symbols.
  some-nonsurjunctive-group-gives-a-binary-one: that is universal binary descent; this proves it is equivalent to reducing the rest alphabet of a donor-covering strict automaton to two symbols, with the active alphabet free up to its 2-adic valuation.
  modular-matrix-failures-descend-to-scalars-over-g-times-p: that descends characteristic-two linear witnesses over G × P; this descends nonlinear witnesses of a combinatorial shape, and linear witnesses need not have that shape.
artifacts:
  - experiments/donor-covering-descent-2026-09-17/check.py
---

**ESTABLISHED** by `donor-covering-phase-transport-proof`. Elementary.

**Setting.** `G` is a group. A finite alphabet is split as `L = Z ⊔ B`, with *rest* symbols `Z` and a nonempty set
of *active* symbols `B`. An automaton `τ` on `L^G` has the form `τ(ℓ)(g) = μ((g^(-1)ℓ)|_M)`, with `M ∋ 1` finite
and `(g^(-1)ℓ)(m) = ℓ(gm)`. Call `τ` *donor-covering* if there is a map `d` from `{u ∈ L^M : μ(u) ∈ B}` to `M`
such that, writing `D_ℓ(g) = g·d((g^(-1)ℓ)|_M)` (the *donor* of an active output site `g`):
- **(D1)** `ℓ(D_ℓ(g)) ∈ B` whenever `τ(ℓ)(g) ∈ B`;
- **(D2)** for every `ℓ` and every `h` with `ℓ(h) ∈ B`, some `g` with `τ(ℓ)(g) ∈ B` has `D_ℓ(g) = h`.

So active output sites read an active input site nearby, and every active input site is read by at least one
of them. Call `(|Z|, |B|)` the *type*. A *strict* automaton is injective and not surjective.

**Theorem.**
1. **Phase transport.** Let `F` be a finite group and `C` a finite `F`-set on which `F` acts freely off its set
   `Z_C` of fixed points. Let `σ: C → L = C/F`, with the fixed points as rest symbols and the free orbits as
   active symbols. If `τ` on `L^G` is strict and donor-covering, then there is a strict automaton `Φ` on `C^G`
   that commutes with the symbolwise `F`-action, satisfies `σ∘Φ = τ∘σ`, and is donor-covering for
   `C = Z_C ⊔ (C \ Z_C)`, with the same memory.
2. **Tag multiplication.** If `G` carries a strict donor-covering automaton of type `(z, b)`, it carries one of
   type `(z, bt)` for every `t >= 1`.
3. **Binary witnesses.**
   - (a) If `G` carries a strict donor-covering automaton of type `(2, (2^p - 2)/p)` for a prime `p`, then
     `G × C_p` is not surjunctive over two symbols.
   - (b) If `G` carries one of type `(1, (2^(q-1) - 1)/q)` for an odd prime `q`, then `G × C_q` is not
     surjunctive over two symbols.
4. **Admissible types.** For every odd `c >= 1` there are infinitely many primes `q` with `c | (2^(q-1) - 1)/q`.
   Hence if some group carries a strict donor-covering automaton of type `(1, b)` with `b` odd, or of type
   `(2, b)` with `4 ∤ b`, then `2 ∈ NS_all` (notation of `ec-groups-share-the-nonsurjunctive-alphabet-sizes`).
5. **Reformulation.** Every strict automaton `β` on `A^G` gives a strict donor-covering automaton of type
   `(|A|, |A|)` on `G`: `β × id` on `(A × {rest, active})^G`, with donor `d ≡ 1`. Therefore:
   - `2 ∈ NS_all` iff some group carries a strict donor-covering automaton of type `(2, b)` with `4 ∤ b`;
   - `some-nonsurjunctive-group-gives-a-binary-one` is equivalent to: if some group carries a strict
     donor-covering automaton of some type `(k, k)`, then some group carries one of type `(2, b)` with `4 ∤ b`.

**What this changes.** The recorded products-with-a-finite-group design
(`research/artifacts/gk3-alphabet-descent-2026-09-14.md`, Section 4.3) embeds a strict pair over `[k]` in the free
orbits of `{0,1}^(C_p)`, tags invalid cells and constant fibers, and dies by the count `k(N - k + 3) > N`. Here there
are no invalid cells, since tag multiplication matches `|B|` to the orbit count exactly. The constant fibers are
symbols of the witness itself, not tags. Phases travel along donors, so none is spent twice. Orbit counting is never
the obstruction. The whole obstruction is the number of rest symbols: from `k` down to `2`, or to `1` with odd `|B|`.

**Scope.**
- The active part is free only up to its 2-adic valuation. `(2^p - 2)/p = 2·(2^(p-1) - 1)/p` with the second factor
  odd, so types `(2, b)` with `4 | b` are not reached by this route.
- `Φ` keeps relative input phases where they are. A general `ζ`-homogeneous automaton on `R_q^G` can let output
  labels depend on relative phases, so item 1 does not describe all equivariant witnesses.
- With one rest symbol a strict donor-covering automaton must raise the number of active sites on some finite
  configuration (`one-rest-donor-covering-strict-automata-raise-the-count`).
- Off groups the class is not empty. The copying rule `x(p(v))` of `end-fixing-tree-symmetries-carry-strict-automata`
  is donor-covering of type `(1, |A| - 1)` with donor `p(v)`, and the formulas of item 1 turn it into the
  parent-copy rule on `C^V`. On a group this mechanism is absent, as that node records.

**Calibration** (`experiments/donor-covering-descent-2026-09-17/check.py`). Over `G = C_n`, exhaustively on all
configurations and for 40 random donor-covering rules per fiber, `Φ` commutes with translation and with the fiber
action, `σ∘Φ = τ∘σ`, `Φ` is injective whenever `τ` is, and `Φ` is not surjective whenever `τ` is not. Fibers:
`R_5` (type `(1,3)`), `{0,1}^(C_3)` (type `(2,2)`), `{0,1}^(C_2)` (type `(2,1)`), and the tag fiber `{0} ⊔ C_3`.
Orbit counts are checked for `p <= 13`, and item 4 for odd `c < 400`.
