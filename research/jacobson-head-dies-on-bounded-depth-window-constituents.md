---
rg: 2
id: jacobson-head-dies-on-bounded-depth-window-constituents
kind: claim
title: In every window model of an EL_20(J)-set, the Jacobson head is killed on every bounded-depth symmetric or alternating constituent, at rate (depth x window defect)^(1/4)
distinct_from:
  kazhdan-unitary-corners-require-finite-dimensional-mass: that is the general corner-mass inequality for a corner of one genuine representation, whose tuple is compared generator by generator; this turns a permutation window of an E-set into such a corner for every bounded-depth Sym(F) isotypic block at once (diagonal uniformity of the block), and adds the fact that the finite-dimensional sector of EL_20(J) is blind to L, so the head is killed constituent by constituent.
  kazhdan-representations-have-no-hs-compression-models: that needs a representation with no finite-dimensional part, as for an infinite simple group; EL_20(J) has many finite-dimensional representations through the symbol, and this shows that they carry the corner mass but not the head.
  jacobson-head-concentrates-on-template-constituents: that says the head of a finite-group model lives on template constituents and leaves alternating-type constituents open; this kills the alternating and symmetric constituents of bounded depth whenever the generator permutations are truncations of a genuine E-action, the test recorded as its next step.
  binary-jacobson-el3-is-sofic: its truncation attempts treat vectors and Grassmannians case by case in rank three; this is uniform over every E-set, including configuration and coset spaces, and over every bounded-depth unitary constituent.
  kazhdan-consistent-partial-models-round-to-finite-actions: that is the open general rounding of consistent partial permutation models; this is the special case where the partial model is literally a restriction of a genuine action, which needs no rounding.
---

**ESTABLISHED** (route `jacobson-head-dies-on-bounded-depth-window-constituents-proof`, swarm-0917-w10-w10-nh-last1,
2026-09-18, unreviewed).

**Setting.**
* `J = F_2<S,T | TS=1>`, `E = EL_20(J)`, `L = ker(E -> SL_20(F_2[z^(±1)])) ≅ GL(∞,2)`.
* `Q = Q^(-1)` is a finite Kazhdan set of `E` with constant `κ`, in the convention
  `dist(x, H^E) <= κ^(-1) max_(q∈Q) ||qx - x||`. It exists by
  `ershov-jaikin-kassabov-steinberg-groups-have-property-t`.
* `w` is a word of length `ℓ` over `Q` whose value `z` lies in `L`. The head `x_13(1-ST)` is one choice.

**Window models.** A *window model of defect `ε`* is a countable `E`-set `X`, a finite `F ⊆ X` with `|F| = n`, and
permutations `π(q) ∈ Sym(F)` with

```text
|{x ∈ F : π(q)x ≠ qx}| <= ε n     for every q ∈ Q.                          (WD1)
```

Here `π(q)x ≠ qx` includes the case `qx ∉ F`. Examples: truncations of `E` acting on vectors or subspaces of `J^20`,
on flags, on coset spaces `E/H`, and on `m`-point configurations of any of these.

**Theorem.** Let `ρ` be a unitary representation of `Sym(F)` all of whose irreducible constituents `λ` have depth
`n - λ_1 <= D`, and let `‖·‖_2` be the normalized Hilbert–Schmidt norm. Then

```text
‖ρ(π(w)) - 1‖_2  <=  2 (ℓ D ε)^(1/2) + (4√2/κ) (D ε)^(1/4).                  (WD2)
```

The same bound holds for the restriction of `ρ` to `Alt(F)`, or to any subgroup containing `π(Q)`, since the matrix
`ρ(π(w))` is the same. When `D < (n-1)/2`, no partition of depth `<= D` is self-conjugate. So every irreducible
representation of `Alt(F)` whose Sym-label has depth `<= D` is such a restriction.

**Kills.** The test "the head against `A_m` acting on `m`-point configurations of the Toeplitz truncation", recorded as
the next step of `jacobson-head-concentrates-on-template-constituents`, is dead. So is every model built by truncating
any genuine `E`-set and passing to a Sym or Alt constituent of depth `D = o(1/ε)`: the head is `o(1)`-close to `1`.
The same holds for mixtures and direct sums of such constituents.

**Step where it dies.** Every depth-`D` isotypic block of `ℓ²(F^(D))` (injective `D`-tuples) has constant diagonal.
So the truncation error, which lives on a `Dε`-fraction of tuples, is a `2(Dε)^(1/2)` corner defect for the genuine
action on `ℓ²(X^(D))`. The corner mass inequality `(KFM1)` then puts all but `8(Dε)^(1/2)/κ²` of the block on
finite-dimensional subrepresentations. Those factor through a residually finite linear image of `E`, which kills the
infinite simple normal subgroup `L`.

**Survivors (hole stays OPEN).** A finite-group or permutation certificate of `EL_20(J)` that sees the head must do one
of two things.
* Use generator permutations that are **not** `ε`-close, with `ε -> 0`, to the restriction of a genuine `E`-action on
  any set containing `F`. These are non-window models.
* Put the head mass on constituents of depth `D` with `D ε` bounded below, that is depth at least of the order of the
  inverse window defect.
