# STW XVI: the three reference targets are closed without the UCT

*2026-08-30 goal session.  Establishes
`ssa-unit-divisibility-forces-uhf-absorption` and
`stw99-xvi-holds-for-reference-targets`; patches the XVI root.*

## The engine

Two tensor-shift constructions on `D ≅ D^{⊗∞}` (any strongly
self-absorbing algebra):

1. **Tail-centrality**: a unital subalgebra placed in ever-farther
   tensor blocks becomes approximately central — one unital copy
   `B ⊆ D` yields `B → D_ω ∩ D'`.
2. **Central upgrade**: the block shifts applied entrywise define a
   unital `*`-homomorphism `E_ω → E_ω ∩ E'` for ANY strongly
   self-absorbing `E` — so ultrapower embeddability already gives
   central embeddability, hence `E ≅ E ⊗ D` by McDuff.

Plus class arithmetic: `[1] ∈ p·K_0` yields a unital `M_p ⊆ D`
(cancellation from `Z`-stability + sr1 on the finite side; Cuntz's
properly-infinite-class realization on the infinite side), so
unit-divisibility forces UHF absorption.

## The three closures

* `[1] = 0 ⟹ D ≅ O_2` — Cuntz isometry pair exists exactly when
  `[1] = [1] + [1]`; tail-centrality + Kirchberg `O_2`-absorption.
  Note this uses NO embeddability hypothesis and only the unit class,
  not all of `K`.
* embeddable + `K(Q ⊗ O_∞)` ⟹ `D ≅ Q ⊗ O_∞` — the hypothesis
  ultrapower IS the target: central upgrade one way, divisibility +
  Kirchberg `O_∞`-absorption the other.
* QD + `K(Q)` ⟹ `D ≅ Q` — nuclearity turns QD into
  `D → ∏_ω M_{n_i}`, arbitrary sizes embed unitally into `Q`.

## The honest residue (recorded on the root)

`E ∈ {Z, O_∞, M_{J^∞}, M_{J^∞} ⊗ O_∞}`, proper `J`.  The wall in the
UHF cases is `J`-ADAPTED matrix-model sizes: unital `M_n → M_m` needs
`n | m`, and neither compressing (kills multiplicativity) nor
tensoring by dimension-drop tricks changes model sizes into `J`
numbers.  For `Z` and `O_∞` there is no divisibility to spend, and
the `O_2`-shortcut is blocked by `[1] ≠ 0`.  Adversarial guard
retained in the proof: unital `O_2 ⊄ O_∞`, since a unital embedding
transports `[1_{O_2}] = 0` onto the unit class — the same check that
caught an early over-claim ("every Kirchberg SSA absorbs O_2") before
landing.

## Placement

With XIX/XX/LV/LXII/LXXXIX/XCVIII∞/X(1) and the earlier partials,
this makes XVI the ninth problem with a substantial solved region:
three of its seven target cases are theorems.
