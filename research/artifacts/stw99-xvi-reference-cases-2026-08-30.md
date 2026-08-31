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

## Addendum: the J-adapted wall is exactly one-sided (model-size extraction lemma)

Let `D` be finite strongly self-absorbing with `[1]` `J`-divisible
(so `D ≅ D ⊗ M_{J^k}` for all `k`), and let
`Φ : D → ∏_ω M_{n_i}` be any unital embedding (from
quasidiagonality + nuclearity).  Two observations:

1. **Forced `J`-divisibility.**  Restricting `Φ` to a unital
   `M_{J^k} ⊆ D` and perturbing componentwise (semiprojectivity of
   matrix algebras) shows `J^k | n_i` for ω-many `i`; the diagonal
   trick (`h(i) := max{k ≤ i : J^k | n_i}`) gives `n_i = J^{h(i)}·m_i`
   with `h(i) → ∞` along the ultrafilter.  So the `J`-part of the
   model sizes can be made to grow without bound — the sizes are
   "asymptotically `J`-divisible" for free.

2. **Extraction.**  Conjugate so that `Φ(1 ⊗ M_{J^{h(i)}})` (from
   `D ≅ D ⊗ M_{J^{h(i)}}`) is the exact left leg
   `M_{J^{h(i)}} ⊗ 1 ⊆ M_{n_i}`.  The image of `D ⊗ 1` asymptotically
   commutes with the left leg, and Haar-averaging over
   `U(M_{J^{h(i)}})` (an exactly-commutant-valued conditional
   expectation moving elements by at most their commutator norm)
   yields unital asymptotically multiplicative maps `D → M_{m_i}` —
   models of `D` of the QUOTIENT sizes.

So the two operations available both preserve the co-`J` part `m_i`
untouched: divisibility inserts `J`-legs, extraction removes them, and
neither can convert `m_i` into a `J`-number.  The residue of Problem
XVI for `E = M_{J^∞}` (and with it the corresponding XIII case) is
therefore EXACTLY: does some quasidiagonal model family of `D` exist
with co-`J`-parts bounded (equivalently `= 1`)?  A negative answer for
a single Künneth-compatible `D` with `K = (Z[J^{-1}], 0)` would
refute XVI; a positive general answer closes the UHF cases.  This is
a clean, previously unnamed approximation problem ("J-smooth
quasidiagonality"), and by the extraction lemma it is INDEPENDENT of
which embedding `Φ` one starts from.

## Addendum 2: the tracial half of the J-adapted wall is free for |J| ≥ 2

Two further structural facts about gate 2' (the UHF cases of XVI):

1. **Ratio-density kills the size gap tracially.**  For `|J| ≥ 2`
   (two distinct primes `p, q ∈ J`), the `J`-smooth integers
   `p^a q^b` are LOG-DENSE, so every matrix model `D → M_n` embeds as
   a corner of `M_s` with `s` `J`-smooth and `s/n ≤ 1 + ε`.  Together
   with trace-controlled Cuntz comparison in UHF ultrapowers
   (componentwise trace-null projections are Cuntz-small) and the
   tensor-tail centrality of `M_{J^∞}`, this yields order-zero maps
   `φ : D → (M_{J^∞})_ω ∩ M_{J^∞}'` with `1 − φ(1)` trace-null: the
   TRACIALLY-`D`-absorbing half of `M_{J^∞} ≅ M_{J^∞} ⊗ D` is free
   whenever `D` is quasidiagonal and `|J| ≥ 2`.  For a single prime
   the `J`-powers are ratio-`p`-sparse and even this half is blocked.

2. **The genuine half is an order-zero repair problem, and no
   unconditional lifting theorem can close it.**  Upgrading the
   trace-null unit defect to an exact unital embedding is precisely
   the tracial-versus-genuine absorption gap (Hirshberg--Orovitz
   territory); the repair of lifted order-zero models to exact ones
   inside a UHF target uses semiprojective finite stages of `D`,
   which an exotic strongly self-absorbing `D` need not have.
   SANITY BOUND on any hoped-for shortcut: `M_2` embeds unitally into
   `R^ω ∩ R'` (von Neumann tail trick), yet `Z ⊗ M_2 ≇ Z`; so
   "nuclear `D` into the von Neumann central sequence algebra implies
   `D` into the C*-central sequence algebra" is FALSE in general, and
   any correct lifting theorem must consume divisibility/
   semiprojectivity data of `D` — exactly gate 2' again.  This
   check is what separates the solved reference cases (where the
   hypothesis ultrapower already matches the target) from the UHF
   residue.
