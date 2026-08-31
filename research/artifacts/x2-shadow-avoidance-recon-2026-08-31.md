---
X(2) shadow-avoidance reconnaissance and certificate-mechanism survey (2026-08-31)
---

# X(2): the relative-commutant reduction, its solved cell, and why the known obstruction mechanisms cannot refute

Companion to `x2-local-afd-holds-at-rate-controlled-packets`,
`x2-rate-controlled-local-afd-proof`,
`dimension-free-shadow-avoidance-in-hyperfinite-factor`,
`x2-via-dimension-free-shadow-avoidance`.  Derived and hostile-checked
in-session; the positive cell is elementary once Popa's local-AFD
formulation is in hand, which is presumably why the tiny-support
freedom in that criterion exists at all.

## 1. The reduction

Fix a packet `Y` and a finite-dimensional subfactor `M_d ⊂ R`
2-norm-approximating it; residues `z_i = y_i − E_M(y_i)`.  Choosing the
avoidance projection from `R' = M_d' ∩ R` makes the commutator
condition of local AFD FREE (`[d_i, 1⊗s'] = 0`), so the entire problem
becomes: norm-kill finitely many 2-norm-small elements by a nonzero
relative-commutant projection.  For `M = ℂ`, one element: spectral cut,
done, dimension-free.  For general `M_d`: entrywise cuts cost
`δ ≲ ε·d^{-5/2}` (matrix reassembly `d`, corner 2-norm inflation
`√d`, union bound `d²`) — the solved cell.  The open residue is
exactly dimension-freeness, and the failure mode is a small-trace bad
subspace whose `R'`-shadow (support of `(tr_d ⊗ id)` of the bad
projection) is full: maximal entanglement of bad directions with the
approximating subfactor.  The unspent freedom is that `M_d` may be
CHOSEN adapted to `Y` — nothing forces a CAR level; Popa-style
incremental patching chooses its finite-dimensional pieces, and a
proof of the dimension-free claim should be expected to re-choose `M`
and `s'` jointly.

## 2. Why the known non-QD certificate mechanisms cannot produce an X(2) witness

A refutation needs a finitely generated `B ⊂ R` whose restricted trace
is non-quasidiagonal for a PROVABLE reason.  Inventory of every known
mechanism for proving a trace non-quasidiagonal:

1. **Rosenberg (reduced group algebras).**  Needs the canonical trace
   of a nonamenable group; inside `R` every restricted trace is
   amenable and `nonamenable-reduced-group-algebras-avoid-hyperfinite-gns`
   plus `x2-witnesses-are-never-group-shaped` close the class.
2. **Mark-compression (the X(1) technology).**  Scale-free ±1-valued
   certificate: a central group-like mark whose image under any
   asymptotically norm-multiplicative model is forced to `1` while the
   trace says `−1`.  Requires group-like rigidity (compressor
   conjugacy, spectral shearing), and the landed invisibility theorems
   (`literal-group-mark-invisible-to-hyperfinite-representations`,
   `finite-packet-compressor-hyperfinite-invisibility`) show exactly
   this rigidity forces a non-injective von Neumann closure — it
   cannot exist inside `R`.
3. **K-theoretic / index pairings (new analysis, this file).**  A
   Bott-type or `K₀`-state obstruction assigns to the packet an
   integer invariant of the model (a `bott(ũ,ṽ)`, a dimension `k` of a
   model projection) whose NORMALIZED value must approximate a real
   number computed in `B` (`τ_*` of a class).  These never obstruct:
   the model chooses its own size `m`, and every real is approximable
   by `k/m` — simultaneous approximation of finitely many reals at a
   common denominator is likewise free.  Attempted escalations and
   why they fail:
   * exact-value forcing (irrational rotation relations): the model
     only satisfies relations approximately, so no exact irrational
     value is forced;
   * divisibility towers (`u = x_k^{2^k}` forcing `2^K | bott`): the
     integer's a-priori bound grows with `m`, and the model picks `m`
     AFTER seeing the finite packet, so `2^K` never exceeds the bound;
   * two-invariant rationality clashes at a shared `m`: dissolve for
     the same reason (round both).
   Conclusion: any packet-continuous invariant whose admissible model
   values fill `(1/m)ℤ`-nets is useless against quasidiagonality.  An
   obstruction must be SCALE-FREE (finite-valued independent of `m`),
   and mechanism 2 is the only known source of scale-free rigidity —
   which injectivity kills.  So refuting X(2) requires a genuinely new
   certificate class: scale-free, non-group, surviving injective
   closures.  None is known; this is the sharpest current statement of
   the negative route's difficulty, strictly extending
   "witnesses are never group-shaped" to the mechanism level.

## 3. Consistency checks recorded

* Rate-cell sanity at `δ = 0` (packet inside `M_d`): reduces to
  `s = 1`, `B = M_d`, conditions exact.
* Nonemptiness beyond finite dimensions: `y = Σ 8^{-n} u_n`,
  `u_n ∈ M_{2^n}`: level-`n` tail `O(2^{-3n})` beats the required
  `2^{-5n/2}`.
* The rank-`n` projection pair (`‖P−Q‖ = 1`, relative HS `√(2/n)`)
  bounds what black-box arguments can do; the cell does not contradict
  it because the rate hypothesis is exactly what black-box packets
  lack.
* The `j = 1, M = ℂ` case is dimension-free and TRUE — the difficulty
  is localization to a commutant, not smallness conversion per se.
