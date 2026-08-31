---
rg: 2
id: x2-local-afd-holds-at-rate-controlled-packets
kind: claim
title: Popa's local-AFD criterion holds for packets with rate-controlled hyperfinite approximation
distinct_from:
  popa-projection-formulations-of-x2: that is the equivalence between quasidiagonality of R and the local-AFD criterion for ALL packets; this establishes the criterion's instances on the locus of packets whose 2-norm approximation rate beats an explicit power of the approximating dimension.
  norm-folner-projections-for-hyperfinite-factor: that is the full open workface; this is its first solved cell, and it isolates the dimension-free residue as dimension-free-shadow-avoidance-in-hyperfinite-factor.
artifacts:
  - research/artifacts/x2-shadow-avoidance-recon-2026-08-31.md
---

Let `Y = {y_1,…,y_j} ⊂ R` with `‖y_i‖ ≤ 1` and `ε > 0`.  Suppose there
is a finite-dimensional subfactor `M ≅ M_d ⊂ R` (so `R = M ⊗ R'` with
`R' = M' ∩ R ≅ R`) with

```text
‖y_i − E_M⊗1-span…(y_i)‖₂ ≤ δ,   δ ≤ ε / (2 √(2j) · d^{5/2}),
```

more precisely `dist₂(y_i, M) ≤ δ` for each `i`.  Then there is a
nonzero projection `s ∈ R` and a finite-dimensional \*-subalgebra
`B ⊂ R` with support `s` such that

```text
‖[y_i, s]‖ < 2ε   and   ‖s y_i s − E_B(s y_i s)‖ < 2ε   for all i,
```

i.e. Popa's local-AFD condition (`popa-projection-formulations-of-x2`,
formulation 3) holds at `(Y, 2ε)`.

So the local-AFD criterion — hence quasidiagonality of `R` packetwise —
holds on every packet admitting 2-norm finite-dimensional approximation
at rate `o(d^{-5/2})` in the approximating dimension `d`.  Nontrivial
instances: elements with fast CAR tails, e.g.
`y = Σ_n 8^{-n} u_n` with `u_n ∈ M_{2^n}` unitaries (tail from level
`n` is `O(2^{-3n})`, beating the required `2^{-5n/2}`), which lie in no
finite-dimensional subalgebra.  The support `s` produced has small but
nonzero trace — Popa's criterion deliberately permits this, and the
tiny-support freedom is what the proof spends.

What this does NOT give: `τ_R` quasidiagonal.  Hyperfiniteness supplies
`δ → 0` for every packet but with NO rate against `d`, and generic
`y ∈ R` has no rate (the weak closure is exactly the rate-free regime).
The dimension-free strengthening of the underlying avoidance
statement is FALSE (`shadow-avoidance-fails-at-column-isometries`:
column isometries have 2-norm `d^{-1/2}` and full commutant shadow),
so some dimension dependence in the threshold is necessary: the
critical exponent lies in `[1/2, 5/2]`.  Consequently this cell is
not a stepping stone to all packets — for generic `Y` the
finite-dimensional subfactor must be chosen jointly with the packet,
which is a reformulation of local AFD itself.
