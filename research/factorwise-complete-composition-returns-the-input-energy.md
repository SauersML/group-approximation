---
rg: 2
id: factorwise-complete-composition-returns-the-input-energy
kind: claim
title: Clausewise composition with private proofs and factorwise completeness returns at most the input energy on tensor-OR amplified instances, so it cannot meet either quantum PCP reducer claim
artifacts:
  - research/factorwise-complete-composition-returns-the-input-energy-proof.md
  - experiments/qpcp-copy-respecting-composition-2026-09-17/check_composition_bound.py
  - experiments/qpcp-copy-respecting-composition-2026-09-17/check_composition_bound_output.txt
distinct_from:
  local-or-simulation-has-linear-normalized-loss: that bounds statewise simulation of one tensor-OR clause with a fixed data-independent ancilla and a bounded-depth encoding; this bounds only the ground energy of a whole reduced instance, with data-dependent proofs of unbounded size and circuit complexity, and with arbitrary encodings of single data qubits.
  unfolding-tensor-clauses-returns-the-original-gap: that analyses one reducer, the factor average; this proves that every reducer in a class containing it, private-proof gadgets that are complete on factorwise-satisfying data, loses the whole amplification gain, and the factor average is the equality case.
  locality-reduction-with-amplifier-independent-loss: that is the open reducer claim of the Dinur-iteration route; this excludes one broad construction class for it and names the step a reducer outside the class must change.
  global-walk-reducer-has-net-energy-gain: that is the open reducer claim of the global-walk route; this excludes the same class for it at every fixed t, not only for loss families o(t).
---

**ESTABLISHED (ordinary proof, unreviewed).** Full proof:
`research/factorwise-complete-composition-returns-the-input-energy-proof.md`.

## Setting

An amplified instance has `T` copies of `n` qubits and a list `F` of clauses.
Clause `f` puts one input term `h_(f(j))` on copy `j`, for each `j` in `[T]`.
Both BMVZ amplification (`bmvz-iterable-tensor-gap-amplification`, `T=2t`) and the
global walk (`global-walk-linearly-amplifies-hamiltonian-energy`, `T=t`) have this form.

A **factorwise-complete clausewise composition** (FCC) with locality `k_0` and
completeness error `eta` outputs a Hamiltonian of the following form.

- **Registers.** Qubit `q` of copy `j` becomes a block `B_(j,q)` through an isometry
  `E_(j,q)`. The block may hold its own ancillas. Each clause `f` owns a private
  proof register `A_f`.
- **Terms.** `H'=sum_f mu_f G_f` with `G_f=sum_i p_(f,i) g_(f,i)`,
  `0<=g_(f,i)<=I`, and `mu`, `p` probability vectors. Every `g_(f,i)` acts on
  blocks and on `A_f` only, and meets at most `k_0` blocks.
- **Factorwise completeness.** Let `y` be classical data on all copies such that
  `h_(f(j))` annihilates copy `j` of `y` for every `j`. Then some state `pi` on
  `A_f` has `<Ey (x) pi, G_f (Ey (x) pi)> <= eta`.

Proof sizes, proof circuits, commutation of terms and interaction degree are
unrestricted. The proofs may depend on the data.

## Theorem

Let every `h_e` be a diagonal projector of parity type: on a violating basis
state, flipping any single qubit of `supp(h_e)` repairs `h_e`. Suppose
`|supp h_e|>=r` for all `e`, and some distribution on basis states `x`
violates every term with probability at most `rho`. Then

```text
lambda_min(H') <= eta + rho k_0 / r.                                  (FCC1)
```

If the blocks encode whole copies (one isometry per copy, the term meeting at
most `k_0` copies) and every `h_e` is a diagonal projector other than `I`, then
`lambda_min(H')<=eta+rho k_0`. **(FCC2)**

**Instances.** For odd `n`, even `r` and `gcd(n,r)=1`, let `W(n,r)` be the
`n` cyclic window constraints `x_i+...+x_(i+r-1)=1 mod 2`. Then
`lambda_min(W(n,r))=1/n`, and the uniform distribution on optimal assignments
gives `rho=1/n`. `W(n,r)` is one layer of commuting qubit projections with
`omega_min=1`, so it lies in `L(k_0,g_0,omega_0)` whenever `r<=k_0`.

## Consequences

1. **Dinur-iteration reducer.** Take any FCC family meeting (RED1) of
   `locality-reduction-with-amplifier-independent-loss`, with completeness
   errors `eta_t(n)` on the instances `W(n,2)`. Then
   `c <= (n eta_t(n) + k_0/2) sqrt(log t/t)/eta_B`
   for all large `n`, where `eta_B=1/(20 max{1+C_mu,1})`
   is the BMVZ constant. If `liminf_n n eta_t(n)<=K` with `K` independent of `t`,
   then `c<=(K+k_0/2) sqrt(log t/t)/eta_B` for every `t`, so `c=0`. The loss
   of FCC reducers grows like `sqrt(t/log t)`.
2. **Global-walk reducer, at every fixed t.** Take an FCC map meeting
   `global-walk-reducer-has-net-energy-gain` with `n eta(n)->0` on
   `W(n,r)`, where `r` is the largest even integer `<=k_0`. Then
   `L >= (3t+2) r/(8 k_0)`. Since `r>=k_0-1>=k_0/2`, this is at least `(3t+2)/16`,
   which contradicts `L<(3t+2)/16`. Here `n` runs over primes larger than `k_0`.
3. **Equality.** The factor average of `unfolding-tensor-clauses-returns-the-original-gap`
   is FCC with `eta=0`, and it attains (FCC1) with `k_0=r`.

## Where a reducer must leave the class

The proof replaces the data of each violated factor inside one clause's view
and hands the clause an honest proof for that fake data. The other clauses
never see the change, because the proof is private and completeness holds for
every factorwise-satisfying tuple of copies. A reducer with a `t`-independent
loss must break one of these:

- (a) completeness only on **cross-copy correlated** data, so that terms test
  consistency between copies (swap tests, or comparisons against one shared
  encoding of the input);
- (b) proof registers **shared by several clauses** that depend on more than one
  copy, so the fake proof is visible elsewhere;
- (c) data encodings spread over **many copies**, or a map that is not clausewise
  at all.

The classical calibration agrees. On the classical tensor-OR CSP over copies,
Dinur's assignment testers used clausewise are FCC, and their loss grows linearly
in `T`: a one-bit repair has relative distance `1/(Tr)` in the clause view. Dinur's
powering avoids this through (a), because its constraints read opinions of one
shared assignment. The theorem concerns a construction class. It does not show
that no reducer exists: classically, the PCP theorem gives instance-level maps
with constant loss.

`experiments/qpcp-copy-respecting-composition-2026-09-17/check_composition_bound.py`
computes `lambda_min(H')` exactly for random classical FCC testers on
`W(5,2)`, `W(5,4)`, `W(7,2)` and `W(7,4)` with `T=2,3`. It checks (FCC1) and
the explicit fake-proof average of the proof in all 18 cases.
