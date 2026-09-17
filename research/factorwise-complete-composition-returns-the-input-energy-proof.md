---
rg: 2
id: factorwise-complete-composition-returns-the-input-energy-proof
kind: route
title: Fake-data trial states bound the ground energy of factorwise-complete clausewise compositions
target: factorwise-complete-composition-returns-the-input-energy
requires:
  - bmvz-iterable-tensor-gap-amplification
  - global-walk-linearly-amplifies-hamiltonian-energy
---

# Factorwise-complete clausewise composition returns the input energy

Date: 2026-09-17. Lane sw-077 (reframer, quantum PCP). Status: ordinary proof,
not Lean-verified, unreviewed. This is an obstruction for a construction class.
It does not disprove quantum PCP or either open reducer claim.

## 1. Definitions

**Amplified instance.** Fix `n` qubits and diagonal projectors `h_1,...,h_m` on
them. Fix `T>=1` and a finite list `F` of maps `f:[T]->[m]`. Copy `j` is a
register of `n` qubits, and qubit `q` of copy `j` is written `(j,q)`. Clause `f`
is the operator `I - tensor_j (I - h_(f(j)))_(copy j)`. For the construction class
only the clause list matters, not the clause weights of the amplifier.

- BMVZ Definition 1.9, as recorded in `bmvz-iterable-tensor-gap-amplification`:
  `T=2t`, with `f` ranging over walks, and the `j`-th factor on copy `j`
  (artifact `qpcp-dinur-iteration-architecture-2026-09-11.md`, line 34).
- The global walk `G_t(H)` of `global-walk-linearly-amplifies-hamiltonian-energy`:
  `T=t`, with factor `j` on copy `j` (artifact
  `qpcp-global-walk-amplification-2026-09-11.md`, (A_t) and line 77).

**FCC reducer output.** An output of *factorwise-complete clausewise
composition* with locality `k_0` and completeness error `eta` consists of the
following data.

1. *Blocks.* For each `(j,q)`, a finite register `B_(j,q)` and an isometry
   `E_(j,q): C^2 -> B_(j,q)`. For a basis string `y=(y_(j,q))` put
   `Ey = tensor_(j,q) E_(j,q)|y_(j,q)>`.
2. *Private proofs.* For each `f` in `F`, a finite register `A_f`. The whole space
   is `K = tensor_(j,q) B_(j,q) tensor tensor_f A_f`.
3. *Terms.* `H' = sum_f mu_f G_f` and `G_f = sum_i p_(f,i) g_(f,i)`, where `mu` and
   each `p_(f,.)` are probability vectors and `0 <= g_(f,i) <= I`. Each
   `g_(f,i)` acts as the identity outside `tensor B tensor A_f` and meets at most
   `k_0` blocks. (A `k_0`-local qubit term meets at most `k_0` blocks.)
4. *Factorwise completeness.* For every `f` and every basis string `y` with
   `h_(f(j)) |y_(j,.)> = 0` for all `j`, there is a density operator
   `pi_f(y)` on `A_f` with `Tr[G_f (Ey Ey* tensor pi_f(y))] <= eta`.

Terms of `H'` that meet no proof register may be assigned to any `G_f`. They
then take part in that clause's completeness condition. Nothing else is
assumed: proof sizes, circuits producing honest proofs, commutation among
terms, degree and geometry are all free.

**Whole-copy variant (FCC').** Item 1 is replaced by one register `R_j` and one
isometry `V_j:(C^2)^(tensor n) -> R_j` per copy, and item 3 by "meets at most
`k_0` of the `R_j`".

## 2. The bound

**Theorem.** Assume every `h_e` is of parity type: `|supp h_e| >= r`, and for
each basis state `z` with `h_e z = z` and each qubit `q` in `supp h_e`, the
string `z` with `q` flipped is annihilated by `h_e`. Let `D` be a probability
distribution on basis strings `x` of `n` bits with `Pr_D[h_e x = x] <= rho` for
every `e`. Then every FCC output satisfies

```text
lambda_min(H') <= eta + rho k_0 / r.                                  (FCC1)
```

For FCC' outputs, with every `h_e` a diagonal projector other than `I`,
`lambda_min(H') <= eta + rho k_0`. **(FCC2)**

*Proof of (FCC1).* Fix a basis string `x` and a choice function `s` that assigns
to every pair `(f,j)` a qubit `s(f,j)` in `supp h_(f(j))`. Put
`V_f(x) = {j : h_(f(j)) x = x}`, the violated factors of clause `f` when every
copy carries `x`.

*Fake data.* For each `f` let `y^f` be the string that equals `x` on every copy,
except that qubit `(j, s(f,j))` is flipped for each `j` in `V_f(x)`. Factor `j` of
`f` sits on copy `j` alone, and copy `j` of `y^f` differs from `x` at most at
`s(f,j)`. For `j` outside `V_f(x)`, copy `j` equals `x`, which `h_(f(j))`
annihilates. For `j` in `V_f(x)`, the parity-type assumption says the flip
repairs `h_(f(j))`. So `y^f` is factorwise satisfying for `f`, and
`pi_f := pi_f(y^f)` exists.

*Trial state.* `rho_x = E(x,...,x) E(x,...,x)* tensor tensor_f pi_f`, a product
over the proof registers. (Write `Ex` for the data part.)

*Term by term.* Let `g = g_(f,i)`, and let `S` be the set of blocks it meets.
The flipped set of `f` is `Q_f = {(j,s(f,j)) : j in V_f(x)}`.

- If `S` avoids `Q_f`, then `g` acts on `tensor_(S) B tensor A_f`. The reduced
  state of `rho_x` there is `tensor_(b in S) E_b|x_b><x_b|E_b* tensor pi_f`. It
  equals the reduced state of `Ey^f Ey^f* tensor pi_f`, because the data is a
  product over blocks and `y^f=x` on `S`. Hence
  `Tr[g rho_x] = Tr[g (Ey^f Ey^f* tensor pi_f)]`.
- Otherwise `Tr[g rho_x] <= 1`.

Since `g_(f,i) >= 0`, the sum over the terms of the first kind is at most
`Tr[G_f (Ey^f Ey^f* tensor pi_f)] <= eta`. Therefore

```text
Tr[G_f rho_x] <= eta + sum_i p_(f,i) 1[S_(f,i) meets Q_f]
             <= eta + sum_(j in V_f(x)) sum_i p_(f,i) 1[(j,s(f,j)) in S_(f,i)].
```

*Averaging.* Draw `x` from `D`. Independently, draw each `s(f,j)` uniformly from
`supp h_(f(j))`, a set of at least `r` qubits. `Pr[j in V_f(x)] <= rho`, and given
`j`, a fixed block `(j,q)` is chosen with probability at most `1/r`. Hence

```text
E Tr[G_f rho_x] <= eta + (rho/r) sum_i p_(f,i) |S_(f,i)| <= eta + rho k_0/r.
```

Average over `f` with weights `mu_f`. Some realization of `(x,s)` has
`Tr[H' rho_x] <= eta + rho k_0 / r`, and `lambda_min(H') <= Tr[H' rho_x]`. ∎

*Proof of (FCC2).* Take `y^f` equal to `x` on copies outside `V_f(x)`, and on
each copy `j` in `V_f(x)` any string that `h_(f(j))` annihilates (it exists since
`h_(f(j)) != I` is diagonal). The data part is a product over copies, so a term
that meets no copy in `V_f(x)` sees the honest reduced state. A term meets at
most `k_0` copies, so

```text
E_x Tr[G_f rho_x] <= eta + rho sum_i p_(f,i) |{copies met by g_(f,i)}| <= eta + rho k_0. ∎
```

*Remarks.* The proof needs no stationarity, walk structure, weights or
normalization of the amplifier. It uses only that each clause puts exactly one
factor on each copy. It never uses that `x` is a ground state; the distribution
`D` only has to spread its violations evenly.

## 3. The window instances `W(n,r)`

Let `n` be odd, `r` even, and `gcd(n,r)=1`. For `i` in `Z_n` let
`h_i = (I + Z_i Z_(i+1) ... Z_(i+r-1))/2`, the projector onto even parity of the
window `{i,...,i+r-1}`. So `h_i` is violated unless `x_i+...+x_(i+r-1)=1 mod 2`.
Put `W(n,r) = (1/n) sum_i h_i`.

1. *Parity type, `|supp|=r`.* Flipping any window bit changes the window parity.
2. *Unsatisfiable.* Add all `n` equations. Every variable occurs `r` times, an
   even number, so the left side is `0` and the right side is `n = 1 mod 2`.
3. *One violation suffices.* In `F_2[z]/(z^n-1)` the window map is multiplication
   by `p(z) = 1+z+...+z^(r-1) = (z^r-1)/(z-1)`. Its image is the ideal generated by
   `g = gcd(p, z^n-1)`. We have `gcd(z^r-1, z^n-1) = z^(gcd(r,n)) - 1 = z-1`,
   and `z-1` divides `p` because `p(1) = r = 0`. So `g = z-1`, and the image is the
   set of even-weight vectors. The right-hand side `1 + e_0` has weight `n-1`,
   which is even, so some `x` violates exactly one constraint.
   Hence `lambda_min(W(n,r)) = 1/n`, since the Hamiltonian is diagonal.
4. *Even violations.* The cyclic shift preserves the constraint set and maps
   optimal assignments to optimal assignments. Under the uniform distribution
   on optimal assignments, every `h_i` is violated with the same probability.
   These probabilities sum to the expected number of violations, which is `1`.
   So `rho = 1/n`.
5. *Class membership.* The `h_i` are commuting rational qubit projections of
   locality `r`, forming one layer with `omega_min = 1`. So `W(n,r)` lies in
   `L(k_0,g_0,omega_0)` of `locality-reduction-with-amplifier-independent-loss`
   when `r <= k_0`, and in the input class of `global-walk-reducer-has-net-energy-gain`.

With (FCC1): **every FCC output on an amplified `W(n,r)` has
`lambda_min(H') <= eta + k_0/(r n)`, for every `T` and every clause list.**

The script checks items 2-4 by brute force for `(n,r)` in
`{(5,2),(5,4),(7,2),(7,4)}`.

## 4. Consequence for the Dinur-iteration reducer

`bmvz-iterable-tensor-gap-amplification` gives
`lambda_min(H^(2t)) >= min[(1/3) log t/t, eta_B sqrt(t/log t) lambda_min(H)]`,
with `eta_B = 1/(20 max{1+C_mu, omega_min})`. For `H = W(n,2)`, `omega_min = 1`
and `lambda_min(H) = 1/n`. Once `n >= n_0(t)`, the second term is the minimum.

Suppose a reducer satisfies (RED1) with constant `c`, and its output on
`W(n,2)^(2t)` is FCC with error `eta_t(n)`. Then

```text
c eta_B sqrt(t/log t)/n <= c lambda_min(H^(2t)) <= lambda_min(H') <= eta_t(n) + k_0/(2n),
c <= (n eta_t(n) + k_0/2) sqrt(log t/t) / eta_B.
```

If `liminf_n n eta_t(n) <= K` for every `t`, with `K` independent of `t`, then
`c <= (K + k_0/2) sqrt(log t / t)/eta_B` for every `t >= 3`. Hence `c = 0`, which
contradicts `c > 0`. The completeness hypothesis is mild: (RED2) asks for an additive
error `2^(-N)`, and clausewise constructions that meet it clause by clause
have `n eta -> 0`.

## 5. Consequence for the global-walk reducer

`global-walk-linearly-amplifies-hamiltonian-energy` gives, for spectral bound
`lambda <= 1/2`, `epsilon = lambda_min(H)` and even `t`,

```text
lambda_min(G_t(H)) >= 1 - (1-epsilon)[1-(1-lambda^2) epsilon]^((t-2)/2)
                    >= 1 - (1-epsilon)(1 - 3 epsilon/4)^s,       s=(t-2)/2.
```

We use `(1-a)^s <= 1 - s a + s^2 a^2/2` for `0 <= a <= 1`, by alternating Taylor
bounds for `e^(-as)` and `1-a <= e^(-a)`. With `a = 3 epsilon/4`:

```text
lambda_min(G_t(H)) >= epsilon + s a - s^2 a^2/2 - epsilon s a
                    = epsilon (3t+2)/8 - O(t^2 epsilon^2).
```

Take `H = W(n,r)` with `r` the largest even integer `<= k_0`, and `n` prime and
larger than `k_0`, so `epsilon = 1/n`. Suppose the reducer's output is FCC
with `n eta(n) -> 0`. The claim requires `lambda_min(H') >= lambda_min(G_t(H))/L`,
so

```text
L >= lambda_min(G_t(H)) / lambda_min(H')
  >= [(3t+2)/8 - O(t^2/n)] / [n eta(n) + k_0/r]  ->  (3t+2) r/(8 k_0)    (n -> infinity).
```

`L` does not depend on `n`, so `L >= (3t+2) r/(8 k_0)`. For `k_0 >= 2`,
`r >= k_0 - 1 >= k_0/2`, so `L >= (3t+2)/16`, against the requirement
`L < (3t+2)/16`. This holds at every fixed `t` and every `k_0`. It is stronger
than excluding loss families `L_t = o(t)`.

Whole-copy encodings (FCC') give only `L >= (3t+2)/(8k_0)`. That excludes
`L_t = o(t)` families but not a single `t`.

## 6. Scope, equality and calibration

**Equality.** The factor average `U_T(H) = (1/T) sum_j H_(copy j)` of
`unfolding-tensor-clauses-returns-the-original-gap` is FCC: blocks are the qubits,
there are no proofs, `G_f = (1/T) sum_j (h_(f(j)))_(copy j)`, and `eta = 0`. On
`W(n,r)` with `k_0 = r`, (FCC1) gives `1/n`, which is `lambda_min(U_T)`. The
bound is tight.

**Constructions inside the class** (data in the clear or per-qubit encoded, a
private register per amplified clause, complete on all factorwise-satisfying
data):

- the factor average and sub-OR averages over `<= k_0/r` factors;
- clock or history-state encodings of a coherent measurement of one clause,
  with a private clock and private ancillas (BMVZ Lemma 7.6 style AND trees),
  whenever the encoding's completeness error is `o(1/n)`;
- classical assignment testers or PCPPs for one clause, run per clause with
  private proofs, and their quantum lifts;
- per-clause mediator gadgets, whenever they are put in positive normalized form
  with completeness error `o(1/n)`.

This makes the "not proved" attempts on perturbative gadgets and clock encoding in
`locality-reduction-with-amplifier-independent-loss` provably dead, as far as
they are clausewise with private registers and factorwise complete.

**Outside the class, and hence the gate.** The proof uses exactly three
features: (i) the proof register a clause uses is private, (ii) completeness
holds for data in which different copies carry different strings, and (iii)
repairing one factor touches few blocks of one copy. A reducer with a
`t`-independent loss must drop one of them:

- (a) terms that are complete only on cross-copy correlated data, such as swap
  or comparison tests between copies, or checks against a register holding one
  shared encoding of the input;
- (b) proof registers shared across clauses and depending on several copies;
- (c) encodings in which one factor's repair changes a constant fraction of a
  term's view, as in large-alphabet opinion encodings.

**Classical calibration.** Everything above also applies to classical
tensor-OR CSPs over copies. There, clausewise composition with assignment
testers is FCC, and its loss grows linearly in `T`. This matches robust
soundness: repairing one bit is relative distance `1/(Tr)` in the clause view.
Dinur's powering avoids the bound through (a) and (c). A powered constraint
reads opinions about one shared assignment, and one wrong opinion is a
constant fraction of a constraint's two symbols. The theorem does not say that
no reducer exists. Classically, the PCP theorem supplies instance-level maps
with constant loss, and (RED1)-type linear soundness holds for Dinur's
composition. So the class restriction is necessary, and the method does not
prove a known-false statement.

## 7. Script

`experiments/qpcp-copy-respecting-composition-2026-09-17/check_composition_bound.py`
(output in `check_composition_bound_output.txt`, about 2 minutes, single thread).
The script checks the following.

- `lambda_min(W(n,r)) = 1/n`, and the violation probabilities are uniform.
- For random classical FCC testers, it computes `lambda_min(H')` exactly. Each
  tester has random honest-proof functions (factor parities, ANDs, XORs),
  factor-flag checks and random `k_0`-bit forbidden-pattern terms, so `eta = 0`
  by construction. Parameters: `T` in `{2,3}`, 8-15 clauses and 3 seeds.
- It evaluates the fake-proof average of Section 2 explicitly and checks
  `lambda_min(H') <= fake average <= k_0/(rn)`.

All 18 cases pass. The check is a sanity test of the combinatorics. It uses only
diagonal gadgets; the proof above covers arbitrary quantum gadgets.
