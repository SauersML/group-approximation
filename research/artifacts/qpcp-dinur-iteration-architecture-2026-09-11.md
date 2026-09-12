# Quantum PCP by Dinur iteration: amplification is proved, composition is the hole

**Date:** 2026-09-11. Ordinary mathematics plus source reading. No
computation.

## 0. Summary

Dinur's template alternates two steps: gap amplification, which grows the
alphabet, and alphabet reduction by composition with assignment testers,
which loses only a constant factor independent of the alphabet. The first
quantum step now exists and iterates. Bergamaschi--Metger--Vidick--Zhang
(BMVZ, arXiv:2510.01333v1, 1 Oct 2025) amplify the ground energy of layered
Hamiltonians by a factor of order `sqrt(t/log t)` per round. The cost is
multiplying locality by `2t`, and the procedure keeps the layered structure.

This artifact isolates the second step as one precise open statement: a
locality reduction whose soundness loss does not depend on `t`. It proves
that this statement, with BMVZ, gives the root claim
`quantum-pcp-constant-gap-local-hamiltonian`. It also proves that the most
natural reducer, unfolding each amplified clause into the average of its
factors, returns exactly the input ground energy, so it cancels the
amplification.

## 1. BMVZ, verified from the PDF (v1)

- **Definition 1.6 (layered Hamiltonian).**
  `H=sum_(chi in [g]) w_chi H_chi`, where each layer `H_chi` is the
  expectation over `m_chi` commuting projections, `w_chi>0` and
  `sum w_chi=1`. `omega_min=(min_chi w_chi)^(-1)`.
- **Definition 1.9 (derandomised tensor product amplification).** Fix
  `d`-regular spectral expanders `G_chi` on `m_chi` vertices, and let
  `F_chi` be the paths of length `t`. Then
  `H^(t)=sum_chi w_chi E_(f in F_chi)(I - tensor_(j in [t])(I-Pi^chi_(f(j))))`,
  acting on `t` copies of the `n` qubits, with the `j`-th factor on copy `j`.
  If `H` is `k`-local with `m` clauses, `H^(t)` is `k t`-local with `d^t m`
  clauses.
- **Theorem 1.2 (gap amplification).** `H^(2t)` is `2t k`-local with `d^(2t) m`
  terms. Completeness: `lambda_min(H^(2t))<=2t lambda_min(H)` (Proposition 4.1).
  Soundness: `lambda_min(H^(2t))>=min[Theta(log t/t),Theta(sqrt(t/log t) lambda_min(H))]`.
- **Proof of Corollary 6.13, p. 35.** With `r=(t log t)^(1/2)` and `alpha=r/t`,
  the high-energy case gives at least `(1/3)log t/t` (6.62). The low-energy
  case gives at least `lambda_min(H) t^(1/2)(log t)^(-1/2) eta` with
  `eta=1/(20 max{1+C_mu, omega_min})`, "constant not depending on `t`" (6.66).
  `C_mu` is the constant of Lemma 6.7, tied to the expander family.
- **Section 7.** "Upon each iteration, the weight parameter `omega_min` is
  fixed." Iterating gives (7.5):
  `lambda_min(M_l)>=min[(1/3)log t/t, lambda_min(M_0)(eta^2 t/log t)^(l/2)]`.
  Theorem 7.3 then gives locality `k p(n)^(O(1))` and constant gap `c(omega)`.
  Theorem 7.4 is a "streaming" quantum PCP whose terms are `O(n)`-fold tensor
  products of `O(1)`-local projections.
- **Section 8, Claim 8.1** (from Anshu--Breuckmann--Nguyen) gives a 5-local
  Hamiltonian with `a=2^(-poly(n))` and `b=a+1/poly(n)`. Each qubit lies in at
  most 7 terms, and every term is an unweighted projection. **Corollary 8.4:**
  its clauses split into `O(1)` commuting layers of sizes differing by at most
  one, found through an equitable colouring of the clause graph, which has
  degree at most `35`. Theorem 7.4's proof records `omega_min>=1/2*1/35`, i.e.
  `min_chi w_chi>=1/70`.
- **Section 1.1, verbatim.** "All attempted quantisations of Dinur's gap
  amplification, including ours and [AALV09], are locality-increasing, which
  is a significant obstacle to applying the kinds of PCP composition theorems
  that make alphabet reduction possible." Also: "A proof of the quantum games
  PCP conjecture was claimed by [NV18], but it has since been established that
  the proof had errors, and as of now the conjecture remains open."

## 2. The class and the open statement

`L(k,g,omega)` denotes normalized layered Hamiltonians (Definition 1.6) of
`k`-local qubit projections with rational poly-bit entries, at most `g`
layers, and `omega_min<=omega`.

**(RED) Locality reduction with amplifier-independent loss.** There are
constants `k_0>=5`, `g_0>=36`, `omega_0>=70` and `c>0` such that, for every
integer `t>=2`, there are constants `S_t`, `A_t` and a deterministic
polynomial-time map with the following property. Every amplified Hamiltonian
`H^(2t)`, with `H` in `L(k_0,g_0,omega_0)` on `N` qubits and `M` clauses, maps
to `H'` in `L(k_0,g_0,omega_0)` on at most `S_t N` qubits with at most
`S_t d^(2t) M` clauses, satisfying

```text
lambda_min(H') >= c * lambda_min(H^(2t)),                        (RED1)
lambda_min(H') <= A_t * lambda_min(H^(2t)) + 2^(-N).             (RED2)
```

The constant `c` must not depend on `t`. That is the whole difficulty: the
classical analogue is composition with an assignment tester that encodes each
clause's local assignment by a code of constant relative distance, and that
tester's loss does not depend on the alphabet.

## 3. RED plus BMVZ gives quantum PCP

Put `eta_0=1/(20 max{1+C_mu, omega_0})`. Fix `t>=3` large enough for the side
conditions of (6.62)-(6.66) and (7.6), and with `c eta_0 sqrt(t/log t)>=2`.
Start from the Corollary 8.4 family `H_0` in `L(5,36,70)`, contained in
`L(k_0,g_0,omega_0)`, with YES energy at most `2^(-p(n))` and NO energy at
least `1/q(n)`. Iterate `H_(i+1)=RED_t(H_i^(2t))`. Section 7 keeps `omega_min`
and the layer count, and RED keeps the class.

- **NO side.** By (6.62), (6.66) and (RED1),
  `lambda_min(H_(i+1))>=c min[(1/3)log t/t, eta_0 sqrt(t/log t) lambda_min(H_i)]>=min[gamma_t, 2 lambda_min(H_i)]`,
  with `gamma_t=c log t/(3t)`. After `l=ceil(log_2(gamma_t q(n)))=O(log n)`
  rounds, `lambda_min>=gamma_t`, and later rounds keep it there.
- **YES side.** By Proposition 4.1 and (RED2),
  `lambda_min(H_(i+1))<=2t A_t lambda_min(H_i)+2^(-N_i)`. After `l` rounds the
  YES energy is at most `(2t A_t)^l (2^(-p(n))+l 2^(-n))`, which is negligible.
  Here `(2tA_t)^l=poly(n)` because `t` is fixed.
- **Size and time.** Qubits multiply by at most `2t S_t` and clauses by at most
  `d^(2t) S_t` per round, so `O(log n)` rounds give polynomial size and time.
- **Form.** Every `H_i` is a weighted average of `k_0`-local projections with
  rational weights `w_chi`. Repeating clauses in proportion to the weights puts
  it in the uniform form (QPCP1) with polynomial blowup, and projections satisfy
  `0<=h<=I`.

Thus deciding `lambda_min<=negl(n)` versus `lambda_min>=gamma_t` for constant-locality
qubit Hamiltonians is QMA-hard, which is the root claim.

## 4. The natural reducer cancels the amplification

For `H` in `L(k,g,omega)`, define the factor unfolding of `H^(t)`:

```text
U_t(H) = sum_chi w_chi E_(f in F_chi) (1/t) sum_(j in [t]) (Pi^chi_(f(j)))_(copy j).
```

**(UF1)** `U_t(H)<=H^(t)`. For each `f`, the factors act on distinct copies and
commute. `I - tensor_j (I-P_j)` is the projector onto "some factor reads one",
so it dominates each `P_j` and hence their average.

**(UF2)** `U_t(H)=(1/t) sum_(j in [t]) H_(copy j)`. The paths of a `d`-regular
graph, taken uniformly, have a uniform start vertex and uniform neighbour steps.
So every coordinate `f(j)` is uniform on `[m_chi]`, and
`E_f (Pi^chi_(f(j)))_(copy j)=(H_chi)_(copy j)`.

**(UF3)** `lambda_min(U_t(H))=lambda_min(H)`. The copies commute, and a sum of
the same operator over tensor factors has minimum `t lambda_min(H)`.

So `U_t` is `k`-local and keeps completeness, but it returns exactly the input
ground energy. Any locality reduction of the form "replace each amplified clause
by the average of its factors" therefore has
`c<=lambda_min(H)/lambda_min(H^(2t))` on every input. For small
`lambda_min(H)`, (6.66) makes this at most `sqrt(log t/t)/eta_0`, which tends to
zero, so `c` cannot be independent of `t`. Amplify-then-unfold makes no progress
per round.

## 5. Where known tools sit relative to RED (attempts, not theorems)

- **Qudit or qubit re-encoding.** BMVZ already works on qubits; the issue is
  locality, not local dimension. Not applicable.
- **Perturbative gadgets** (Kempe--Kitaev--Regev; Oliveira--Terhal). These
  reduce locality, but the recovered gap depends on the gadget order and energy
  scales. For clauses of locality `2t k_0`, the known constructions give a loss
  depending on `t`. No gadget with `t`-independent loss is known. This note does
  not prove a lower bound for gadgets.
- **Circuit-to-Hamiltonian per clause.** Measuring a clause coherently (BMVZ
  Lemma 7.6: a depth `O(log m)` circuit computing an AND over ancillas) and
  encoding that circuit with a clock construction inherits the inverse-polynomial
  promise-gap loss of clock constructions in the circuit size. The loss grows
  with `t`.
- **Classical composition.** Assignment testers (Dinur--Reingold) encode the
  whole local assignment in a code of constant relative distance, so one wrong
  variable costs a constant fraction of the encoding. The quantum difficulty is
  that data cannot be copied for consistency tests, and a quantum code of
  constant relative distance hides logical information from every local term.
  Bafna--Vyas (ECCC TR26-150) name this local indistinguishability as a central
  obstacle.
- **Positive shift and exact combinatorial soundness.** Irrelevant to RED: they
  do not change locality. See `positive-shift-trivializes-exact-combinatorial-soundness`.

## 6. Not claimed

RED is not claimed true or false. BMVZ is recorded only as stated in v1. The
parameter bookkeeping in Section 3 uses only the quoted equations and the
fixed-`omega_min` remark of Section 7.
