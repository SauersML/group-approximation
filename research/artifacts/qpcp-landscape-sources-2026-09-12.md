# Quantum PCP landscape, 2026-09-12: product states, expanders, codes, games (source record)

Lane `ex-quantum-pcp`. Source reading only, no computation. arXiv e-print TeX
sources and abstract pages were fetched on MSI on 2026-09-12. Where a theorem
number is given, it was read from the arXiv PDF of the stated version. Where only
a TeX label is given, the number was not read and must not be quoted as a number.

## 1. Brandao--Harrow, arXiv:1310.0017v2, "Product-state approximations to quantum ground states"

Numbers read from the v2 PDF, pp. 6--9.

- **Theorem 3 (Basic product-state approximation).** Let `G=(V,E)` be a
  `D`-regular graph with `n=|V|` and `rho` an `n`-qudit state. Then there is a
  globally separable `sigma` with
  `E_((i,j) in E) ||rho^(Q_iQ_j)-sigma^(Q_iQ_j)||_1 <= 12 (d^2 ln(d)/D)^(1/3)`.
- **Corollary 4.** For `H=E_((i,j) in E) H_ij=(2/(nD)) sum_((i,j) in E) H_ij`
  with `||H_ij||<=1`, there is a product state `phi` with
  `tr(H phi) <= e_0(H)+12 (d^2 ln(d)/D)^(1/3)`.
- **Corollary 5.** For the promise problem `e_0(H)<=alpha` versus
  `e_0(H)>=beta`, if `beta-alpha>=12(d^2 ln(d)/D)^(1/3)+delta` there are
  witnesses of length `O(nd log(n/delta))` for the first case; the verifier
  runs in time `nDd^4 polylog(1/delta)`.
- **Theorem 6 (Clustered product-state approximation for regular graphs).**
  `G` is `D`-regular, `{V_1,...,V_(n/m)}` a partition into blocks of size `m`,
  `Phibar_G=E_i Phi_G(V_i)` the average block expansion, where
  `Phi_G(S)=Pr_((u,v) in E)[v not in S | u in S]` (Section 2 of the source), and
  `Ibar=E_i I(V_i:V_(-i))_rho`. Then there is `sigma` separable across the blocks
  with error at most `9((d^2 Phibar_G/D)(Ibar/m))^(1/6)+1/m+m/n`.
- **Corollary 7.** For the same `H`, there is a block-product state with
  `tr(H phi) <= e_0(H)+9((d^2 Phibar_G/D)(E_i S(V_i)_psi0/m))^(1/6)+1/m+m/n`,
  described by a classical string of length `O(n 2^m log(1/delta))`; the text
  after it says the problem is then in NP when `m=O(log n)`.
- **Theorem 8 (weighted graphs).** Error
  `14(d^4 ln(d) tr[A^2] ||pi||_2^2)^(1/8)+||pi||_2^2`, where `A` is the reversible
  walk of the weight matrix and `pi` its stationary distribution.
- **Proposition 10.** For any constants `c,alpha,beta>0` it is NP-hard to decide
  whether a 2-CSP with alphabet `Sigma` on a constraint graph of degree `D` has
  `unsat=0` or `unsat>=c|Sigma|^alpha/D^beta`.
- **Corollary 11.** Suppose that for every `t>=1` there is a map `P_t` from
  2-local Hamiltonians on `d`-dimensional particles to 2-local Hamiltonians on
  `n_t` particles of dimension `d_t`, with (i) deterministic polynomial time,
  (ii) `P_t(H)=E_((i,j)~G') H'_ij`, `G'` a probability distribution,
  `||H'_ij||<=1`, (iii) `deg(P_t(H))>=deg(H)^t`, (iv) `n_t<=n^(O(t))`,
  (v) `d_t=d^t`, (vi) `e_0(P_t(H))>=e_0(H)` if `e_0(H)>0`,
  (vii) `e_0(P_t(H))<=e_0(H)` if `e_0(H)<=0`. "Then the quantum PCP conjecture is
  false." The proof (Section 6) pads to degree `D=8d^3`, takes
  `t>=log_2(96d^3/eps)`, and concludes "our original energy estimation problem is
  in NP, which implies the quantum PCP theorems is false (assuming that
  NP != QMA.)". It states "For simplicity, we neglect the additional arithmetic
  errors from discretization."
- **Section 2.1.4, verbatim.** "a consequence of the result is that a
  quantization of the the gap amplification part of Dinur's proof of the PCP
  theorem to the quantum setting would disprove the quantum PCP conjecture."
  Also: "very good expanders, with `Phi_G` approaching the maximum value 1/2, are
  not candidates for QMA-hard instances" (eq. (13)). On `k>2`: "To apply our proof
  techniques to k-local Hamiltonians for k > 2 and obtain error eps, we would need
  there to be `n^(k-1)/eps^(O(1))` terms, so only for k = 2 could this be
  interpreted as 'large constant degree.'" On gadgets: the 2-local Hamiltonian
  produced by perturbative gadgets "has a constant fraction of vertices with only
  constant degree, which means our results do not yield nontrivial bounds here."
- Section 2.2 gives polynomial-time approximation schemes for 2-local Hamiltonians
  on planar graphs (randomized) and for dense `k`-local Hamiltonians. Theorem
  numbers of those two were not read.

## 2. Aharonov--Eldar, arXiv:1301.3407v1, "Commuting local Hamiltonians on expanders, locally testable quantum codes, and the qPCP conjecture"

Numbers read from the v1 PDF, pp. 5--7.

- **Definition (bi-partite small-set expansion, TeX `def:expbi`).** A bipartite
  graph `G=(L,R;E)` (constraints on the left, particles on the right, right degree
  `D_R`) is `epsilon`-small-set-expanding if every `S subseteq R` with `|S|<=k`
  has `|Gamma(S)|>=|S| D_R (1-epsilon)`.
- **Theorem 1.** Let `gamma(eps)=2kd eps`. Let `H` be an instance of `CLH(k,d)`
  for constant `k,d` whose bipartite interaction graph has right degree `D_R` and
  is `eps`-small-set expanding, `eps<1/2`. For every eigenspace `lambda_i` there
  is `psi_i` with `| ||H psi_i|| - lambda_i | <= gamma(eps)||H||`, generated by a
  constant depth quantum circuit. "In particular, the gamma(eps)-approximation
  problem of CLH(k,d) on such eps small-set bi-partite expander graphs is in NP."
- **Theorem 2.** Given `eps<1/2`, it is NP-hard to approximate `CLH(k,d)` whose
  bipartite interaction graph is `eps` small-set expanding to within a factor
  `gamma(eps)=2kd eps`.
- **Theorem 3.** For a stabilizer code of distance `>1` with a `k`-local
  generating set, each qudit examined by `D_R` generators, whose bipartite
  interaction graph is an `eps`-small set expander with `eps<1/2`, every
  `delta<min{1/(k^3 D_R), dist(C)/2}` has robustness `r(delta)<=2 eps`.
- Source remark (p. 6): the smaller the expansion error of the graphs underlying
  the CLHs, "the weaker the qPCP theorem using these CLHs becomes."

## 3. Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4 (STOC'23), "NLTS Hamiltonians from good quantum codes"

- **Theorem 1 (No low-energy trivial states)** (v4 PDF p. 2). "There exists a fixed
  constant `eps>0` and an explicit family of `O(1)`-local frustration-free
  commuting Hamiltonians `{H^(n)}` where `H^(n)=sum_(i=1)^m h_i^(n)` acts on `n`
  particles and consists of `m=Theta(n)` local terms such that for any family of
  states `{psi_n}` satisfying `tr(H^(n) psi)<eps n`, the circuit complexity of the
  state `psi_n` is at least `Omega(log n)`."
- The Hamiltonians are the CSS stabilizer Hamiltonians `H=H_X+H_Z` of good qLDPC
  codes satisfying the clustering Property 1; Section 3 proves Property 1 for
  families of good qLDPC codes. The formal statement at the end of Section 2 has
  `eps < (1/(400c_1))(min{m_X,m_Z}/n) min{((k-1)/(4n))^2, delta_0, c_2/2}`.
- p. 1--2: "The NLTS conjecture is a necessary consequence of the quantum PCP
  conjecture, because QMA-complete problems do not have NP solutions and a
  constant-depth quantum circuit generating a low-energy state would serve as a NP
  witness." Open questions (p. 3) include "Our construction does not require
  quantum local testability" and "Can our proof techniques be generalized to prove
  non-trivial lower bounds for non-commuting Hamiltonians?"

## 4. Good qLDPC and quantum LTC status

- **Panteleev--Kalachev, arXiv:2111.03654v2.** TeX `th:qLDPC`: "For every number
  `R in (0,1)` and finite field `F_q` there exists an explicit family of quantum
  LDPC codes over `F_q` with the parameters `[[n, k>=Rn, d=Theta(n)]]_q`." TeX
  `th:LTC`: explicit `(omega,s)`-locally testable classical LDPC codes with
  `[n,k>=Rn,d=Theta(n)]_q` for every `R in (0,1/2)`.
- **Leverrier--Zemor, arXiv:2202.13641v3** (abstract): quantum Tanner codes on the
  left-right Cayley complex, linear minimum distance, and a theorem recovering the
  local testability of the Dinur et al. code.
- **Dinur--Lin--Vidick, arXiv:2402.07476v3** (abstract): for `t=4`, "almost-good"
  quantum LTCs "with constant relative rate, inverse-polylogarithmic relative
  distance and soundness, and constant-size parity checks."
- **Kalachev--Panteleev, arXiv:2501.01411v2** (abstract): random codes over a
  large field have good product expansion; "We believe that, in the case of four
  codes, the same ideas can be used to construct good quantum locally testable
  codes". This is stated as a belief, not a theorem.
- **Cross--He--Natarajan--Szegedy--Zhu, arXiv:2209.11405v3** (abstract): qLTCs of
  constant soundness, constant rate, and distance scaling with locality.
- **Wills--Lin--Hsieh, arXiv:2309.05541v3** (abstract): soundness amplification to
  a constant at a locality cost; "the first asymptotically good testable quantum
  code (rather than locally testable)".
- **Bounded absence check.** Two web searches (2026-09-12) and these abstracts
  found no source claiming quantum LTCs with constant rate, linear distance,
  constant soundness and constant locality. This is not a certificate of absence.

## 5. Games and proof-verification forms

- **Natarajan--Vidick, arXiv:1801.03821v2** (abstract) claimed a games quantum PCP
  for QMA under randomized reductions.
- **Natarajan, arXiv:2403.13084v1**, "The status of the quantum PCP conjecture
  (games version)" (abstract): "(2) we explain an error in the energy amplification
  procedure of Natarajan and Vidick (arXiv:1710.03062) which invalidates their
  claim to have constructed a quantum games PCP for a QMA-complete problem." Also:
  MIP* = RE and refinements "show that any connection between the 'constraint
  satisfaction' or 'Hamiltonian' quantum PCP conjecture and nonlocal games must
  involve restricting the players in the game to be computationally efficient",
  and the note highlights "the importance and challenge of understanding gap
  amplification for Hamiltonians even when locality is replaced by much weaker
  constraints". BMVZ (arXiv:2510.01333v1, Section 1.1) agrees the conjecture
  "remains open"; see `research/artifacts/qpcp-dinur-iteration-architecture-2026-09-11.md`.
- **Fitzsimons--Vidick, arXiv:1409.0260v1** (abstract): a five-prover one-round
  MIP* protocol for the local Hamiltonian problem with `O(log n)`-bit questions,
  constant-qubit answers, and inverse-polynomial completeness-soundness separation,
  "a first step towards a multiprover variant of the quantum PCP conjecture."
- **Buhrman--Helsen--Weggemans, arXiv:2403.04841v3** (Quantum 2025, abstract): a
  "detailed construction of the quantum reduction to a local Hamiltonian with a
  constant promise gap"; "(ii) If the q-local Hamiltonian problem with constant
  promise gap can be solved in QCMA, then QPCP[q] subseteq QCMA"; and oracles
  relative to which certain quantum PCP statements are false, so proofs need
  "(quantumly) non-relativizing techniques."
- MIP* = RE itself is recorded in `research/artifacts/mipstar-re-ingestion-2026-08-20.md`.

## 6. Dequantization with a guiding state

- **Gharibian--Le Gall, arXiv:2111.09079v5** (TeX labels, numbers not read).
  `th:classical`: "For any constants `eps,delta in (0,1]` and any `k=O(log n)`, the
  problem `GLH_est(k,eps,delta)` can be solved classically with probability at
  least `1-1/exp(n)` in `O(poly(n))` time." `th:hardness`: BQP-hard at
  inverse-polynomial precision with 6-local terms. `th:qPCP` (informal): with the
  promise that the ground state has constant overlap with a vector allowing
  sampling access, `LH(k,a,b)` with `b-a=Omega(1)` is in MA.
- **Weggemans--Folkertsma--Cade, arXiv:2302.11578v3** (abstract): guidable local
  Hamiltonian problems at constant precision lie in NP (or NqP) when the guiding
  state is classically evaluatable.

## 7. Geometry and triviality

- **Freedman--Hastings, arXiv:1301.1363v2**: non-`k`-hyperfinite complexes; a toric
  code on a non-1-hyperfinite complex with a one-sided NLTS property. Their appendix
  quotes Elek's graph hyperfiniteness (delete an `eps` fraction of edges, leave
  components of bounded diameter).
- **Hastings, arXiv:1201.3387v3** (abstract): commuting projector Hamiltonians whose
  interaction complex maps to a 1-complex with bounded-diameter preimages have
  trivial ground states under one technical condition; after removing a small
  fraction of sites such states "can act as a classical witness to the existence of
  a low energy state."
- **Bafna--Vyas, ECCC TR26-150** (19 Aug 2026), "Private PCPs from Product
  Expansion" (abstract): "The quantum analogue of the PCP theorem for QMA remains
  wide open. A central obstacle is the local indistinguishability of quantum
  codes". They build classical private PCPs for NP (`sqrt(n)` queries, fractional
  privacy `Omega(1/log n)`, constant soundness gap) as a relaxation of the
  Anshu--Breuckmann--Nguyen fault-tolerance approach.

## 8. Regime map (synthesis; each line cites the item above)

| Regime of the hard family | Consequence | Source |
|---|---|---|
| 2-local, `D`-regular, `D > 1728 d^2 ln(d)/gap^3` | NP witness | BH Cor. 5 |
| blocks of size `O(log n)` with small `Phibar_G/D` or sub-volume entanglement | NP witness | BH Cor. 7 |
| degree-amplifying energy-monotone 2-local map with `d_t=d^t` | constant-gap estimation in NP | BH Cor. 11 |
| commuting, small-set expansion error `eps` with `2kd eps < gap` | NP witness (constant depth) | AE Thm. 1 |
| planar 2-local; dense `k`-local | PTAS | BH Sec. 2.2 |
| guiding state with sampling access | MA (constant precision) | GLG `th:qPCP` |
| low-energy states of constant depth | NP witness; NLTS families exist | ABN Thm. 1 |

What escapes all rows: bounded degree, not almost-perfectly small-set expanding,
noncommuting or with expansion error above `gap/(2kd)`, block-volume-law
entanglement, no efficiently samplable guide, and NLTS. Tensor-product
amplification (BMVZ) avoids Corollary 11 by growing locality rather than
degree at locality two.
