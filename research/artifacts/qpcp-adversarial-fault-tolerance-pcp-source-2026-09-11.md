# Anshu--Breuckmann--Golowich--Nguyen--Vazirani, adversarial fault tolerance and PCPs: source record (2026-09-11)

Recorded by the literature scout `lit-probability-tcs` for the quantum PCP lane.

## Provenance

- Anurag Anshu, Nikolas P. Breuckmann, Louis Golowich, Quynh T. Nguyen and
  Umesh Vazirani, *Classical Adversarial Fault-Tolerance and PCPs*,
  arXiv:2608.16860**v1**, submitted 17 August 2026. The abstract page lists v1 as
  the only version on 2026-09-11.
- Read on 2026-09-11 from the arXiv abstract page and the HTML rendering of v1,
  through an automated fetch. The statements below are quoted from that
  rendering.
- Trust surface: unrefereed preprint.

## Abstract (verbatim)

> We show how to compile an arbitrary classical circuit into a fault-tolerant
> circuit, which performs the desired computation even when an almost-linear
> number of bits are adversarially chosen and corrupted in each timestep. Using
> a variant of this fault-tolerance scheme that only detects (rather than
> corrects) corruptions, we give a new construction of probabilistically
> checkable proofs (PCPs) for NP with polylogarithmic query complexity. This
> PCP construction from fault-tolerance presents a promising candidate for
> quantization by the work of Anshu, Breuckmann, and Nguyen (STOC'24), who
> provided a roadmap for constructing quantum PCPs via fault-tolerance.

## Statements (from the HTML rendering)

- **Theorem 1.1 (fault detection).** For every set N̄ of logical dits and every
  ε>0, there exists a fault-detecting scheme that maps an arbitrary logical
  circuit R̄ acting on dits N̄ using time T̄ to a fault-detecting physical
  circuit R acting on |N| ≤ |N̄|^(1+ε) dits using time T ≤ T̄·(log|N|)^O(1/ε),
  with error thresholds λin ≥ λout ≥ λrun = λdet ≥ |N|/(log|N|)^O(1/ε).
- **Theorem 1.1 (fault tolerance).** For every set N̄ of logical dits, there
  exists a fault-tolerance scheme mapping R̄ to a fault-tolerant physical
  circuit R acting on |N| ≤ |N̄|·2^O((log|N|)^(2/3)) dits using time
  T ≤ T̄·2^O((log|N|)^(2/3)), with error thresholds
  λin ≥ λout ≥ λrun ≥ |N|/2^O((log|N|)^(2/3)).
- **Theorem 1.4 (PCP).** For every ε>0 there is a polynomial-time algorithm
  that takes a circuit R of size s with a single output bit and outputs a
  constant-locality CSP instance P with n ≤ s^(1+ε) variables and m = Θ(n)
  constraints such that: if some input x has R(x)=0 then P is satisfiable; if
  every input x has R(x)=1 then every assignment for P has at least
  1/(log m)^O(1/ε) unsatisfied constraints. The query complexity is
  polylogarithmic after (log m)^O(1/ε) repetitions; the gap is not constant.

Quoted remarks on quantization: "[ABN24] suggested that fault-tolerance schemes
could provide a route towards proving the quantum PCP conjecture"; "this
approach requires fault-tolerance schemes protecting against an almost-linear
number of errors with respect to the total number N of qudits. Achieving such
strong error protection was previously an open problem"; "There remain open
questions from [ABN24] regarding the mapping from fault-tolerant circuits to
PCPs, whose resolution is needed to construct a quantum PCP with nontrivial
(i.e. subpolynomial) query complexity."

## Bearing on this graph

- It bears on `quantum-pcp-constant-gap-local-hamiltonian` through the
  fault-tolerance roadmap of Anshu--Breuckmann--Nguyen (arXiv:2309.16475). It
  does not prove the conjecture.
- Correction from the `quantum-pcp` lane (2026-09-11): the exact combinatorial
  gap (LPC1) is already established trivially in this graph by
  `positive-shift-trivializes-exact-combinatorial-soundness` and
  `lpc1-from-shifted-kitaev-reduction`, so this source must not be cited as
  supplying (LPC1). Its place is beside `whole-time-slice-corruption-costs-inverse-depth`,
  as a candidate classical ingredient for the open hole
  `locality-reduction-with-amplifier-independent-loss` on the route
  `qpcp-by-dinur-iteration`. It does not discharge that hole: its gap is
  inverse polylogarithmic and the construction is classical.
- Forwarded on 2026-09-11 to the fork `quantum-pcp`, which wired it into the
  region itself.
