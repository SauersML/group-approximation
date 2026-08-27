# Quantum PCP by syndrome exactification -- Cairn ingestion audit

**Date:** 2026-08-25.  Ingests an external note ("Quantum PCP -- Cairn
syndrome-rounding attack") that proposes to combine the July 2026
locality-preserving *combinatorial* gap amplifier with this repository's
exactification technology.  This file records what was verified, what was
corrected, and what was deliberately not imported.

## 1. Citations checked against primary sources

| source | status |
| --- | --- |
| arXiv:2309.16475, Anshu--Breuckmann--Nguyen, *Circuit-to-Hamiltonian from tensor networks and fault tolerance*, STOC 2024 | **verified**; abstract states adversarial-noise semantics at energy density *exponentially* small in depth, and combinatorial-state semantics at *polynomially* small density |
| arXiv:2608.16857, Breuckmann--Golowich--Vazirani, *Fault-Tolerant Quantum Computation with Adversarial Errors* | **verified**; already in the graph as `bgv-adversarial-fault-tolerance`.  Tolerance is `N^(1-o(1))` corrupted qudits per time step |
| ECCC TR26-150 (19 Aug 2026), Bafna--Vyas, *Private PCPs from Product Expansion* | **verified**; opens "The quantum analogue of the PCP theorem for QMA remains wide open" |
| Simons Institute talk, 23 July 2026, *Gap Amplification for Local Hamiltonians with Combinatorial Soundness*, Quynh T. Nguyen (Harvard) | **verified as a talk**; abstract claims "the first known viable template for quantum locality-preserving gap amplification" and that "we prove that our procedure amplifies combinatorial gap" |
| arXiv:0811.3412, Aharonov--Arad--Landau--Vazirani, *The Detectability Lemma and Quantum Gap Amplification* | **verified** |

Two provenance corrections to the incoming note.

* The amplifier was attributed to "Bafna--Nguyen--Zhang".  The Simons page
  names only the speaker, and **no preprint was locatable** from arXiv
  listing search or the arXiv API on 2026-08-25.  The graph therefore does
  **not** establish the amplifier by citation.  `locality-preserving-constant-combinatorial-gap`
  is an OPEN claim whose body records the talk.
* Even granting the talk in full, it does not deliver criterion (C).  The
  abstract says amplification is locality-preserving at the cost of
  "moderately increasing its local qudit dimension".  Reaching a *constant*
  combinatorial gap from an inverse-polynomial one needs `Theta(log)`
  iterations, and nothing in the abstract bounds the alphabet after
  iteration.  Constant gap **and** constant alphabet is a strictly stronger
  statement than what is announced.

## 2. The transfer theorem is an equivalence, not a reduction

The note's Theorem 2.3 -- combinatorial gap `beta` plus a `C`-rounder implies
`lambda_min >= beta/C` -- is correct.  Its converse is also true and was not
stated, and the converse is what matters.

Let `s* = min{|S| : some normalized sigma has Tr(h_a sigma)=0 for all a not in S}`.
The instrument that discards its input, prepares a minimizer `sigma*`, and
outputs the fixed label `S*` is CPTP and satisfies clause (1) of Definition
2.2 by construction.  Its cost clause reads `s* <= C m Tr(H rho)` for every
`rho`, which is exactly `s* <= C m lambda_min(H)`.  Hence

```text
inf{C : a C-rounder for H exists} = s* / (m lambda_min(H)),
```

so "some constant-cost rounder exists" is **logically equivalent** to
"the energy gap is constant".  Definition 2.2 places no locality, no
efficiency, and no closeness-to-input requirement on the instrument, and
without one of those the transfer theorem renames its conclusion.

This is the repository's own `RESTATEMENT DRESSED AS REDUCTION` failure mode.
It is recorded inside `combinatorial-gap-and-rounder-give-energy-gap`, which
now carries both directions, so that no later reader treats the bare
existence of a rounder as progress.

**Where the content actually is.**  All of it is in the extra structure
Proposition 3.1 demands: the fault set `S` must be the outcome of a *joint
measurement of commuting local projectors of bounded overlap*.  That is the
statement `local-syndrome-port-domination-at-each-gadget`, and it is the only
node in the region whose truth is not already equivalent to the conjecture.

## 3. (SD) is not a strengthening of the cost clause

The note presents the operator inequality

```text
W^* (sum_a B_a) W <= C sum_a h_a                              (SD)
```

as a "concrete sufficient condition" for clause (2).  In fact the two are
equivalent: for self-adjoint `X, Y`, `X <= Y` holds iff `Tr(X rho) <= Tr(Y rho)`
for every state `rho`, and `E|S| = sum_a Tr(B_a W rho W^*)` because the `B_a`
commute.  So (SD) *is* clause (2) quantified over all inputs, written
operator-side.

The genuine additions in Proposition 3.1 are therefore exactly two, and both
are recorded as separate holes:

1. the `B_a` **commute**, so `S` is a genuine classical set rather than a
   sequence of disturbing measurements -- this is what makes `E|S|` a
   cardinality at all;
2. **(EX)**, syndrome-conditioned exactification, which must return a state
   on the space where the `h_a` live.  The note writes `sigma_S` as a "data"
   state on `H_data` while clause (1) tests it against `h_a` on `H`; the
   pullback along `W` is an implicit and load-bearing part of the hypothesis.

Note also that for `h_a >= 0` and `sigma >= 0`, `Tr(h_a sigma) = 0` iff
`h_a sigma = 0`, so the note's two spellings of exactness agree.

## 4. The local-to-global step is already established here

The note's "local version" of (SD) -- per-port domination plus bounded
occurrence -- is, after evaluation in the input state, *verbatim* the
incidence lemma this graph already proves as
`bounded-overlap-syndrome-energy-accounting`:

```text
q_j = Tr(B_j W rho W^*),   e_r = Tr(h_r rho),   L = C_0,   D = R.
```

No new accounting node was written.  The QPCP route consumes the existing
one.  This is the single cleanest point of contact between the two programs.

## 5. The checkpoint lemma is correct and its conclusion is a local charge

Abstracting the ABN backward Bell-syndrome estimate as
`b_t <= L (e_t + b_(t+1))` and iterating to the next checkpoint gives the
note's (4.3).  The iteration is routine; what is worth naming is that the
conclusion

```text
b_t <= L^r ( sum_(s=t)^(c-1) e_s + A e_c )
```

is *exactly* the local-charge hypothesis consumed in section 4 above, with
neighbourhood `N(t) = [t, c]` of width at most `r+1`.  So checkpointing and
the incidence lemma compose without a further step, which is why the region
routes them together.

The lemma does **not** produce the checkpoints.  Knill--Laflamme gives the
abstract logical/syndrome separation on a correctable error set (after
diagonalizing `c_(alpha beta)`, coherent recovery has the form
`R E_alpha P = P tensor |s_alpha>`), but the missing quantitative property is
a constant-locality parent-Hamiltonian inequality realizing `b_c <= A e_c`
with `A` independent of code size *and* a decoder whose depth does not grow
with the global code.  Without the second, `L^r` is replaced by `L^(decoder
depth)` and nothing was gained.  That is `bounded-horizon-syndrome-anchor-exists`.

## 6. The shear obstruction, in a form that is provable

The note's section 6 argues by a frame rotating by `theta/D` per step.  The
argument is right but the version worth recording is quantitative and
endpoint-relative, because the bare statement is compatible with a rounder
that simply discards its input (see section 2).

Take qubits `0..D`, `h_t = (I - SWAP_(t,t+1))/2`, and the product state
`rho_D = tensor_t |v_t><v_t|` with `v_t` at Bloch half-angle `t theta/D`.
Then `sum_t Tr(h_t rho_D) = (D/2) sin^2(theta/D) <= theta^2/(2D)`, while a
state exactly satisfying **every** term is supported in the symmetric
subspace of all `D+1` qubits, hence is invariant under permuting them, hence
has all single-qubit marginals equal -- but `rho_D`'s endpoint marginals are
at trace distance `2 sin theta`.  So any exactifier that preserves the
endpoint marginals must spend `|S| >= 1` against an energy of order `1/D`:
its cost constant is at least `2D/theta^2`.

That is the honest form of "the obstruction is a continuous shear": exact
fault count and soft energy are decoupled by a factor growing with depth as
soon as the exactifier is required to keep constant-scale logical data.  It
is recorded as `coherent-shear-is-combinatorially-invisible`.

## 7. The tracial fence, sharpened

The note says the tracial Hilbert--Schmidt geometry "fails" to give (SD) and
that the author tried the obvious identifications.  An assertion of a failed
search is not evidence; here is the actual fence.

Every gap theorem in this corpus is an inequality of quadratic forms on
`L^2(M,tau)` -- the GNS space of the *normalized trace*.  (SD) is an
inequality in the state-weighted tensor-product geometry, and on a QMA
instance the state is a pure witness.  Trace-weighted domination gives
nothing there: with `d >= 2`, `psi = e_1`,

```text
A = |psi><psi|,   B = (I - |psi><psi|)/(d-1),   tau(A) = tau(B),
Tr(A |psi><psi|) = 1,   Tr(B |psi><psi|) = 0,
```

so no constant `c` makes `Tr(A rho) <= c Tr(B rho)` hold for all states.  The
only general comparison is `Tr(A rho) <= ||rho||_inf * d * tau(A)`, whose
factor is `d = 2^n` on a pure witness -- a modular condition number, exactly
the dependence the note's section 10 asks to avoid.  Recorded as
`tracial-domination-is-not-state-domination`, which kills the import route
from `balanced-overlay-common-reducing-outlier-cut` and
`gapped-face-pinchings-give-same-hilbert-code-pvm-rounding`.

## 8. What the overlay technology does transfer

Not the estimates -- the diagnosis.  `quadratic-overlay-has-uniform-linearized-synchronization-gap`
establishes a dimension-free *linearized* transversality gap and then states
plainly that this is not enough: a Newton or alternating-projection argument
also needs entry into one uniform nonlinear tube, and normalized-HS smallness
supplies no such tube.  The identical shape appears here.  A per-gadget
spectral gap for the syndrome ports is a linearized statement; (SD) is a
global operator inequality against an arbitrary witness.  So the design
advice this corpus can give the QPCP attack is: **do not budget for a
linearized port gap and expect (SD); budget for a basin-capture or truncation
theorem in the state-weighted geometry.**

## 9. Not imported

* The amplifier as an established citation (section 1).
* Any node asserting that quantum PCP is closed, or that the note's
  Criterion 7.1 is discharged.  It is a hole with four open prerequisites.
* A second incidence-counting lemma (section 4 reuses the existing one).
* Knill--Laflamme as a graph node: it enters only as prose justification
  inside `bounded-horizon-syndrome-anchor-exists`, because nothing in the
  region derives anything from it alone.
