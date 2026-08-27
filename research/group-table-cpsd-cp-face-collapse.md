---
rg: 2
id: group-table-cpsd-cp-face-collapse
kind: claim
title: Classical and quantum conic descriptions of a group table have equal closures
distinct_from:
  hyperlinear-implies-sofic: that is the group statement quantified over all groups; this is a convex-geometry statement about two cones associated with one finite table, whose failure would be a finite certificate and whose proof would explain the group statement rather than restate it.
  finite-table-quantum-classical-hamming-gap: that is the negation of this claim in its quantitative form — an exposed functional separating the two feasible regions on some table. Establishing either forecloses the other; they are recorded separately because their consumers differ, one feeding the affirmative answer and one feeding the separation.
  definetti-group-table-rounding: that is a rate — a rounding map at a finite symmetric-extension level with explicit parameters; this is an exact statement about closures with no rate at all, and could hold with no effective bound whatsoever.
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**Target.**  Attach to a finite partial multiplication table `T` a correlation
system whose *classical* feasible points encode finite partial actions of `T`
by bijections, and whose *finite-dimensional quantum* feasible points encode
unitary models of `T` with regular-trace separation.  Then

```text
closure( C_class(T) )  =  closure( C_quant(T) )
```

on the regular-character face.

The two sides are the completely positive and the completely positive
semidefinite cones respectively: the CP/CPSD pair is the standard algebraic
separation of classical from finite-dimensional quantum feasibility for
correlation data (Sikora–Varvitsiotis arXiv:1506.07297; Laurent–Piovesan
arXiv:1312.6643), and noncommutative CSP rounding gives the language for
operator assignments (Culf–Mousavi–Spirig arXiv:2312.16765).  None of those
papers is imported as a premise: what they supply is the encoding vocabulary,
and the content here is that the *group-table face* behaves differently from a
generic instance.

**Why the face might collapse when the cones do not.**  Globally CP and CPSD
are very different, and generic noncommutative CSPs have integrality gaps.
The group-table face is not generic: it is closed under an associative
composition, every generator variable is invertible, the marginals are uniform
(the trace is the regular one), and separation is imposed at the regular
character.  The claim is that these four constraints together destroy the
usual quantum advantage.  If true it is a conceptual explanation of the
affirmative answer to Q3.4 — arbitrary quantum constraint systems round badly,
group-action constraint systems at the regular trace do not — rather than a
technique-driven proof.

**What a proof would have to produce.**  Either a direct argument that the
extreme points of the quantum face are classical, or a rounding scheme; the
latter is the quantitative version and is `definetti-group-table-rounding`.
The interest of the conic form is the dual: failure is witnessed by a single
exposed linear functional, i.e. a finite trace-polynomial inequality valid for
all finite actions and violated by some finite-dimensional unitary table.
That is a computationally searchable object (moment/SOS hierarchies on the
quantum side, CP/copositive relaxations on the classical side, symmetry
reduction from the table), which is why this claim is worth carrying even
though it has no rate.

## Attempts

- **Quote a known CP = CPSD result.**  None applies: equality is known only in
  small dimensions and special combinatorial cases, and is false in general.
  Nothing off the shelf sees the group-table face.
- **Argue extreme points of the quantum face are permutation models by a
  Birkhoff-type theorem.**  This is the natural first attempt and it is exactly
  the one refuted in the channel setting by `asymptotic-quantum-birkhoff-false`.
  The refutation does not literally apply here — the face is different — but it
  removes every argument that would work for arbitrary bistochastic data, which
  is most of the naive ones.
- **Reduce to the two-marginal case, where Birkhoff does hold.**  Dies on
  associativity: the group table constraint is genuinely three-index
  (`gh = k` couples input, middle and output), and the two-marginal miracle has
  no analogue for higher stochastic tensors.
- **Deferred, and cheap:** compile a tiny table into both relaxations and ask a
  solver for a separating dual functional.  A robust separator refutes this
  claim and is the seed of `finite-table-quantum-classical-hamming-gap`; the
  absence of separators across many small tables is evidence for the collapse
  and tells the affirmative programme where to look.
