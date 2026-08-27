# Quantum low-degree tests as occurrence metapixels

## Result

The Natarajan--Vidick quantum low-degree test is the first concrete object in
this lane which genuinely performs global Pauli synchronization without
pairwise equality clouds.  Its soundness is on the original strategy and its
perfect-completeness version forces local dimension at least `q^n` at one
fixed success threshold, once `d/q` is fixed sufficiently small.

It does not directly finish the occurrence compiler.  The published test
uses a growing field and growing plane-answer packet, and its mixed test
samples every X point against every Z point.  The complete mixed rectangles
therefore survive, while ordinary degree reduction recreates the already
proved two-pair contour obstruction.

## Exact parameter audit

Theorem 3.2 of arXiv:1801.03821 uses `h^m>=n`, `d=hm`, and robustness with an
additive `poly(d/q)` term.  The usual choice has

```text
m ~ log(n)/log log(n),  h ~ log(n),  q >= const d.
```

Thus the sometimes-suggested specialization to one fixed sufficiently large
field is not uniform in `n`.  The underlying tensor Reed--Solomon relative
distance `((q-h)/q)^m` gives the same warning.

## Surviving target

The smallest new object is not another equality expander.  It is an
operator-valued, entanglement-sound twisted-commutation sampler coupled to a
constant-alphabet agreement code.  It must simultaneously:

- decode global X and Z polynomial/linearity measurements on the same
  Hilbert space;
- infer the uniform Weyl relation from bounded-incidence mixed tests;
- retain perfect completeness;
- expose only finitely many local group-word templates; and
- have sign-safe relative girth or balanced mixed contours.

This target is recorded as
`bounded-degree-entangled-agreement-pauli-metapixel`.  Proving it would plug
directly into the existing relative-coset/Greendlinger compiler.

## Primary sources checked

- A. Natarajan and T. Vidick, *Robust self-testing of many-qubit states*,
  arXiv:1610.03574.
- A. Natarajan and T. Vidick, *Low-degree testing for quantum states, and a
  quantum entangled games PCP for QMA*, arXiv:1801.03821, especially the
  protocol in Figure 2 and Theorem 3.2.
