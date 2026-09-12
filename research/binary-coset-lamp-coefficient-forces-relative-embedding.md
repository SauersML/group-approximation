---
rg: 2
id: binary-coset-lamp-coefficient-forces-relative-embedding
kind: claim
title: A Connes-embeddable binary coset-lamp coefficient gives scalar relative embeddability
distinct_from:
  fd-fell-coset-observable-gaussianizes-wreath: That constructs ordinary wreath microstates from exact finite-image orthogonal actor representations; this starts from a CE algebra carrying one involution coefficient and constructs a scalar conditional-expectation commuting square without exactifying its actor.
  relatively-embeddable-pair-makes-the-hnn-group-hyperlinear: That consumes scalar relative embeddability to construct an HNN model; this extracts the relative embedding from one binary lamp and is its needed reverse input.
  arithmetic-double-swap-extension-is-binary-coset-wreath: That gives the group identity and index-two microstate transfer; this obtains scalar relative embeddability by tensoring independent swap expectations.
artifacts:
  - research/artifacts/tensor-swap-expectation-repair-2026-09-07.md
---

Let `C<=A` be countable groups. Suppose a Connes-embeddable finite tracial
algebra contains the canonical group unitaries `u_g` of `L(A)` and a
self-adjoint unitary `s` such that

```text
[s,u_c]=0                           (c in C),
tau(u_g^* s u_g s)=1_(g in C)        (g in A).
```

Then `L(C)<=L(A)` is relatively embeddable over the scalar complex field.
There are canonical actor microstates `V_j(g)` and finite-dimensional
subalgebras `B_j` with

```text
dist_2(V_j(c),B_j)->0                (c in C),
||E_(B_j)(V_j(g))||_2->0             (g outside C).
```

Both ordinary and free binary coset-wreath groups carry the displayed
coefficient in their canonical traces. Thus hyperlinearity of either group
implies scalar relative embeddability. The free binary group is the
index-two swap extension of `A *_C A`; consequently hyperlinearity of the
plain double also implies scalar relative embeddability for every countable
pair.

The construction uses `k` independent tensor coordinates. The squared
conditional-expectation norm of an off-subgroup actor word is asymptotically
`2^-k`. It uses group comultiplication and does not repair or invoke the
general-von-Neumann-algebra converse in Gao Appendix Theorem 7.1.
