---
rg: 2
id: finite-bad-character-packing-extension
kind: claim
title: Bad BCS characters admit large trace-compatible finite-overgroup packings
distinct_from:
  simultaneous-bad-character-packing-extension: That asks for one joint cross-type orthogonality system at threshold 2/beta; this asks for separate trace-compatible finite overgroups and pays the maximal-type factor M.
  finite-selector-gadget-induction-barrier: That says every character of a finite selector subgroup survives in some representation of every finite overgroup; this asks for a chosen tracial mixture avoiding the bad character while the character idempotent remains nonzero and has many conjugates.
  finite-depth-adaptive-selected-atom-escape-tree: That asks for node-dependent overlap escape on reached reducing carriers; this asks for a static root packing and a prescribed trace extension.
  abelian-matrix-hnns-have-marked-finite-quotients: That seeks finite quotients for families of matrix HNNs; this requires quantitative nonintertwining of one character idempotent and exact realization of one restriction distribution.
  finite-character-hecke-intersection-formula: That computes the exact regular norm of every proposed overlap; this asks for finite overgroups whose transported bad-character intersection labels are all incompatible while the prescribed trace still extends.
  finite-character-packing-extension-is-clique-lp: That decides both clauses for each fixed finite candidate group; this asks for the construction of some candidate passing those finite tests at the required threshold.
---

**OPEN FINITE PACKING--EXTENSION LEMMA.** For every forbidden type `i` of
the fixed robust shared BCS, let

```text
H_i=<J,B,x_v : v in X_c>
```

be its finite abelian seed-context subgroup, let `chi_i` be the character

```text
chi_i(J)=-1,       chi_i(B)=1,       chi_i(x_v)=a(v),
```

and let `mu_i` be the exact tracial character distribution on `widehat(H_i)`.
Thus `mu_i(chi_i)=0`.

Construct a finite overgroup `G_i>=H_i` and elements
`g_(i,1),...,g_(i,K)` for

```text
K=floor(2M/beta)+1                                   (FBE1)
```

such that:

1. `J` is central in `G_i`;
2. the conjugates `g_(i,r)e_(chi_i)g_(i,r)^(-1)` are pairwise orthogonal in
   `C[G_i]`; and
3. `mu_i` is the restriction of a tracial state on `C^*(G_i)`.

Equivalently, condition 3 says that `mu_i` lies in the convex hull of the
normalized `H_i`-weight multiplicity distributions of the irreducible
representations of `G_i`.

By `finite-character-hecke-intersection-formula`, condition 2 is equivalent
to disagreement of the transported bad characters on every pairwise
intersection of transported context subgroups.  It is therefore a finite
labelled-intersection problem, but condition 3 must hold simultaneously. No
construction satisfying all three conditions is currently known.

For any proposed finite `G_i`,
`finite-character-packing-extension-is-clique-lp` makes the audit exact:
condition 2 is a coloured-clique search in the transported-character
intersection graph, and condition 3 is a rational linear feasibility
problem over `Irr(G_i)`.

## Surviving route

Finite graphs of finite groups may allow conjugate context subgroups with
controlled intersections: transported bad characters can disagree on every
pairwise intersection even when no global automorphism permutes one fixed
context subgroup. The allowed characters in the support of `mu_i` must at
the same time extend through the finite graph. This is the concrete finite
character-table design problem left by the audit.

## Attempts

- **Semidirect orbit.** Distinct characters in an automorphism orbit are
  orthogonal, but `semidirect-bad-orbit-needs-zero-trace-support` shows that
  exact extension forces the entire bad orbit to lie in the zero support of
  `mu_i`.
- **Independent selectors.** Each added selector bit doubles the orbit menu
  while halving the guaranteed refined atom mass; the packing ratio does not
  improve.
- **Bare finite Bass--Serre attachment.** Amenable-edge hyperlinearity
  permanence shows that attaching finite overgroups along finite context
  groups cannot destroy a canonical matrix model of a hyperlinear base. A
  successful use of the lemma must therefore verify that the packing
  identities and contextual soundness coexist in the actual combined
  presentation; trace-compatible extension of a selected noncanonical model
  alone is not a canonical-trace obstruction.
