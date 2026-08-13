# Audit of the affine base used in Theorem A — 2026-08-13

This note isolates the two external inputs behind the literal affine base in
`non_mf_groups_exist.tex`: its finite presentation and property (T).  It also
records the proof shape needed for a premise-free formal identification of the
twenty-relator group with `Z^3 ⋊ SL_3(Z)`.

## Matrix-labelled presentation

The eight relations printed in the manuscript are the Conder--Robertson--
Williams presentation

```text
x^3 = y^3 = z^2 = (xz)^3 = (yz)^3
    = (x^-1 z x y)^2 = (y^-1 z y x)^2 = (xy)^6 = 1.
```

The current labels are correct:

```text
x = [[ 0, 1, 0], [0,  0,  1], [ 1,  0,  0]],
y = [[ 1, 0, 1], [0, -1, -1], [ 0,  1,  0]],
z = [[ 0, 1, 0], [1,  0,  0], [-1, -1, -1]].
```

Conder--Liversidge--Vsemirnov, *Generating pairs for SL(n,Z)*,
J. Algebra 662 (2025), 123--137, DOI 10.1016/j.jalgebra.2024.08.008,
records this exact matrix-labelled presentation in its Introduction and
attributes it to Conder--Robertson--Williams.  The accepted manuscript was
checked through the University of Auckland repository.  Its Section 2 also
records the order-two presentation automorphism interchanging `x` and `y`
and fixing `z`; this explains why secondary sources sometimes use the
opposite `x,y` convention without changing the relator list.

The columns give exactly the nine conjugation relations printed for the
translation generators:

```text
x: e1 |-> e3,       e2 |-> e1,       e3 |-> e2;
y: e1 |-> e1,       e2 |-> -e2+e3,   e3 |-> e1-e2;
z: e1 |-> e2-e3,    e2 |-> e1-e3,    e3 |-> -e3.
```

Thus the affine presentation has exactly twenty relators: eight base
relators, three commutativity relators, and nine action relators.

## Completeness proof for the twenty-relator presentation

Let `P` be the abstract group defined by the twenty relators, let `S` be the
abstract group defined by the eight CRW relators, and let `A = Z^3`.

1. The six displayed matrices and vectors induce a surjective homomorphism
   `Phi : P -> A ⋊ S`.
2. The three commuting elements `v1,v2,v3` induce
   `V : A -> P`, with
   `V(n1,n2,n3) = v1^n1 v2^n2 v3^n3`.
3. The base relators induce `B : S -> P` sending the abstract base generators
   to `x,y,z`.
4. For each base generator, the nine action relators and the basis
   decomposition of `A` prove
   `B(s) V(a) B(s)^-1 = V(s*a)` for every `a`.  The set of `s` satisfying
   this identity for all `a` is a subgroup of `S`; since it contains
   `x,y,z`, the covariance identity holds for every `s`.
5. Define `Psi(a,s) = V(a) B(s)`.  Covariance gives
   `Psi(a,s) Psi(b,t) = Psi(a+s*b, st)`, so `Psi : A ⋊ S -> P` is a
   homomorphism.
6. `Phi ∘ Psi` is the identity by the definitions of `V` and `B`.
   `Psi ∘ Phi` fixes all six presentation generators, hence is the identity
   by presentation induction.  Therefore `P` is isomorphic to `A ⋊ S`.

This normal-form/inverse argument is preferable to an informal appeal to
“reading off the columns”: it makes surjectivity, covariance, and absence of
extra relations explicit.  It is also the direct proof shape to reproduce in
Lean.

## Property (T)

Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Example 1.7.4(i),
states exactly that `SL_n(Z)` and `SL_n(Z) ⋉ Z^n` have property (T) for
`n >= 3`.  Their proof uses:

- Theorem 1.4.15 and Corollary 1.4.16 for property (T) of the ambient Lie
  groups `SL_n(R)` and `SL_n(R) ⋉ R^n`;
- Theorem 1.7.1, which transfers property (T) between a locally compact group
  and a lattice.

Consequently the manuscript's claim for `Z^3 ⋊ SL_3(Z)` is correctly cited.
No separate finite-index or relative-property argument is needed.

## Remaining premise-free formalization gap

The literature checks establish the printed mathematics but cannot serve as
axioms under the project's strict trust policy.  A literal, unconditional
formal Theorem A still requires both of the following internal results:

1. a proof that the eight-relator presented group is isomorphic to the
   displayed matrix group `SL_3(Z)` (or a formal derivation from an internally
   proved transvection presentation), followed by the semidirect-product
   inverse above; and
2. an internal proof of property (T), or a checked finite Kazhdan/SOS
   certificate, for the resulting affine group.

Direct matrix evaluation proves only that the matrices satisfy the eight
relations.  It does not prove that those relations are complete.  Likewise,
the nine action relations prove covariance only after the base presentation
has been identified.  These are the precise missing group-generation and
presentation facts; citing CRW or BHV is mathematically legitimate in the
paper but does not discharge the premise-free Lean endpoint.

The original CRW article was blocked by AMS/JSTOR anti-bot responses during
this pass.  The exact presentation was nevertheless checked in the open
accepted manuscript of the 2025 paper by Conder and coauthors, one of whom is
the first author of CRW.  The BHV book was checked from its complete freely
available PDF.
