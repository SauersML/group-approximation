# Finite-presentation `INF/FIN` compilers: a uniform-seed-map firewall

**Date:** 2026-08-26  
**Scope:** finite-presentation hardness only  
**Method:** Cairn proof from finite derivation enumeration and diagonalization  
**Not used:** Lean, MSI, literature, tensor synchronization, or
`Transport.CompletionLemma`

## Verdict

No complete finite-presentation `INF/FIN` compiler is currently justified by
the repository.  More strongly, a large class of seemingly natural compiler
designs is impossible.

Let `E` be a fixed finitely presented non-MF group.  There cannot be a
computable family of finite presentations `R_e` together with a computable
tuple of words defining a homomorphism

\[
  \phi_e:E\longrightarrow R_e
\]

for every `e`, such that

\[
  e\in\mathrm{FIN}\Longrightarrow\phi_e\text{ is injective},
  \qquad
  e\in\mathrm{INF}\Longrightarrow R_e\text{ is MF}.
\]

The reason is not group theory.  The noninjectivity set of any such uniformly
displayed family of homomorphisms is `Sigma^0_2`, whereas the two branch
conditions would make it exactly `INF`, which is `Pi^0_2`-complete and not
`Sigma^0_2`.

Consequently, “replace the literal forbidden group by an arbitrary finitely
presented non-MF group” is valid only **after** a genuinely branch-sensitive
finite-output compiler has been proved.  It is not itself a compiler.  In a
successful construction the negative embedding must be assembled using the
finite-branch witness (for the ray switch, a last event/cut), and cannot be a
single computable map carried through both branches.

This also disproves the unrestricted meta-principle that heredity, one good
group, and one forbidden finite presentation automatically imply
`Pi^0_2`-hardness on finite presentations.  The property “is the trivial
group” satisfies those three clauses, but triviality of a finite presentation
is recursively enumerable.

## 1. Effective conventions

Fix a finite presentation

\[
  E=\langle x_1,\ldots,x_m\mid r_1,\ldots,r_k\rangle.
\]

For every finite presentation, equality of a word to the identity is
recursively enumerable without any external theorem: enumerate finite
products of conjugates of defining relators and their inverses, freely reduce,
and compare with the word.  Write

\[
  D_E(w,t)
\]

for the decidable assertion that `t` is such a derivation of `w=1` in `E`.
Then

\[
  w\ne_E1\quad\Longleftrightarrow\quad
  \forall t\;\neg D_E(w,t).                                      \tag{1}
\]

Likewise, from a computable finite-presentation code `e |-> R_e`, and a
computable substitution of the `x_i` by words in the generators of `R_e`,
there is a decidable predicate

\[
  D_R(e,w,s)
\]

saying that `s` proves the substituted word `phi_e(w)` trivial in `R_e`.

No solution of a word problem is used here; only finite derivations are
enumerated.

## 2. The noninjectivity predicate is `Sigma^0_2`

Assume the substituted generator tuple respects the finitely many relators of
`E`, so it defines `phi_e:E -> R_e` for every `e`.  Then

\[
\begin{aligned}
  \phi_e\text{ is not injective}
  &\Longleftrightarrow
  \exists w\;[w\ne_E1\ \wedge\ \phi_e(w)=_{R_e}1]\\
  &\Longleftrightarrow
  \exists w\,s\;[D_R(e,w,s)\ \wedge\
                 \forall t\;\neg D_E(w,t)].                    \tag{2}
\end{aligned}
\]

The last line has one existential block followed by one universal block over
a decidable matrix.  Hence

\[
  \{e:\phi_e\text{ is not injective}\}\in\Sigma^0_2.           \tag{3}
\]

Notice that this argument allows `E` to have undecidable word problem.  The
negative test `w != 1 in E` contributes exactly the universal block in (2).

## 3. The two compiler branches force noninjectivity exactly on `INF`

Suppose now that

\[
  e\in\mathrm{FIN}\Longrightarrow\phi_e\text{ is injective}.   \tag{4}
\]

Suppose also that

\[
  e\in\mathrm{INF}\Longrightarrow R_e\text{ is MF}.             \tag{5}
\]

MF passes to subgroups.  Since `E` is not MF, an injective `phi_e` into an MF
`R_e` is impossible.  Therefore (5) implies that `phi_e` is noninjective.
Together with (4), and the complementarity of `FIN` and `INF`, this gives

\[
  e\in\mathrm{INF}
  \quad\Longleftrightarrow\quad
  \phi_e\text{ is not injective}.                               \tag{6}
\]

Equations (3) and (6) would put `INF` in `Sigma^0_2`.

## 4. Why `INF` is not `Sigma^0_2` (diagonal proof)

For completeness, the strictness input can be proved directly.  Enumerate all
decidable ternary predicates `T_i(e,a,b)`.  Their `Sigma^0_2` sections are

\[
  A_i(e)\quad\Longleftrightarrow\quad
  \exists a\,\forall b\;T_i(e,a,b).
\]

Define

\[
  D(i)\quad\Longleftrightarrow\quad
  \forall a\,\exists b\;\neg T_i(i,a,b).
\]

Then `D` is `Pi^0_2`, and at the diagonal input `i`,

\[
  D(i)\Longleftrightarrow\neg A_i(i).
\]

Thus `D` is not any `Sigma^0_2` set.  Since the repository's prefix compiler
reduces every `Pi^0_2` predicate to `INF`, if `INF` were `Sigma^0_2`, its
computable preimage `D` would also be `Sigma^0_2`, a contradiction.

Combining this with (6) proves the firewall.

## 5. Exact theorem

### Uniform-seed-map firewall

Let `E` be a finitely presented non-MF group.  There do not simultaneously
exist:

1. a total computable map `e |-> R_e` to finite presentation codes;
2. a total computable tuple of words defining a homomorphism
   `phi_e:E -> R_e` for every `e`;
3. injectivity of `phi_e` for every `e in FIN`; and
4. MF-ness of `R_e` for every `e in INF`.

The proof is Sections 1--4.

The same theorem applies to any subgroup-hereditary property `P` in place of
MF whenever `P(E)` fails and the positive branch has `P`.

## 6. Consequences for proposed compiler architectures

### 6.1 A literal forbidden factor cannot persist through both branches

Any presentation template which includes the generators and relators of `E`
and sends those named generators to designated output words produces the
forbidden uniform map.  It cannot realize the requested truth table.

This rules out a direct finite-presentation analogue of

```text
output = E * machine-gadget,
```

followed by branch-dependent extra relations, if the displayed copy of `E`
remains a homomorphic image in every output.

### 6.2 The negative embedding must use a noncomputable branch witness

The recursive event-ray construction avoids the firewall correctly.  On a
finite event set, its isomorphism with the tail copy of `E` uses a last cut
`J`.  There is no computable choice of such a `J` on all indices, and no one
tuple of seed words defines the tail embedding on both branches.

Any finite-output compiler must retain this feature.  A Higman/rope
construction may output its finite presentation effectively, but the
embedding of `E` on `FIN` has to be obtained only after choosing the finite
branch witness.  The embedding must not be advertised as a uniform field of
the compiler.

### 6.3 Adian--Rabin does not lift the quantifier by itself

For a computable finite presentation and a computable word, word triviality is
`Sigma^0_1`.  The Adian--Rabin transform converts that one word test into a
property test; it does not turn the test into `INF`.  Feeding it a uniformly
displayed seed map would hit the firewall above.  A second-level result still
needs a mechanism packing an unbounded family of obligations into one finite
presentation.

## 7. The unrestricted hereditary-property slogan is false

Consider

\[
  P(G)\quad:\Longleftrightarrow\quad G=1.
\]

This property:

* passes to subgroups;
* holds of the positive group `1`; and
* fails for the finite presentation `<x | >` of `Z`.

But on finite presentations, `P` is recursively enumerable.  If

\[
  G=\langle x_1,\ldots,x_m\mid R\rangle,
\]

then `G=1` exactly when every one of the finitely many generators `x_i` has a
finite derivation from `R` to the identity.  Dovetail the finitely many
derivation searches.  They all terminate exactly for the trivial group.

Therefore the following statement is false:

> Every subgroup-hereditary property with one good group and one forbidden
> finitely presented group is `Pi^0_2`-hard on finite presentations.

The recursive-presentation switch theorem is valid because an infinite
relator stream carries the universal quantifier directly.  Moving to finite
presentations requires additional, property-specific permanence and packing
structure.

## 8. What remains as the honest MF target

The firewall does **not** disprove the desired MF theorem.  It narrows the
possible proof to one of two genuine constructions.

### Route A: branch-sensitive MF-Higman compiler

Construct a finite presentation effectively from the recursive event ray,
prove it MF when the ray has infinitely many cuts, and construct the seed
embedding only after choosing a last cut on `FIN`.

This route still needs a correct replacement for the false
`Transport.CompletionLemma`, an effective coded benign witness, and an MF
permanence proof for the final asymmetric rope layer.

### Route B: a different finite packing gadget

Build a finite presentation whose MF microstate condition enforces all rows of
the `Pi^0_2` predicate, while any failed tail produces a branch-dependent copy
of `E`.  The copy cannot be a uniformly designated seed homomorphism.

At present the repository contains neither route.  In particular, replacing
the literal `E` by an arbitrary finitely presented non-MF seed is a valid
**parameterization of the negative endpoint**, but it does not close the
finite-output compiler and does not prove the dichotomy

\[
  \exists\text{ fp non-MF group}
  \quad\Longrightarrow\quad
  MF_{fp}\text{ is }\Pi^0_2\text{-complete}.
\]

That implication remains exactly the substantive computer-science theorem to
be proved.

