# Quantum symmetry rung between MIP* = RE and nonhyperlinear groups

Lane `ex-nh-mipstar`, 2026-09-12.  The mathematics lands as Cairn nodes.  This
note carries the separation analysis, the context of the new nodes and the
literature record.

## 1. What separates a non-CE algebra from a nonhyperlinear group

For a finite synchronous game `G` with game algebra `A(G)` there are four
satisfiability levels.  Brannan--Chirvasitu--Eifler--Harris--Paulsen--Su--
Wasilewski (BCEHPSW), arXiv:1812.11474v2, Theorem 2.1 and Definition 2.2,
give the dictionary (read at source):

| level       | algebraic condition                                          | perfect strategy |
|-------------|--------------------------------------------------------------|------------------|
| algebraic   | `A(G) != 0`                                                  | `A^*`            |
| C*          | a unital *-homomorphism into some `B(H)`, `H != 0`           | `C^*`            |
| tracial     | a unital *-homomorphism into a C*-algebra with faithful trace | `qc`             |
| approximate | a unital *-homomorphism into `R^U`                           | `qa`             |

The levels behave differently on three syntaxes.

1. **General synchronous or BCS games.**  All four levels differ.
   - Algebraic but not C*: `A(Hom(K_5,K_4))` (Helton--Meyer--Paulsen--Satriano,
     quoted in BCEHPSW Remark 4.10).
   - C* but not tracial: Paddock--Slofstra, arXiv:2310.07901v2, Section 4.
   - Tracial but not approximate: `MIP*=RE`, via Paddock--Slofstra Example 4.2
     (`mipstar-bcs-tracial-nonru-exists`).
2. **Linear systems, i.e. solution groups.**  Algebraic, C* and tracial
   coincide (Cleve--Liu--Slofstra, as stated on p. 4 of Paddock--Slofstra).
   Tracial versus approximate is equivalent to a finitely presented
   nonhyperlinear group (Paddock--Slofstra Proposition 5.8,
   `lcs-tracial-ru-gap-equiv-nonhyperlinear`).
3. **Graph isomorphism games, i.e. quantum automorphism groups.**  Algebraic,
   C* and tracial coincide (BCEHPSW Theorem 4.9).  Tracial versus approximate
   is open: `qc-isomorphic-not-qa-isomorphic-graph-pair-exists`.

In syntaxes 2 and 3 the collapse has one cause.  A nonzero algebra carries an
ergodic symmetry with a unique invariant state, and that state is a trace.

- **Solution groups.**  `C[Gamma]` carries the coaction `g |-> g (x) g`.  An
  invariant state satisfies `tau(g) g = tau(g) 1`, so `tau(g)=0` for `g != e`.
  The invariant state is the regular trace, and on the corner `(1-J)/2` it
  gives the tracial state of the linear system.
- **Isomorphism algebras.**  A nonzero `A(Iso(X,Y))` is an
  `O(G_Y)`-`O(G_X)` bigalois extension (BCEHPSW Theorem 4.5).  A bi-invariant
  state on a bigalois extension is unique and faithful (Theorem 3.15(1)), it
  exists whenever the algebra is nonzero, and it is tracial for classical
  graphs (Theorem 4.7).

**The separation, pinned.**  `MIP*=RE` produces a tracial state that exists
but that no symmetry selects.  A nonhyperlinear group needs the invariant
trace itself to fail Connes embeddability, and so does a non-Connes-
embeddable quantum automorphism group.  This is the trace-selection gap of
`mipstar-equals-re` restated as a symmetry requirement.  For LIN,
Paddock--Slofstra (p. 4) state the algebraic half of the point: the collapse
of the first three levels for linear systems, "combined with the existence of
constraint systems which are algebraically satisfiable but not tracially
satisfiable, implies that it is not possible to embed every BCS algebra in
the BCS algebra of a linear system game.  This is an obstacle for one method
of constructing a non-hyperlinear group that tends to come up when discussing
potential consequences of MIP*=RE."

Between the algebra and the group sits the isomorphism rung.  It has the
invariant trace, like groups.  Its local syntax is not affine, and the
quantum symmetry is not a group.

## 2. The rung theorem

Node: `qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group`, with the
complete proof in `qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group-proof`.

Mechanism, in one paragraph.  Put the two graphs side by side, `Z = X ⊔ Y`,
after replacing both by complements if `X` is disconnected.  The magic
unitary of `Qut(Z)` intertwines the same-component matrix `J_X (+) J_Y`,
because intertwining pairs are closed under entrywise products.  So the mass
that row `x in X` sends into `Y` is one central projection `P`.  The block
`(u_(xa))_(x in X, a in Y)` is a quantum isomorphism `X -> Y` in the corner
`P O(Qut Z)`.  `P` is nonzero because `[[0,V],[V^t,0]]` is a quantum
automorphism of `Z` for any quantum isomorphism `V`.  Haar invariance alone
forces `h(P)=1/2`.  So twice the Haar trace, restricted to the corner, is a
tracial state on `A(Iso(X,Y))`.  If `L^infinity(Qut Z)` embedded in `R^U`,
this state would give a perfect `qa`-strategy.

Two features worth recording.

- No faithfulness of `h`, no coamenability and no residual finite-
  dimensionality are used.  Invariance fixes the corner trace.
- The corner argument is syntax-independent.  It only needs a Kac compact
  quantum group whose fundamental matrix intertwines a "same part" relation.
  It therefore applies to finite edge-coloured graphs if that relation is
  added as a colour.  That variant is not landed as a node, because Kac
  traciality for coloured structures is not cited from a source here.

## 3. The goal implies the rung

For a binary linear system `Ax=b`, BCEHPSW Theorem 5.6 proves that
`syncBCS(A,b)`, `Iso(G_(A,b),G_(A,0))` and `Hom(K_m, complement(G_(A,b)))` are
hereditarily *-equivalent.  Their Proposition 5.3 then transfers perfect
`t`-strategies for `t in {loc, q, qa, qc, C^*}`.  Hence:

```text
finitely presented nonhyperlinear group
  => (Paddock--Slofstra Prop. 5.8) a tracial, non-R^U linear system Ax=b
  => (BCEHPSW Thm 5.6, Prop. 5.3) G_(A,b) ≅_qc G_(A,0), but not ≅_qa
  => (rung theorem) a finite graph Z with L^infinity(Qut Z) not Connes embeddable.
```

The middle arrow needs the identification of the synchronous algebra of
`syncBCS(A,b)` with the BCS algebra.  Kim--Paulsen--Schafhauser and Goldberg
proved it for linear systems, per Paddock--Slofstra p. 2.  For CFI-type pairs
`(G_(A,b), G_(A,0))` the `qc`/`qa` gap is therefore equivalent to the linear
system gap, hence to the goal.  For general graph pairs no converse is known.

**Colored CFI pairs are the group case exactly.**  Roberson--Schmidt,
arXiv:2111.12362v1, read at source, prove two identifications.

- Theorem 3.8: `C(Qut(G(M,b))) ≅ C^*(Gamma_0(M))` as compact quantum groups.
- Theorem 6.7: `Iso(G(M,b), G(M,b')) ≅ A(M, b+b') = p C^*(Gamma(M,b+b'))`,
  with `p = (1-gamma)/2`.

So on colored CFI pairs the rung is literally the solution-group endpoint.
The linking algebra is the linear-system algebra, and the quantum symmetries
are group duals (`colored-cfi-rung-is-the-solution-group-case`).  The rung can
go strictly beyond groups only on colored digraphs whose quantum automorphism
groups are not group duals.  Examples of such quantum symmetry:
- `S_N^+` and `H_N^(s+)` themselves, which are Connes embeddable;
- quantum Latin squares and Hadamard or association-scheme constructions,
  whose quantum isomorphisms are finite-dimensional.

## 4. Consequences

**Computability.**  `A(Iso(X,Y))=0` is recursively enumerable: search for a
derivation of `1` in the defining ideal.  So `qc`-isomorphism is coRE.
Suppose every finite graph had a Connes-embeddable quantum automorphism group.
Then the rung theorem makes `qa`-isomorphism equal to `qc`-isomorphism, so it
would be coRE as well.  Therefore any computable family `M |-> (X_M, Y_M)`
with

```text
M halts        =>  X_M ≅_q Y_M,
M does not halt =>  X_M not ≅_qa Y_M
```

yields a pair as in the rung theorem.  One pair can be named: let `M_*` be the
fixed point that searches for a derivation of `1=0` in its own
`A(Iso(X_(M_*),Y_(M_*)))` and halts when it finds one.  This is the
perfect-completeness requirement of `perfect-completeness-constant-soundness-lcs-compiler`
again, but in isomorphism syntax.  There the local checks may carry
nonabelian symmetry rather than affine parity.

**The monomial compiler region.**  `normal-phase-safe-toric-games-have-qa-one`
refuted `monomial-gap-phase-safe-toric-groupification` and
`phase-safe-toric-gap-game-exists`.  So the only consumer route of
`bisynchronous-to-monomial-game-algebra-compiler` targets a refuted claim.
The compiler still has a correct payoff, at the quantum-group level:
a finite-phase monomial linking algebra with a `qc`/`qa` gap would give a
non-Connes-embeddable Kac quantum group by the coloured corner argument of §2.

## 5. Where attempts at a graph pair die

1. **CFI pairs from linear systems.**  By §3 these are exactly as hard as a
   finitely presented nonhyperlinear group.
2. **Uniform gadget reductions from NP-hard constraint languages.**  A
   hereditary *-equivalence preserves perfect classical strategies
   (BCEHPSW Proposition 5.3 with `t = loc`).  A polynomial-time family of such
   equivalences from 3SAT-type systems to isomorphism games would reduce 3SAT
   to graph isomorphism.  Babai's quasipolynomial algorithm (arXiv:1512.03547,
   not re-read here) would then put NP in quasipolynomial time.  This blocks
   only uniform, classical-solution-preserving gadgets.  It says nothing about
   a single instance, or about compilers that do not preserve classical
   solutions (the `MIP*=RE` compilers do not).
3. **Algebra-level equivalence with a fixed source.**  A hereditary
   *-equivalence with an isomorphism game transfers the collapse of the first
   three levels.  A source whose own levels differ (Paddock--Slofstra
   Section 4, Helton--Meyer--Paulsen--Satriano) cannot be equivalent to any
   isomorphism game.  The `MIP*=RE` separating algebra is not excluded by this.
4. **Symmetric hosts.**  A unital *-homomorphism from the fixed non-`R^U`
   algebra `A(B_*)` into a corner `P O(G) P` of a Kac compact quantum group,
   with `h(P)>0`, makes `L^infinity(G)` non-Connes-embeddable.  This is the
   quantum form of `non-ru-bcs-is-satisfiable-in-a-group-factor`.  Hosts with
   Connes-embeddable Haar state are excluded, among them:
   - `S_N^+` and `H_N^(s+)`: residually finite-dimensional
     (Brannan--Chirvasitu--Freslon, Adv. Math. 363 (2020)), hence CEP
     (Bhattacharya--Brannan--Chirvasitu--Wang), both as stated in Theorems 1.6
     and 1.7 of Freslon's notes;
   - Kac free wreath products over amenable amalgams of hyperlinear duals
     (`generalized-free-wreath-hyperlinearity-permanence`).

5. **Support closure versus squareness.**
   `closure-safe-support-is-exactly-the-colored-iso-rung` gives the exact
   boundary for colored digraphs.  A bisynchronous game with a perfect trace
   and no `R^U` model feeds the rung iff every linked component of its pair
   support is allowed.  That condition plays the role of affine safety for
   linear systems.
   - Independent-set games pass it for free, since their rule sees only
     whether the two questions are equal.
   - They fail squareness instead: a perfect strategy is a quantum injection
     `[t] -> V`, and the rung needs a quantum bijection.
   - Classically this is where independent set (NP-complete) and graph
     isomorphism (quasipolynomial) part ways.
   - Completing the qc injection to a bijection is the open step for the
     independent-set sources of
     `perfect-qc-separation-yields-finite-bcs-with-no-matrix-model`.

## 6. Literature check (bounded)

- **Read at source.**
  - BCEHPSW arXiv:1812.11474v2: pp. 1--7 and 17--33.
  - Paddock--Slofstra arXiv:2310.07901v2: pp. 1--12.
  - A. Freslon, *Matricial approximation of quantum automorphism groups of
    graphs* (survey notes, 8 pp.).
- **Abstracts only.**
  - Lupini--Mančinska--Roberson arXiv:1712.01820.
  - Kar--Roberson--Seppelt--Zeman arXiv:2407.10635.
  - Voigt arXiv:2603.25141.
- **Web searches on 2026-09-12:**
  - qc-isomorphic but not qa-isomorphic graphs and MIP*=RE;
  - Connes embedding for quantum automorphism groups of graphs;
  - non-Connes-embeddable Kac compact quantum groups;
  - open questions on quantum approximate isomorphism;
  - hyperlinear discrete quantum groups and counterexamples.
- **Not found:** any non-Connes-embeddable Kac compact quantum group, any
  `qc`-but-not-`qa` isomorphic graph pair, or the rung theorem.  The check is
  bounded to these searches and is not a survey of the quantum-group
  literature.

## 7. Sharpest next targets

- `qc-isomorphic-not-qa-isomorphic-graph-pair-exists` via a computable
  isomorphism-syntax compiler with perfect completeness (§4).  Its local
  checks may use nonabelian symmetry, which the affine-LIN barrier of
  `lcs-compiler-target-is-goal-equivalent` does not see.
- A converse for special graph classes: when does a `qc`/`qa` gap for a pair
  force a linear-system gap?  If quantum isomorphisms of a class always come
  from solution-group representations, the rung collapses onto the goal for
  that class.
