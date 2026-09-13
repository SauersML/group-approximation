---
rg: 2
id: fibre-commutative-quantum-isomorphisms-are-coset-systems
kind: claim
title: Quantum isomorphisms of colored digraphs whose fibre blocks commute are exactly coset systems over the fibre automorphism groups, so a square completion leaves coset syntax only through a fibre with quantum symmetry
distinct_from:
  coset-systems-are-torsor-isomorphism-games: that proves coset systems are isomorphism games between torsor digraphs; this proves the converse for arbitrary fibre configurations, with fibre-commutativity as the only hypothesis, and recovers that dictionary when the fibres are Cayley configurations.
  port-generated-square-completions-force-coset-support: that derives regular groups for Latin completions inside the port algebra; this treats completions with arbitrary padding rows and non-regular fibres, and derives the automorphism groups of the fibres, with padding given by the orbit map of a port.
  closure-safe-support-is-exactly-the-colored-iso-rung: that says which bisynchronous gaps are colored isomorphism gaps; this says which colored isomorphism gaps are coset-system gaps.
---

**ESTABLISHED** by `fibre-commutative-quantum-isomorphisms-are-coset-systems-proof`.
Not reviewed by an ex-verify lane.

**Setting.**
- `X, Y` are colored digraphs and `A(Iso(X,Y))` is their isomorphism algebra,
  with magic unitary `v = (v_(xa))`, as in
  `closure-safe-support-is-exactly-the-colored-iso-rung`.
- The *fibre* `F_q^X` is the set of vertices of diagonal colour `q`, and
  `W_q^X` is the colored digraph `X` restricted to it.  Likewise on `Y`.
- The *fibre block* of `q` is `(v_(xa))_(x in F_q^X, a in F_q^Y)`.
- `A^fc(X,Y)` is the quotient of `A(Iso(X,Y))` by all commutators of entries
  of a common fibre block.
- `K_q = Aut(W_q^X)`, acting on `F_q^X`.

**Theorem.**
- **(F1) Degenerate cases.**  If some `W_q^X` and `W_q^Y` are not isomorphic,
  then `A^fc(X,Y) = 0`.  Otherwise fix isomorphisms
  `φ_q : W_q^X -> W_q^Y`, and for `q != q'` put

  ```text
  R_(qq') = {(k,l) in K_q x K_(q') : c_Y(φ_q k x, φ_(q') l x') = c_X(x,x') for all x in F_q^X, x' in F_(q')^X}.
  ```

  Each `R_(qq')` is empty or a left coset `c_(qq') D_(qq')` of
  `D_(qq') = {(k,l) : c_X(kx, lx') = c_X(x,x') for all x, x'}`.  If one is
  empty, `A^fc(X,Y) = 0`.
- **(F2) Dictionary.**  Otherwise `A^fc(X,Y) ≅ A(S)`.
  - Here `S` is the coset system with fibres `K_q`, all pairs as edges, and
    relation sets `R_(qq')`, as in
    `coset-systems-are-torsor-isomorphism-games`.
  - The isomorphism is `v_(xa) |-> sum_(k : φ_q k x = a) p_q^k`.
- **(F3) Fibres with no quantum symmetry.**  Suppose every
  `A(Iso(W_q^X, W_q^Y))` is commutative.  For example, `W_q^X ≅ W_q^Y` and
  `O(Qut W_q^X)` is commutative.  Then `A(Iso(X,Y)) = A^fc(X,Y) ≅ A(S)`, so:
  - `X ≅_qc Y` iff `S` is tracial;
  - `X ≅_qa Y` iff `S` is `R^U`.
- **(F4) Trace level.**  Let `tau` be a tracial state on `A(Iso(X,Y))` whose
  GNS representation makes every fibre block commutative.  Then `tau`
  factors through `A(S)`.
- **(F5) Ports.**  For a port vertex `x_q in F_q^X`, the port PVM
  `v_(x_q, ·)` is the pushforward of `p_q` under the orbit map
  `beta_q(k) = φ_q k x_q`.  So a square completion of a synchronous game
  that is fibre-commutative on its perfect trace is a coset refinement with
  padding `beta_q`, in the sense of
  `coset-refinement-forces-rectangular-central-splitting`.

**Consequences.**
1. **Rigid completions.**  Take any completion whose fibre configurations have
   no quantum symmetry, however far from regular they are.  Then:
   - (RCS) applies;
   - so does `forbidden-pair-splits-are-central-rectangle-splittings`;
   - so do `exact-label-coset-refinements-are-affine` and
     `hidden-labels-import-cross-context-commutation`;
   - so does `relabelable-coset-systems-are-solution-group-corners`, for
     relabelable `S`.
2. **The exit from coset syntax.**  A colored qc/qa gap outside coset syntax
   needs a perfect trace with a noncommuting fibre block.  That in turn needs
   `A(Iso(W_q^X, W_q^Y))` to be noncommutative for some `q`.
   - If `W_q^X ≅ W_q^Y`, this means the fibre configuration has quantum
     symmetry.
   - Otherwise `A(Iso(W_q^X, W_q^Y))` is nonzero with no character, so the
     two copies of the fibre are quantum isomorphic but not isomorphic.
   - The port row `v_(x_q, ·)` is a PVM, so the noncommutation lies between
     distinct rows of one fibre, i.e. between padding rows.
3. **Completions whose fibres are not torsors.**  Fibres that are not torsors
   do not by themselves leave coset syntax: nonregular action, orbit-map
   padding and nonrectangular port supports are all inside it.  What leaves
   it is quantum symmetry inside a fibre.

**Model tests.**
- **Torsor digraphs.**  `X(S_1)` and `X(S)` have Cayley configurations with
  colours `x^(-1) x'`.
  - `K_q` is `K_q` acting by left translation.
  - Every row of a fibre block equals a translate of the row at `e`, so the
    block commutes.
  - `R_(qq') = c_(qq') D_(qq')`, and (F2) is (T1) of
    `coset-systems-are-torsor-isomorphism-games`, with `p_q^(a x^(-1))`.
- **The `S_3` orbital example** of
  `port-generated-square-completions-force-coset-support`.
  - The fibres are the points and the 2-subsets of `{0,1,2}`, each an
    uncoloured triangle with `K = S_3`.  `S_3^+ = S_3`, so the fibres are
    rigid.
  - `D` is the diagonal copy of `S_3`, the algebra is `C^6`, and the port
    support, the incidence relation, is the image of `D` under
    `beta(g) = (g(0), g({0,1}))`.
  - It is a padded coset refinement, as (F5) says.
- **The hypothesis is needed.**  Take `X = Y` a single uncoloured `K_4`.
  - `A(Iso(X,X)) = O(S_4^+)` is noncommutative (Wang).
  - `A^fc = C(S_4)` is a strict quotient, so (F3) fails without rigidity.
