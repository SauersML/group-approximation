# Torsor CFI graphs, part 2: port profiles are cosets

Lane `ex-kac-quantum-compiler`, 2026-09-13.  Part 1 is
`research/artifacts/ex-kac-quantum-compiler-torsor-cfi-2026-09-13.md`
(definitions, Theorem D).  Nodes: `torsor-cfi-port-profiles-are-cosets` and
its `-proof` route.

## 1. Ports

Fix torsor CFI data `(H,[n],S)` with non-port relations `R_k`, `R'_k`
(`k in [m]`), and a set of port variables `P subseteq [n]`.  For `π in H^P`
adjoin one port context `k_i` for each `i in P`, with `S_(k_i) = {i}` and
relation `{π_i}`.  Write `G_H(R, π)` for the resulting torsor CFI graph.  Put

```text
X = G_H(R, π^0),      Y_σ = G_H(R', σ)      (σ in H^P),
N_t = { σ in H^P : X ≅_t Y_σ },                                   (TP1)
N''_t = { δ in H^P : G_H(R', e) ≅_t G_H(R', δ) },                  (TP2)
```

for `t in {q, qa, qc}` as in part 1, §1.

## 2. The theorem

**Theorem P.**  For each `t in {q, qa, qc}`:
- `N''_t` is a subgroup of `H^P`;
- `N_t` is empty or a right coset `N''_t σ_0`.

In particular `N_t` is closed under the Mal'tsev operation
`(σ, τ, ρ) |-> σ τ^(-1) ρ`.

**Lemma E (the quantum isomorphism groupoid).**  For colored digraphs and
`t in {q, qa, qc}`, `≅_t` is an equivalence relation.

*Proof.*
- **Reflexive.**  The identity matrix is a colour-preserving magic unitary
  over `C`.
- **Symmetric.**  `v_(xa) v_(x'a') = 0` implies `v_(x'a') v_(xa) = 0`, since
  it is the adjoint.  So `w_(ax) = v_(xa)` is a colour-preserving magic
  unitary `Y -> X` over the opposite algebra `A^op`.
  - A finite-dimensional representation of `A` gives one of `A^op` on the
    conjugate space.
  - A tracial state stays tracial on `A^op`.
  - `R^U` is anti-isomorphic to itself, through the transpose on `R` and
    ultrapowers.
- **Transitive.**  Let `V: X -> Y` over `A` and `W: Y -> Z` over `B`.  Put
  `U_(xz) = sum_y v_(xy) (x) w_(yz)` in `A (x) B`.
  - The summands are orthogonal projections.
  - Rows and columns sum to one.
  - `U_(xz) U_(x'z') = sum_(y,y') v_(xy) v_(x'y') (x) w_(yz) w_(y'z')`.  A
    surviving term needs `c_X(x,x') = c_Y(y,y') = c_Z(z,z')`.
  - So `A(Iso(X,Z)) -> A (x) B` unitally.  Tensor products of
    finite-dimensional representations, of tracial states, and of
    `R^U`-embeddable trace-preserving images (`R^U (x̄) R^U ⊂ (R (x̄) R)^U ≅ R^U`)
    stay in their class.  QED.

**Lemma T (twists).**  `A(Iso(Y_σ, Y_τ)) ≅ A(Iso(G_H(R',e), G_H(R',τσ^(-1))))`.

*Proof.*  By Theorem D both sides are coset constraint algebras on the same
contexts.
- A non-port context has `T_k = {g : g R'_k = R'_k} = Stab(R'_k)` on both
  sides.
- The port context `k_i` has `T = {g : g σ_i = τ_i} = {τ_i σ_i^(-1)}` on the
  left and `{τ_i σ_i^(-1) e^(-1)}` on the right.

The presentations coincide.  QED.

*Proof of Theorem P.*
- **Subgroup.**
  - `e in N''_t` by reflexivity.
  - If `δ, δ' in N''_t`, then `G_H(R',δ) ≅_t G_H(R',e) ≅_t G_H(R',δ')`.
  - By Lemma T, `G_H(R',e) ≅_t G_H(R', δ' δ^(-1))`, i.e. `δ'δ^(-1) in N''_t`.
- **Coset.**
  - If `σ, τ in N_t`, then `Y_σ ≅_t X ≅_t Y_τ`, so `τσ^(-1) in N''_t` by
    Lemma T.
  - If `σ in N_t` and `δ in N''_t`, then Lemma T gives `Y_σ ≅_t Y_(δσ)`, so
    `δσ in N_t`.
  - Hence `N_t = N''_t σ_0` for any `σ_0 in N_t`.
- **Mal'tsev.**  `(aσ_0)(bσ_0)^(-1)(cσ_0) = a b^(-1) c σ_0`.  QED.

**Corollary B (Boolean ports).**  Read port `i` as a bit through an involution
`t_i in H`, i.e. restrict to `E = prod_i {e, t_i} ≅ F_2^P`.  Then
`N_t ∩ E` is empty or a coset of the subgroup `N''_t ∩ E`, i.e. an affine
subspace of `F_2^P`.  Suppose a torsor CFI gadget is complete, at level `t`,
on the three sectors `(+,+)`, `(-,+)`, `(+,-)` of two ports.  Then it is
complete at level `t` on `(-,-)`.  Nor does the conclusion depend on the
level: the same holds separately for `q`, `qa` and `qc`.

## 3. What the theorem blocks

This is the isomorphism-syntax counterpart of
`central-character-profiles-affine-under-odd-tensor-products`.  There the
ternary operation is the tensor product of three group representations.  Here
it is composition in the quantum isomorphism groupoid, `Y_σ -> X -> Y_τ`,
together with the twist identity of Lemma T.

**Blocked.**  Any compiler that realizes each verifier predicate by a torsor
CFI gadget over some finite group, with scalar port sectors, and asks the
gadget to be complete atom by atom.
- The group may be nonabelian and the ports `H`-valued.
- The quantum level of completeness may be `q`, `qa` or `qc`.
- The realizable port relations are cosets of subgroups of `H^P`.
- With Boolean involution ports they are affine, so NAND and every other
  nonaffine predicate needs a forbidden sector.
- The `jnvwy-active-output-has-no-affine-safe-perfect-model` firewall applies
  unchanged to such gadgets.

**Not blocked.**
1. **Non-twist gadget families.**  Lemma T is the only place where torsor
   structure is used.  A gadget family `{Y_σ}` in general isomorphism syntax
   has the groupoid (Lemma E) but no twist identity.  Its profile is one
   equivalence class, with no ternary closure.  Association schemes that are
   not Schurian, and quantum Latin squares, are sources of such families.
2. **Non-scalar port sectors.**  As in the group case, a gadget whose ports
   are coupled to the rest of the instance, instead of being fixed scalars, is
   not covered.
3. **One-instance gaps.**  A single torsor CFI pair with a `qc`/`qa` gap is
   not excluded.  Via Theorem D it is exactly a *coset-safe* `H`-valued
   constraint system with a perfect trace and no `R^U` model: replace each
   allowed set by the smallest left coset of a subgroup containing the
   trace's local support.  This is the analogue of
   `locally-affine-support-bcs-is-exactly-the-lcs-boundary`.

**Classical shadow.**  Coset relations over `H` admit the Mal'tsev
polymorphism `x y^(-1) z`, so every relation pp-definable from them is again
a coset.  3SAT is not.  Theorem P is the quantum version, at the level of
port profiles: composing quantum isomorphisms plays the role of the
polymorphism.

## 4. Open question recorded

Is a `qc`/`qa` gap for a torsor CFI pair over a nonabelian `H` equivalent to a
finitely presented nonhyperlinear group?
- Over abelian `H` one expects the solution-group endpoint, as over `F_2`.
- Over nonabelian `H` the quantum symmetry is not a group dual
  (part 1, Corollary G).
- Coset relations over a nonabelian group are not affine, so they are not
  pp-definable from LIN, and Paddock--Slofstra Lemma 5.4 does not compile
  them to a linear system.
- No reduction in either direction is known here.
