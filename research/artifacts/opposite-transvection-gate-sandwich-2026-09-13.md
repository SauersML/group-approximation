# The opposite-transvection gate: what sits below it, what sits above it, and what each answer gives

Lane `ex-nonore-relative-gate`, 2026-09-13.  Everything here is handwritten; nothing was run.
Supports `opposite-slice-contains-function-field-hecke-pair` and
`kt-double-hyperlinearity-requires-function-field-hecke-re`.  Status: the containments are proved
in those nodes' routes and are unreviewed.  Sections 3 and 4 are explanations, not theorems.

## 1. Objects

`k=F_q`, `r,d>=3`.  The inclusions of pairs are:

```text
Gamma_1=EL_r(k[t])      <  Lambda_1=EL_r(k[t^(+-1)])                    (one-place Hecke pair, t=x_1)
Gamma=EL_r(k[N^d])      <  E_pm=EL_r(k[Z^2 x N^(d-2)])                  (two-place Laurent pair)
Gamma                   <  P=E_pm rtimes SL_2(Z)=<Gamma,(1,I+E_12),(1,I+E_21)>   (the gate)
Gamma                   <  G=EL_r(k[Z^d]) rtimes SL_d(Z)                (Kun--Thom Theorem E)
```

For a pair `C<H` write:
- `X_H=H/C`;
- `D_H=H *_C H`;
- `W_H=(direct_sum_(X_H) Z/2) rtimes H`;
- `RE/C(C,H)` for scalar relative embeddability of `L(C)<=L(H)`.

## 2. The sandwich

Each pair above is contained in the next.  At each step:
- the smaller group lies in the larger one;
- intersecting the larger base with the smaller group gives the smaller base.

The one-place step uses `Lambda_1 intersect Gamma=Gamma_1`, proved by intersecting entries.  The
other steps are identities.  Amalgam normal forms and extending lamps by zero then give injective
homomorphisms

```text
D_(Lambda_1) -> D_(E_pm) -> D_P -> D_G,        W_(Lambda_1) -> W_(E_pm) -> W_P -> W_G,
```

and the coset actions restrict, orbit by orbit, down the chain.  Hence:

- **positive properties descend**: a sofic coset action, a sofic double, a hyperlinear double or
  wreath, and `RE/C`;
- **negative properties ascend**: a non-hyperlinear double and non-`RE/C`.  A nonsofic coset action
  ascends only in the weak sense that some orbit of a restriction is nonsofic.

What changes along the chain:

| pair | kernel-ring units | compressors of base | ambient (T) | finite images of base |
|---|---|---|---|---|
| Hecke `(Gamma_1,Lambda_1)` | `t^Z` | none (normalizer only) | yes | co-dense |
| two-place `(Gamma,E_pm)` | `x^(Z^2)` | none known in `E_pm` | yes | co-dense |
| gate `(Gamma,P)` | `x^(Z^2)` | free monoid `<A,B>_+` | **no** (`P->SL_2(Z)`) | normal, not co-dense |
| Kun--Thom `(Gamma,G)` | `x^(Z^d)` | all of `SL_d(Z) intersect M_d(N)` | yes | normal |

For every Ore slice the kernel ring has only the constant units, so no Hecke pair appears below it.
That is exactly why the Ore telescope proofs succeed without meeting a building action.

## 3. What each answer gives

**3a. The gate coset action `P action P/Gamma` is sofic.**
- It gives soficity of `W_P`, of the free wreath and of `D_P` (GKP 3.6, 3.7 and the
  coset-difference embedding), and it gives `RE/C(Gamma,P)`.
- Restricting down the chain, `E_pm action E_pm/Gamma` and the building action
  `Lambda_1 action Lambda_1/Gamma_1` are sofic.  Both pairs are co-dense Kazhdan, so every such model
  is noncorrectable to exact finite actions.
- Q3.4: nothing, since everything is sofic.  Kun--Thom pair: nothing, because restriction points the
  wrong way.

**3b. The gate coset action is nonsofic.**
- It gives a nonsofic coset action with a Kazhdan stabilizer and a non-Kazhdan ambient, compressed by
  a free monoid.  That would show the ambient (T) in Kun--Thom is not needed for action nonsoficity.
- It says nothing about `W_P` or `D_P` as groups.  Theorem A needs (T) for the ambient.
- `RE/C` remains undecided, so Q3.4 gets nothing from this alone.

**3c. `RE/C(Gamma,P)`, equivalently `D_P` or `W_P` hyperlinear.**
- It gives `RE/C(Gamma,E_pm)` and `RE/C(Gamma_1,Lambda_1)`.
- It is necessary for the Kun--Thom Q3.4 witnesses (`RE/C(Gamma,G)` implies it), but not
  sufficient.
- A Q3.4 witness built on `P` itself would also need a group nonsoficity theorem for `D_P` or `W_P`.
  No mechanism for that is known, because `P` has no (T).

**3d. Not `RE/C(Gamma,P)`.**
- `D_P` is non-hyperlinear, which settles `non-hyperlinear-group`.
- It makes `D_G` and `W_G` non-hyperlinear, so the Kun--Thom Q3.4 witnesses die at those parameters.

**3e. Hecke pair not `RE/C`.**  Every double in the chain is non-hyperlinear, with the same
consequences as 3d.  This is the cheapest negative target in the chain, and it is still of
non-hyperlinear-group strength.

**3f. Hecke pair `RE/C`, or its building action sofic.**  Nothing transfers up the chain.

## 4. Where the Kun--Thom normalization machinery stops

Kun--Thom Proposition 3.1 (verbatim record in `research/artifacts/kun-thom-2608-06222-verified.md`,
source pass 2026-08-15) needs expander decompositions for `sigma|_Gamma` and for `sigma`.  For the
gate, replace `G` by `P` and follow the argument.

- Let `s(y)` be the size of the `Gamma`-component of a point.  Strict compression makes
  `sigma(a^(-1))` map each `Gamma`-component into a union of `Gamma`-components, so
  `s o sigma(a^(-1)) <= s` off the model's error set.  The same holds for `b`.
- Each level set `{s<=tau}` is therefore approximately invariant under `Gamma`, `a` and `b`, hence
  under `P`, with error uniform in `tau`.
- Kazhdan subgroups make approximately invariant sets approximate unions of components.  Apply this
  to `E_pm`, `E_pm rtimes C_4` and `E_pm rtimes C_6`, using the Bass--Serre splitting
  `SL_2(Z)=C_4 *_(C_2) C_6` recorded in `farey-tree-lift-hits-opposite-steinberg-cycle`.  Each level
  set is approximately a union of `E_pm rtimes C_4`-components and of `E_pm rtimes C_6`-components.
- The remaining freedom lives on the finite component graph.  Its vertices are those components and
  its edges are `E_pm rtimes C_2`-components, so it approximates the Bass--Serre graph of `SL_2(Z)`.
  A "Hilbert hotel" is a nested family of `K_n -> infinity` sparse cuts in that graph, along which the
  component scale drifts.  It keeps every level set approximately invariant while making the
  compression non-surjective.
- For Kun--Thom's `G`, which has (T), components have uniform Cheeger constant and such cuts are
  excluded.  For a virtually free group they are not.  Take `Y=Z/L x V`, with `V` a random model of
  `F_2` and generators drifting one layer on a random half of `V`.  This is a sofic approximation of
  `F_2`.  If every component after deleting `eta|Y|` edges had Cheeger constant `h`, a component would
  span at most `O(1/h)` layers.  Counting drift then gives `eta>=h/8`.

So the Proposition 3.1 route does not force `D^(sigma(Gamma))` to be invariant for the gate.  This is
not a proof that the gate action is sofic, and not a proof that no other argument excludes Hilbert
hotels.

## 5. The two unsolved transfers

1. **Hecke to two-place.**  Does soficity (or `RE/C`) of the one-place pairs `EL_r(k[x^(+-v)])` over
   `EL_r(k[x^v])` give it for `(Gamma,E_pm)`?  The two-place pair has no locally finite building,
   and `Gamma` is not commensurated in `E_pm`: `k[N^d]/(x_1^2)` is infinite.
2. **Two-place to gate.**  `P/E_pm=SL_2(Z)` is not amenable.  Amenable-extension permanence, used for
   the cyclic steps of the Ore slices, does not apply.  Extending a sofic action along a free
   quotient is open even for the regular action, where it is the sofic-by-free problem.

## 6. Literature bound

I did not check the literature on soficity of S-arithmetic building actions in positive
characteristic beyond the repository's dyadic nodes (`dyadic-bruhat-tits-vertex-action-is-sofic`,
`sl3-dyadic-building-vertex-action-is-sofic`, both open).  GKP, as recorded in
`gkp-sofic-action-toolkit`, state that soficity of all actions of sofic groups was open when they
published.
