# Exact finite-normal augmentation-corner source audit

Date: 2026-08-30

## Question audited

The operator-norm argument in
`nonhyperlinear-normal-augmentation-corner-kills-mf` needs exactly:

```text
(A) a finite unital BCS star algebra B with no CE tracial state;
(G) a countable group G with a nontrivial finite normal subgroup K;
(M) a unital star map B -> q_K C[G] q_K,
    q_K=1-|K|^(-1) sum_(k in K) k.                         (AUG1)
```

The source and the compiler must not be conflated.  The source is already
unconditional and effectively named: `lin-explicit-fixed-bcs-gap-via-generic-conversion`
gives a finite `B_loop` with perfect commuting value and quantum value at
most `1-delta_loop`.  Thus `A(B_loop)` has a tracial state and has no CE
tracial state.  The older existential source
`mipstar-bcs-tracial-nonru-exists` would also work.

No established Cairn node or audited primary paper supplies `(G)--(M)` for
either source.

## The smallest authenticated corner

There is no benefit in taking a large finite subgroup.  Take

```text
K=<J> ~= C_2,     J central,     q_K=(1-J)/2.              (AUG2)
```

The augmentation complement is then the sole nontrivial irreducible type.
Consequently it cannot be omitted while some other nontrivial `K`-type is
retained.  This is the smallest exact map gate:

```text
A(B_loop) -> ((1-J)/2) C[G] ((1-J)/2),                    (AUG3)
```

with `J!=1`.  A solution of `(AUG3)` gives the entire subgroup
`<J><=Rad_MF(G)`, not only failure of a faithful model.

For a larger finite normal `K`, an atlas in a selected type
`z_rho C[G]z_rho` does **not** imply `(AUG1)`: its unit is `z_rho`, not
`q_K=sum_(rho!=1)z_rho`, and a corona representation may annihilate `z_rho`
while retaining a different nontrivial type.  Filling the complementary
types would require additional unital representations of the no-CE BCS and
is not formal.

## Existing route-by-route audit

| Route | What is unconditional | Exact failure at `(AUG1)` |
|---|---|---|
| Paddock--Slofstra / Lin fixed BCS | `B_loop` is finite, explicit, tracial and has no CE trace | It is a general nonlinear BCS algebra. No group or corner map is supplied. |
| LCS solution groups | For an LCS, `y_i |-> q_Jx_i` gives its algebra in the negative central-sign corner | A perfect commuting / finite-dimensional LCS gap is not known. `perfect-lcs-gap-implies-weak-non-mf` is conditional on exactly this missing object. |
| Slofstra wagon-wheel embedding | An already finitely presented marked group embeds in a solution group, preserving the central involution | It starts with group relators. It does not convert forbidden BCS spectral projections into group-ring identities; see `slofstra-solution-group-embedding-preserves-marked-involutions` and `wagon-wheel-stops-before-bcs-groupification`. |
| Signed-Hecke atlas | Exact local context PVMs exist in selected finite-group types; common type and rank balancing are solved | `signed-hecke-compatible-projection-atlas-for-nonce-bcs` is still open at cross-context marginal equality. Its selected `z_rho` is also not the authenticated unit `q_K`. |
| Fanizza et al. | The machine BCS has a fixed finite nonlinear predicate menu and exact signal semantics | `fanizza-native-signal-ultraproduct-groupification` remains open. The paper constructs BCS algebras, not an ordinary group with `(AUG3)`. |
| Culf--Mastel | A computable finite oracular 2-CSP family has perfect CE completeness and constant CE soundness | The predicates are general nonaffine relations; `culf-mastel-oracular-2csp-perfect-gap-family` supplies neither a central sign nor a group-corner map. |
| Bowen--Chapman--Vidick | Tailored games and subgroup tests produce perfect ZPC/IRS-side objects with a quantum gap | The output is an IRS/subgroup-test strategy, not a point-mass normal subgroup and not a unital algebra map into an ordinary group ring. |
| Manzoor / relation factors | A non-co-hyperlinear IRS and a non-CE relation algebra exist | The source explicitly stops before a nonhyperlinear discrete group; `primary-nonce-sources-miss-finite-index-core` finds no finite projective sector. |
| Lin / Mastel--Slofstra wrappers | A fixed synchronous separation converts unconditionally to `B_loop`; efficient BCS reductions preserve substantial structure | They stop at general BCS/3SAT syntax. `lin-ji-mastel-slofstra-stop-before-lcs` records the absent affine/group map. |

## 2025--2026 primary-paper delta

The current primary literature sharpens the boundary but does not cross it.

- Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao,
  [*The NPA hierarchy does not always attain the commuting operator value*](https://arxiv.org/html/2510.04943v4),
  constructs BCS algebras and a machine-indexed BCS family.  It does not
  construct an ordinary group-ring corner.
- Taller--Vidick,
  [*Approximating the quantum value of an LCS game is RE-hard*](https://arxiv.org/html/2507.22444v2),
  explicitly retains imperfect completeness.  Its introduction also states
  that a generic BCS-to-LCS algebra morphism is impossible; this rules out a
  black-box syntax conversion, not the source-specific map `(AUG3)`.
- Lin, [*MIPco = coRE*](https://arxiv.org/abs/2510.07162), supplies exact
  synchronous commuting completeness and a quantum gap before the BCS/LCS
  boundary.  The unconditional fixed-game BCS conversion is already recorded
  in Cairn, but no central-sign corner follows.
- Culf--Mastel,
  [*MIP-star-completeness of entangled constraint satisfaction problems*](https://arxiv.org/abs/2410.21223),
  gives perfect general-CSP data, not affine LCS or group-ring data.
- Bowen--Chapman,
  [*The Aldous--Lyons Conjecture I: Subgroup Tests*](https://arxiv.org/abs/2408.00110),
  and the BCV tailored-game work organize IRS/subgroup-test strategies.  No
  point-mass groupification or algebraic augmentation corner is asserted.
- Manzoor,
  [*There is an equivalence relation whose von Neumann algebra is not Connes embeddable*](https://arxiv.org/html/2502.06697v2),
  proves the relation/IRS analogue and notes the discrete-group promotion
  problem rather than solving it.

The July 2026 tilted-XOR and NPA papers found in the search change hardness
or hierarchy statements but do not supply perfect LCS completeness or
`(AUG3)`.

## Exact status and route to the property-T-free headline

The source and endgame are now established.  The one missing construction
for the first manuscript endpoint is `(AUG3)`, isolated as
`nonhyperlinear-bloop-central-sign-corner`.  Once it is proved,
`nonhyperlinear-normal-augmentation-corner-kills-mf` gives the explicit
nontrivial element

```text
1!=J in Rad_MF(G),                                        (AUG4)
```

using no Property `(T)`.  This settles endpoint 1 of
`property-t-free-manuscript-results`.  It does not settle that combined root:
the unrelated binary-Leavitt full-radical and torsion-free full-radical
obligations remain exactly
`property-t-free-leavitt-full-mf-radical` and
`property-t-free-torsion-free-full-mf-radical`.

This is also a rigor check on impact: completing `(AUG3)` is not a cosmetic
encoding lemma.  Its finite support subgroup is already non-MF, so the first
successful cross-context identity must itself carry the new obstruction.
Selected packets, finite Bass--Serre gluings, and a later ambient wrapper
cannot manufacture it after the fact.
