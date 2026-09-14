# sk-strong-4 part 2: the boundary map

Where the manuscript's method stops, in each direction, with the owner of each statement. "PASS"
means a verifier lane passed it; everything else is unreviewed. Line references are to main's
`simple_kazhdan_sofic_group.tex` at rev1 (5b1890ce6c).

## 1. The action

| Question | Answer | Owner |
|---|---|---|
| When do clopen towers exist inside every open set? | Exactly when the action is topologically free | `clopen-towers-at-every-scale-iff-topologically-free` (this lane) |
| When is `EL_n(LC(X,F_2) ⋊ Γ)` simple, `n ≥ 3`? | Exactly when the action is minimal and topologically free; the centre is then trivial | `binary-el-simple-iff-minimal-topologically-free` (this lane) |
| Over `Z`, which subshifts? | Exactly the infinite minimal ones | `subshift-elementary-group-simple-iff-infinite-minimal` (sk-hypotheses-sharp) |
| When is the ring simple? | Minimal and effective, for Hausdorff ample groupoids | `steinberg-algebra-simple-iff-minimal-effective`, PASS |
| When does the group have finite models (LEF by the manuscript's route)? | When `X` has finite models; this forces `Γ` residually finite, and every f.g. infinite RF group admits such an `X` | sk-general-actions-a (e3d0976807) |
| Converse at the ring level | `EL_N` LEF iff the ring is LEF, `N ≥ 4` | `lef-el-groups-force-exactly-matricial-simple-ring`, PASS |

**Where the method stops.** The tower argument stops exactly at actions that are not topologically
free, by the first line; and it is not obstructed by points with nontrivial stabilizers as long as
the fixed sets have empty interior, which corrects the scope sentence of
`finite-model-subshift-elementary-groups-simple-kazhdan-lef`. The finite-model argument stops
exactly at acting groups that are not residually finite.

**Gap between the two.** Topological freeness is enough for simplicity and property (T) but not
for the manuscript's LEF proof. So for `Γ` residually finite the two boundaries coincide on the
Toeplitz family, and for `Γ` not residually finite the group is still simple and Kazhdan while its
approximation type is decided elsewhere (paradoxical side: no MF quotient, nonsofic).

## 2. Coefficients

| Question | Answer | Owner |
|---|---|---|
| Which coefficient rings keep finite generation and (T)? | Exactly the finite fields, with `X` a subshift over a finite alphabet | `crossed-product-el-kazhdan-iff-finite-field-and-subshift` (sk-hypotheses-sharp) |
| Does the theorem hold over every `F_q`? | Yes, modulo a finite centre, for `n ≥ 3` | sk-coefficients (5776c97bfc) |
| What is special about `F_2`? | `LC(X,F_2)^× = {1}`, so the centre is trivial and the scalar step is one line | this lane, Proposition 3 |
| Where does the binary proof break over `F_q`? | At the scalar step: a nonconstant unit `c` commutes with every `e_{ij}(e_V)`, so the roots `e_{ij}(e_V u_γ)` are needed | sk-referee-1 warning; this lane §3 |
| Finite coefficient rings that are not fields | A non-simple finite ring gives a proper noncentral congruence kernel; `M_d(F_q)` only reproduces a larger rank | sk-coefficients |

## 3. Ranks

| Question | Answer | Owner |
|---|---|---|
| Why `n ≥ 3`? | EJZ gives (T) from rank 3, and the tower group needs three distinct indices | manuscript |
| Is `n = 2` impossible? | No. `EL_2` is simple and Kazhdan whenever `X` has a finite cyclic factor. Sturmian `X` is open | sk-hypotheses-sharp; sk-el2 owns the open case |
| Rank in the LEF converse | Proved for `N ≥ 4`; rank 3 open | `lef-el-groups-force-exactly-matricial-simple-ring` |
| `EL` versus `GL` | `GL_n` has an infinite cyclic index quotient, so it is neither simple nor Kazhdan | `crossed-product-gl-n-has-infinite-cyclic-index-quotient` |
| Does raising the rank give new groups? | No: `EL_3(R_{X^{(k)}}) ≅ EL_{3k}(R_X)` for the tower system | `tower-subshift-elementary-group-is-el-3k-of-base` (sk-open-5) |

**Firewall.** Never write "`n = 2` loses (T)"; it is false for subshifts with a finite cyclic
factor.

## 4. Approximation types

| Question | Answer | Owner |
|---|---|---|
| LEF, sofic, hyperlinear | LEF implies sofic implies hyperlinear; the manuscript proves LEF | Pestov, Elek–Szabó |
| Sofic approximations into linear, affine or projective targets | They are automatically local embeddings, so they force LEF | `gap-sofic-approximations-are-local-embeddings` (sk-fp-sofic-a) |
| Paradoxical actions | No MF quotient, and `S_∂` is nonsofic | un-paradox, un-hyperlinear-paradox, PASS |
| Middle regime (neither matricial nor paradoxical) | Open; the `Z^2` aperiodic SFT case is the test object | sk-fp-sofic-b, un-m-converse |
| Finitely presented | A f.p. LEF group is residually finite, so no `G_X` is f.p.; the f.p. sofic question is open | Vershik–Gordon; sk-fp-sofic-a/-c/-d |

## 5. What this lane changes downstream
- `rf-toeplitz-subshifts-act-freely` is not needed for the simplicity half of the universal
  embedding: a dense free orbit gives topological freeness in one line, and Theorem T supplies one.
- Any general statement of the manuscript's theorem should read "minimal and topologically free",
  not "free". It is strictly more general at the same length, and by this lane's equivalence it is
  the exact hypothesis.
- `finite-model-subshift-elementary-groups-simple-kazhdan-lef` keeps freeness only in its LEF half.
