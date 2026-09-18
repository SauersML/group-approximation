---
rg: 2
id: binary-leavitt-atomic-morita-return
kind: claim
title: Return one binary Leavitt coefficient cell to the marked root spectral atom
distinct_from:
  opnorm-leavitt-coarse-fine-return-row: that asks for exact depth-one and depth-two matrix-unit packets with one identity and a vanishing support-leakage row; this asks instead for four corner coefficient operators satisfying only two diagonal inverse rows and one completeness row.
  affine-leavitt-prescribed-root-spectral-carrier-decoder: that is a normalized-Hilbert--Schmidt decoder for an odd-characteristic affine-Leavitt group and needs positive relative carrier mass; this is the operator-norm binary-Leavitt decoder and rank one is enough.
  corona-coefficient-module-decoder: that reconstructs a coherent unital action of the whole coefficient ring on one finitely generated projective corona module; this reconstructs one binary cell on one prescribed finite-coordinate atom and allows the coefficient window to vary with the coordinate.
artifacts:
  - research/binary-leavitt-atomic-return-via-three-row-compiler.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**OPEN.** Work in the fixed finite binary-Leavitt Steinberg presentation
of

```text
Delta=St_20(L_(F_2)(1,2))
```

with the distinguished involutive root

```text
z=x_13(q),                         q=s_1t_1.
```

For every sufficiently accurate operator-norm presentation model `U`, round
`z(U)` to an involution and prescribe its nontrivial spectral projection

```text
p_U=(1-z_round(U))/2.
```

Prove a dimension-independent modulus `eta(delta)->0` such that, whenever
`p_U!=0`, there are bounded operators

```text
s_0,s_1,t_0,t_1 in p_U M_d(C) p_U
```

satisfying

```text
||t_i s_i-p_U||_op <= eta(delta),              i=0,1,
||s_0t_0+s_1t_1-p_U||_op <= eta(delta).                (BLAMR)
```

The carrier is prescribed before the coefficient operators are chosen, so
the zero-carrier shortcut is unavailable.  No lower bound on its normalized
rank is requested, the off-diagonal rows are omitted, and different finite
coefficient windows may be used at different coordinates.

Establishing this claim and applying
`atomic-morita-return-kills-finite-order-mf-mark` kills `z`; the established
root-saturation calculation then gives total MF radical.

## Attempts

The direct typed-packet attack fails: `rectangular-escape`,
`literal-prefix-three-root-swap-retains-typed-carriers`, and
`typed-pi-superrank-data-do-not-decode-prescribed-leavitt-carrier` give exact
finite models of every separately typed packet while keeping the source and
target identities on different reservoirs.  A universal group-algebra
selector also fails by
`fixed-group-algebra-polynomials-cannot-supply-atomic-return`: on the regular
marked corner, arbitrary compressed root-word polynomials have total
three-row defect at least one.  Finally, the existing normalized-Hilbert--Schmidt
ledgers cannot be upgraded: a leakage row can have operator norm one on a
vanishing-rank carrier while its ambient normalized-HS norm tends to zero.

The live attack is `binary-leavitt-three-row-atomic-compiler`: derive the
three rows from finitely many prototype discrepancies at a
coordinate-dependent, losslessly conjugated address.

The authenticated support-idempotent returns do not by themselves furnish
such prototypes.  `support-return-odd-loops-do-not-imply-atomic-return`
retains both literal odd native factorizations, their transported Pauli-chart
covariances, chart intersection and native braid in one exact finite marked
model.  Applying the atomic gap on its nonzero marked atom proves that no
three-row output with a vanishing modulus follows from that finite menu.  A
live compiler must add a relation coupling coefficient completeness to the
prescribed atom, rather than only recombine `Z_i,H_i,W_i,J_i`.

Nor can that new occurrence remain in the balanced-prefix coefficient core.
By `degree-zero-leavitt-core-has-locally-finite-marked-models`, every fixed
finite inventory in gauge degree zero lies in a finite matrix ring over
`F_2`, so its elementary-word table has an exact finite model with the marked
root surviving.  Thus the next viable atomic-return row must expose nonzero
Leavitt gauge degree on the prescribed atom (an uncancelled `s_i`, `t_i`, or
unequal-length prefix coefficient), or use genuinely unbounded adaptive
depth.  Noncommuting balanced matrix units alone do not cross the finite-model
firewall.

The natural analytic bypass, replacing the Kazhdan projection in the
manuscript transport argument by finite-window averages over the locally
finite coefficient root subgroup `X_12(R_0)`, is vacuous.
`window-average-kazhdan-substitute-forces-trivial-corona-rep` proves that the
window averaging projections in the adjoint corona are norm-Cauchy precisely
when the corona representation is trivial.  Equal window commutants give
equal bicommutants, so the root image is finite along every ultrafilter.  A
finite-index coefficient kernel generates the unit ideal, so the normal
closure is all of `Delta`.  The approach dies at the existence of the norm
limit: in any surviving representation the window projections never
stabilize, and only level-shifted orders `U^*P_(k')U<=P_k` remain, which
stable finiteness does not force to equality.  A Property-`(T)`-free proof
cannot import the transport/stable-finiteness step through a window-limit
projection.  It must produce a same-class inequality by some other means.

2026-09-17 (swarm-0917-w5-pt-morita, reframing).  The same-class inequality
asked for above can come from a single projection instead of a window
limit.  `kesten-spectral-gap-replaces-kazhdan-projection-per-model` shows
that the manuscript transport and normal-subgroup theorems consume
property `(T)` only through one per-model hypothesis `(MSG)`: `1` is not an
accumulation point of `sp(rho(h_S))` for one Markov element `h_S` of the
subgroup.  Under `(MSG)`, `chi_{1}(rho(h_S))` is the fixed-vector
projection, it is a norm limit of group-algebra elements with coefficient
sum near one, and it satisfies `U^*PU<=P`.  Stable finiteness then forces
equality, with no Kazhdan hypothesis.  For `delta_e`-profile models, the
subgroup algebra in the adjoint corona always surjects onto
`C + C*_r(L)`, and the Kesten element supplies a positive `e` with
`omega(e)=1` and `tau(e)=0`.  The Kazhdan-projection shape is therefore
available without `(T)`, and only isolation of `1` is missing.

The prerequisite can fail.  A free-group model with a vanishing-rank
rotation block through `F_2->Z` has `sp=[-3/5,1]` in both the norm corona
and the adjoint corona.  So `(MSG)` does not follow from nonamenability,
the `delta_e` profile, coordinatewise exactness, or stable finiteness.  In
that model the failure is carried by an amenable quotient on a
vanishing-rank block.  A T-free proof of `(MSG)` for a subgroup of
`EL_20(L_(F_2)(1,2))` must therefore use that the model extends to the
simple group.  This does not prove `(BLAMR)`, and the claim stays OPEN.
The live bypass is now `(MSG)` for the root subgroups the manuscript
compresses, or injectivity of the adjoint splitting map, in every
`delta_e`-profile model.

2026-09-17 (swarm-0917-w6-w6-ptl-last2, quantifier-shift).  The finite
von Neumann rung of the `(MSG)` quantifier ladder is now decided by
`tracial-model-spectral-gap-is-character-gap-weaker-than-t`.  Along every
finite von Neumann target, `(MSG)` on `L` is equivalent to a uniform gap
for `h_S` over the GNS representations of characters of the ambient group.

This rung is strictly weaker than `(T)`:
- `(V,V)` and `(V,F_2)` satisfy it by the Dudko--Medynets character
  classification and Kesten, although every Kazhdan subgroup of `V` is
  finite;
- it depends on the ambient group, since `(F_2,F_2)` fails it.

So ambient data can replace `(T)`, but only through characters.  For this
claim that is useless.  In the adjoint corona of every `delta_e`-profile
model, the tracial completion sees `lambda_G`, where the gap is automatic.
Whenever `(MSG)` holds, the substitute eigenprojection is `tau`-null.

The approach "prove `(MSG)` for the compressed root subgroup from a
T-free tracial or character property of `Delta`" therefore dies at the
step `pi_tau(P)=0`.  Such a property includes character rigidity of
`Delta`, and it includes `Thompson V<=Delta` with its character
classification.  That approach proves nothing about the projection that
`(BLAMR)` and the transport consume.

What survives has to control tau-null spectrum of one Markov element in
the norm corona.  The next undecided rung is stably finite C-star targets,
which contain the coronas.  The claim stays OPEN.

2026-09-17 (d-ptf-morita, transplanter, entropy-measure).  This attempt
transplanted 1-bounded entropy and regularity invariants of `L(L)` as a
replacement for property `(T)` of the compressed subgroup.  It dies at the
subgroup-intrinsic step.  `z-direct-factor-kills-intrinsic-t-substitutes`
takes the involutive cyclic compression group `G_0` of
`finite-order-central-compression-defect-survives-mf`, forms `G_0 x K` for
an arbitrary countable MF group `K`, and uses the tensor model.  For the
compressed subgroup `L=Z x K`, the defect `[uc'u^-1,l]` tends to `-I` in
operator norm and in normalized Hilbert--Schmidt norm, and the Kazhdan
normal subgroup `{1,d'}` of `D_G(L)` survives in an MF group.  So both
conclusions of the compression criterion fail for `L=Z x F_2` (nonamenable,
Haagerup, exact, RF) and for `L=Z x SL_3(Z)` (infinite normal Kazhdan
subgroup, relative `(T)`).  They also fail for every `L` with `h(L(L))<=0`
coming from a central diffuse `L(Z)`; that case is cited from Hayes and is
not verified in-graph.

The resulting invariant: any subgroup-intrinsic substitute for `(T)` must
fail for every `Z x K`.  Such a substitute must be of ICC,
trivial-amenable-radical, or non-inner-amenable type, or of the kind that
`(T)` itself satisfies.  Otherwise the proof must use ambient data, such as
simplicity of `EL_20` or Leavitt coefficients, which forbid the tensor
splitting.  This does not prove `(BLAMR)`, and the claim stays OPEN.
