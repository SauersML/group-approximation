---
rg: 2
id: leavitt-nonhyperlinear-from-internal-commutants
kind: route
title: Select a scalar commutant by bounded Poincare defects and contradict it using native internality
target: binary-leavitt-unit-group-is-not-hyperlinear
requires:
  - kazhdan-commutants-are-internal
  - elementary-groups-over-fg-rings-have-property-t
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/liu-leavitt-direct-internality-and-consequences-2026-09-20.md
  - research/artifacts/liu-leavitt-consequences-audit-2026-09-20.md
  - research/artifacts/leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md
  - research/artifacts/leavitt-regular-trace-cp-reversal-2026-09-08.md
---

## Attribution

The proposed analytic input is Jihao Liu,
[*Nonhyperlinear groups exist* (2026-09-20)](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 1.2/6.7. The Leavitt conclusion is a Cairn conditional application,
not a theorem claimed in Liu's paper. The native finite central-height and
generation arguments are the September 8 Cairn proof. The September 20
artifact gives a direct bounded-Poincare selection and expectation comparison
which bypass the earlier heat interface. It does not reprove or certify Liu's
upstream analytic theorem.

## Direct proof

Put R=L_(F_2)(1,2). Prefix coordinates and GL=EL identify H=R^x with
EL_4(R), its native rank-three subgroup L with H, and its fourth-coordinate
subgroup K with H. These are finitely generated Kazhdan groups. Infinite
simplicity of H gives ICC.

Suppose H is hyperlinear and take a regular-trace embedding pi in a
specified tracial matrix ultraproduct. Internality gives
C=pi(H)' cap M=[B_n]_omega. The property-(T) inequality on L2(M) is

```
||x-E_C(x)||_2^2 <= c^(-1) sum_s ||[pi(s),x]||_2^2.
```

Coordinate expectations onto B_n induce E_C. A sequence of contraction
witnesses shows the same inequality holds uniformly at the coordinates,
with an additive delta_n||x||op^2 and delta_n->_omega0. Internality also
makes the generators uniformly almost commute with U(B_n). Haar averaging
and polar completion perturb their lifts into B_n' with vanishing error;
the uniform inequality persists with vanishing additive error.

Decompose B_n into M_(a_i) tensor I_(b_i). Define each component's bounded
Poincare defect as the supremum over its operator unit ball of

```
||x-tr(x)I||_2^2 - c^(-1) sum_s ||[W_(n,i,s),x]||_2^2.
```

It is nonnegative, and these defects average to zero with physical weights
a_i b_i/d_n, by putting independently maximizing contractions into the
block-diagonal algebra. Full relation defects average with the same weights.
ICC conjugate averaging also makes each nonidentity word's squared trace
average tend to zero. Selecting a component whose combined bounded-gap,
growing-prefix relation and trace cost is at most the mean yields another
canonical H-model. The bounded Poincare inequality makes its full external
commutant scalar. This argument needs no heat time or SOS certificate.

Apply internality again to the selected model restricted to L. Write its
native commutant D=[A_n]_omega, E_n=E_(A_n), and
F_n=Ad(U_n)E_n Ad(U_n*), where U_n lifts the native compressor u.
The identity uLu^-1<=L gives D<=pi(u)Dpi(u)*. Hence F_n E_n-E_n tends
uniformly to zero in infinity-to-2 norm, by contraction witnesses.

The native k=diag(I_3,1+et) belongs to K and
y=uku^-1=x_12(e) belongs to L and is nonidentity. Its represented image
lies in pi(u)Dpi(u)* but is orthogonal to D, because it is a trace-zero
element of the canonical factor pi(L)''. Thus
`||E_n F_n-F_n||_(infinity->2) ->_omega1`.

The finite central-height lemma now produces z in Z(D) commuting with
pi(u), with zero trace and L2 norm at least 1/8. Since pi(K)<=D,
z commutes with pi(uKu^-1). The explicit native generation identity
H=<L,uKu^-1> puts z in the full global commutant, contradicting scalarity.

All bounded-witness, physical-weight, ICC trace and native algebra steps
are supplied in the cited direct proof. The only unresolved analytic
premise is internality; this route does not use Liu Proposition 3.1,
Theorem 7.4, general channel rounding, a factorial-embedding conjecture,
or finite presentation. Internality solely for canonical embeddings of
this same H would already suffice, since L is isomorphic to H.
