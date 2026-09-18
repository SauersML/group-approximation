---
rg: 2
id: leavitt-mf-survivor-yields-jacobson-regular-character-proof
kind: route
title: Diracize a nontrivial Leavitt MF character and pull its scalar-kernel indicator back through the Jacobson head
target: leavitt-mf-survivor-yields-jacobson-regular-character
requires:
  - torsion-normal-generator-mf-character-criterion
  - character-diracization-limit
  - full-leavitt-idempotent-defect-saturation
  - binary-jacobson-steinberg-cover-is-elementary
  - binary-jacobson-head-retaining-homomorphisms-are-faithful
---

Notation is as in the claim.

**Step 0: the map.**  `binary-jacobson-steinberg-cover-is-elementary`
gives `E=EL_5(J) ~= St_5(J)`.  The assignment `S->s_0`, `T->t_0` is a unital
ring map `J->R`, because `t_0s_0=1` in `R`.  So it induces
`St_5(J)->St_5(R)`, which we follow by the stabilization
`St_5(R)->St_20(R)`, `x_ij(a)->x_ij(a)`.  Call the composite `iota`.
Because `s_0t_0+s_1t_1=1` in `R`,

```text
iota(w) = x_13(1-s_0t_0) = x_13(s_1t_1) = z.                       (0)
```

This map is recorded in `property-t-free-leavitt-via-jacobson-head-root`.

**Step 1: a nontrivial MF character of `Delta`.**
* `z` is an involution: `x_13(q)^2=x_13(2q)=1`.
* `z` normally generates `Delta` (`full-leavitt-idempotent-defect-saturation`).
* `Delta` is finitely generated: `R` is a finitely generated ring and `n=20>=3`.

So if `Rad_MF(Delta)!=Delta`, `torsion-normal-generator-mf-character-criterion`
gives an MF character `chi` of `Delta` with `chi!=1`.  Here "character" means
a normalized central positive-definite function; extremality is not needed
below.

**Step 2: MF characters are closed under the operations used.**  Let
`V_k:Delta->U(d_k)` be operator-norm asymptotic with `tr V_k->chi` pointwise.
1. **Powers.**  `V_k^(tensor j) tensor conj(V_k)^(tensor j)` is again
   operator-norm asymptotic for fixed `j`, since tensor products of
   `eps`-multiplicative unitaries are `(2j eps)`-multiplicative.  Its
   normalized trace is `|tr V_k|^(2j)`.  So `|chi|^(2j)` is MF.
2. **Pointwise limits.**  Choose a diagonal sequence over an enumeration of
   the countable group.  Then a pointwise limit of MF characters is MF.
3. **Pullback.**  For any homomorphism `phi:H->Delta`, the maps `V_k o phi`
   are operator-norm asymptotic representations of `H`, with traces tending
   to `chi o phi`.  The defect of `V_k o phi` on `(g,h)` equals the defect
   of `V_k` on `(phi g, phi h)`.

**Step 3: Diracize.**  By `character-diracization-limit`:
* `K=K_chi={g in Delta : |chi(g)|=1}` is a normal subgroup of `Delta`;
* `|chi|^(2j) -> 1_K` pointwise as `j -> infinity`.

By Step 2 (1 and 2), `1_K` is an MF character of `Delta`.

**Step 4: the mark survives modulo `K`.**  Suppose `K=Delta`.  In the GNS
representation every `u_g` is the scalar `chi(g)1`
(`character-diracization-limit`, the identity
`||u_g-tau(g)1||_2^2=1-|tau(g)|^2`).  So `chi:Delta->T` is a homomorphism.
Now `Delta=St_20(R)` is perfect: `x_ij(a)=[x_ik(a),x_kj(1)]` for distinct
`i,j,k`.  Hence `chi=1`, contradicting Step 1.  So `K!=Delta`.  Because `z`
normally generates `Delta`, it follows that `z notin K`.

**Step 5: pull back.**  Let `theta:E->Delta/K` be `iota` followed by the
quotient map.  By (0), `theta(w)=zK!=1`.  So
`binary-jacobson-head-retaining-homomorphisms-are-faithful` (JHF3) makes
`theta` injective:

```text
M := iota^(-1)(K) = ker(theta) = 1.
```

Therefore `1_K o iota = 1_M = delta_e^E`.  This is an MF character of `E` by
Step 2 (3).  That proves (RP1), and (RP2) is its contrapositive.

The scalar kernel `K` may be nontrivial.  Nothing is claimed about the
centre of `Delta`, and no simplicity of `Delta` is used.  The finitary kernel
of `E` meets `iota^(-1)(K)` trivially because it is simple, self-centralizing
and contains `w`.  That is the whole content of (JHF3).

**Corollaries.**
1. **Dichotomy.**  Let `V_k` witness `delta_e^E`.  For `g!=1`,
   `||V_k(g)-1||_2^2 = 2-2 Re tr V_k(g) -> 2`, so the corona map is
   injective and `E` is MF.  Operator-norm asymptotic multiplicativity
   implies normalized-HS asymptotic multiplicativity, so the same `V_k` are
   hyperlinear microstates.
2. **Hyperlinearity lane.**  This is the contrapositive of the
   hyperlinear half of Corollary 1.
3. **(HC) ==> (H1).**  If `delta_e^E` were MF, Corollary 1 gives a corona
   embedding of `E`, so `w` is not in `Rad_MF(E)`.  This contradicts (HC).
4. **(H1) ==> regular hole for `EL_n(R)`, `n>=5`.**  The composite
   `E -> EL_5(R) -> EL_n(R)` sends `w` to `x_13(q)!=1`, so it is injective by
   (JHF3).  If `W_k` witnessed `delta_e^(EL_n(R))`, then `W_k` restricted
   along this embedding would witness `delta_e^E`.
