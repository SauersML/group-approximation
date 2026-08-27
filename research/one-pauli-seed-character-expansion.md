---
rg: 2
id: one-pauli-seed-character-expansion
kind: claim
title: One Pauli seed plus expanding character covariance forces dimension or mark collapse
distinct_from:
  full-weyl-defect-equals-pvm-transport-energy: that uses the complete mixed Weyl table to translate every character; this needs only one anticommuting seed and bounded actor covariance.
  dimension-expander-two-matching-square-function: that propagates alternating X/Z matrix bridges; this propagates the scalar ranks of one X-spectral PVM.
---

ESTABLISHED.  Let `V=F_2^n`, let `P` be a central marked projection in
`M_d(C)` of normalized trace `mu`, and let `U:V->U(PH)` be an exact additive
action with spectral PVM `(P_x)_(x in V)` inside `P`.

Let `g_1,...,g_D in GL(V)` be symmetric as a multiset, and suppose their dual
action on

```text
Omega=V^*\{0}
```

has normalized spectral gap at least `gamma>0`.  Let `C_s` be unitaries
preserving `PH`, and put

```text
eta_act^2
 =(1/D) sum_s E_a
   ||C_s U(a) C_s^* - U(g_s a)||_(2,d)^2.                     (OPS1)
```

Finally let `Z` preserve `PH`, fix `a_0!=0`, and put

```text
eta_seed=||Z U(a_0) Z^*+U(a_0)||_(2,d).                       (OPS2)
```

Then either

```text
d >= (2^n-1)/2,                                               (OPS3)
```

or

```text
mu <= 4 eta_act^2/gamma + eta_seed^2/4.                       (OPS4)
```

Thus one D8/Pauli edge `[U(a_0),Z]=J` on the `J=-1` sector, together with a
bounded uniform-expander actor on the nonzero X characters, is already an
unbounded same-Hilbert dimension witness.  No second additive Z table and no
mixed X/Z rectangle sampler is required.
