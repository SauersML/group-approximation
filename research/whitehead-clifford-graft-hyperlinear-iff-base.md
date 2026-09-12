---
rg: 2
id: whitehead-clifford-graft-hyperlinear-iff-base
kind: claim
title: The full Whitehead--Clifford graft is hyperlinear exactly when its affine-Leavitt base is
distinct_from:
  full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark: that proves exact finite-dimensional collapse of the grafted binary mark; this proves that the normalized-HS question has not become smaller than hyperlinearity of the base.
  amenable-edge-graph-corners-cannot-groupify-a-nonce-game: that gives general hyperlinearity permanence for amenable-edge graphs; this applies it in both directions to the specific signed Whitehead cyclic amalgam and computes its canonical leakage.
  affine-leavitt-tracial-square-function-firewall: that substitutes the regular representation of the affine-Leavitt base into a broad tracial proof calculus; this computes the exact unoriented support obstruction in the regular representation of the graft itself.
---

**ESTABLISHED PERMANENCE AND REGULAR-MODEL FIREWALL.**  Retain the notation
of `full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark`:

```text
Gamma_A'=St_5(R_A)/<<W^4>>,
Gamma_FWA=D *_(<u>=<W>~=C_4) Gamma_A',                 (HCE1)
```

where `D` is the explicit finite controlled-Pauli monomial group.  Then

```text
Gamma_FWA is hyperlinear  iff  Gamma_A' is hyperlinear. (HCE2)
```

The forward implication is subgroup permanence: Bass--Serre normal form
embeds `Gamma_A'` in `Gamma_FWA`, and subgroups of hyperlinear groups are
hyperlinear.  Conversely, `D` is finite and hence hyperlinear, the edge
`C_4` is finite amenable, and hyperlinearity is preserved by amalgamated
free products over amenable subgroups.  This is the one-edge case of
`amenable-edge-graph-corners-cannot-groupify-a-nonce-game`.

Thus adjoining the complete controlled packet and the odd row does not
turn the normalized-HS problem into a weaker local stability assertion.  A
dimension-uniform estimate forcing the nontrivial packet mark to collapse
in canonical microstates of `Gamma_FWA` proves `Gamma_FWA`
nonhyperlinear, and `(HCE2)` then proves the affine-Leavitt base
`Gamma_A'` nonhyperlinear.  Conversely, nonhyperlinearity of the base
already forces nonhyperlinearity of the graft.

There is also an exact canonical-trace countermodel to every *tracial*
promotion of the desired support row.  In `L(Gamma_FWA)`, form from the
embedded finite packet `D` the projections

```text
p_s=e z_+,                 p_t=f(z_++z_-).             (HCE3)
```

The canonical group trace restricts to the regular trace on `D`, so

```text
tau(z_+)=1/4,             tau(p_s)=tau(p_t)=1/8.       (HCE4)
```

All affine-Leavitt occurrences, the cyclic amalgam row, and the odd row

```text
t=W Z_1 W^(-1)                                           (HCE5)
```

hold exactly.  Apply
`odd-row-unoriented-fine-return-has-quarter-floor` with this exact tuple.
Its odd-row defect is zero, hence

```text
||(1-p_t)W p_s||_2^2 >= tau(z_+)/4 = 1/16.             (HCE6)
```

Therefore the full occurrence system itself does not algebraically imply
the support incidence `(OUF8)`, even with exact canonical trace on every
fixed word and exact packet types.  Any estimate

```text
||(1-p_t)W p_s||_2^2
 <= C (presentation energy + canonical trace error)     (HCE7)
```

which is valid in all finite tracial von Neumann algebras is false by
`(HCE6)`.  A successful matrix theorem must use a genuinely finite-coordinate
operation unavailable in this regular model.

The standard proposed upgrades do not supply such an operation:

1. property `(T)` and robust adjoint spectral gap are finite-tracial
   representation-theoretic statements and hold in the regular model;
2. exactifying any fixed finite root/Heisenberg window leaves arbitrarily
   large finite Schrödinger multiplicity and does not construct the common
   returned reservoir;
3. the exact root-kernel proof chooses a kernel of codimension depending on
   matrix dimension and then an ideal expression for `A` depending on that
   kernel; normalized-HS-small errors may have full rank, so neither choice
   has a dimension-uniform finite-window bound; and
4. LLP, weak ucp stability, or full flexible HS stability would suffice,
   but each is already a known nonhyperlinearity-strength input for this
   non-residually-finite Kazhdan base.

This is a no-go for the proposed *method classes*, not a matrix
ultraproduct countermodel: constructing the latter with the canonical mark
would prove `Gamma_A'` hyperlinear and select the opposite side of `(HCE2)`.
The remaining robustness gate is exactly the original MF-radical question.

This last statement can be made a literal equivalence.  Let `(CAN-OUF)` be
the asymptotic assertion that for every canonical microstate sequence of
`Gamma_FWA`,

```text
||(1-p_t(U_n))W(U_n)p_s(U_n)||_2 -> 0.                (HCE8)
```

Then

```text
(CAN-OUF)  iff  Gamma_FWA is nonhyperlinear
           iff  Gamma_A' is nonhyperlinear.           (HCE9)
```

If the group is nonhyperlinear there is no canonical microstate sequence,
so the universally quantified asymptotic assertion holds.  If it is
hyperlinear, choose a canonical sequence.  The square of the norm in
`(HCE8)` is the trace of one fixed group-algebra `*`-polynomial, hence it
converges to its regular value.  By `(HCE6)` that value is at least `1/16`,
so `(CAN-OUF)` fails.  The second equivalence is `(HCE2)`.

Accordingly, the asymptotic form of `(OUF8)` is not merely sufficient for
the desired result: on this full graft it is logically equivalent to it.
Any useful intermediate lemma must retain additional quantitative structure
which is weaker than canonical support collapse; otherwise it has simply
renamed the open problem.
