---
rg: 2
id: affine-leavitt-p-heisenberg-graft-kills-fd-four-cap-corner
kind: claim
title: A native p-Heisenberg graft kills every finite evaluation of a selected four-cap corner
distinct_from:
  odd-root-cannot-drive-central-d8-actuator: that claim rules out converting the odd root into a binary central sign; this construction keeps a separate central sign of the same odd order and uses its character projection.
  four-cap-three-actuator-destroys-all-fd-packet-evaluations: that claim uses a Thompson-V involution to kill the binary sign exactly; this construction retains the binary sign and adds an odd character sector whose HS collapse is precisely the affine-Leavitt decoder.
  affine-leavitt-steinberg-mark-is-fd-invisible: that claim kills the native root in finite-dimensional representations; this claim promotes the root to a positive canonical packet-corner selector.
---

**ESTABLISHED.**  Let the affine-Leavitt splitting field have odd
characteristic `p>=5`, put

```text
Gamma_A=St_5(R_A),             w=x_12(A),                (PHG1)
```

and let `c` be a new central element of order `p`.  Form the finite
Heisenberg group

```text
H_p=<w,z,c | w^p=z^p=c^p=1,
                 c central, [w,z]=c>,                   (PHG2)
```

and the amalgam

```text
Lambda_p=(Gamma_A times <c>) *_(<w,c>) H_p.             (PHG3)
```

Here `<w,c>` is `C_p^2` in both factors.  The amalgam normal form embeds
both vertex groups, so `c` and `w` remain nontrivial.  The group `Lambda_p`
is finitely presented.

Let `Gamma_2` be the marked two-chart four-cap mixer and put

```text
G_p=Gamma_2 times Lambda_p.                              (PHG4)
```

For a nontrivial character `chi:C_p -> T`, define

```text
e_chi=(1/p) sum_(k=0)^(p-1) conjugate(chi(c))^k c^k,
Q_chi=q tensor e_chi,       q=(1-J)/2.                  (PHG5)
```

Then `Q_chi` is a nonzero projection of positive canonical trace

```text
tau(Q_chi)=tau(q)/p>0.                                  (PHG6)
```

The binary packet sign `J` stays central and nontrivial, and every cap atom
of `q C[Gamma_2]q` remains nonzero after tensoring with `e_chi`.

Every finite-dimensional unitary representation of `G_p` kills this whole
selected corner.  Its restriction to `Gamma_A` sends `w` to `1` by
`affine-leavitt-steinberg-mark-is-fd-invisible`; `(PHG2)` then gives

```text
pi(c)=pi([w,z])=1.                                      (PHG7)
```

The nontrivial character sum in `(PHG5)` is zero at `c=1`, so

```text
pi(e_chi)=0,               pi(Q_chi)=0.                 (PHG8)
```

This is the order-correct affine-Leavitt graft.  It does not identify the
odd root with the binary sign and therefore avoids
`odd-root-cannot-drive-central-d8-actuator`.  Unlike the Thompson actuator,
its normalized-HS endpoint is genuinely the existing affine-Leavitt
coefficient decoder.

The selected odd corner itself is computed by
`selected-odd-heisenberg-corner-is-native-matrix-amalgam`: it is exactly
`C[Gamma_A] *_(C[C_p]) M_p(C)`.  Hence the graft supplies the necessary
finite-dimensional-invisible packet type but does not create a new
independent source of non-CE holonomy.  A no-CE BCS atlas in that corner
would already force the native `Gamma_A` vertex to be nonhyperlinear.
