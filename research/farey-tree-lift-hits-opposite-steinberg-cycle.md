---
rg: 2
id: farey-tree-lift-hits-opposite-steinberg-cycle
kind: claim
title: The Farey-tree lift hits the opposite-cone Steinberg cycle at its first edge
distinct_from:
  opposite-transvections-are-first-nonore-relative-gate: that identifies the opposite pair as the first open slice and proves finite-image collapse; this computes why the SL2 Bass--Serre tree does not resolve it
  heisenberg-kun-thom-slice-is-relatively-embeddable: that uses an Ore Heisenberg telescope with common positive levels; this exhibits the explicit cross-cone relation preventing such a directed/tree-free replacement
  sofic-coset-action-makes-amalgam-double-sofic: that gives a positive conclusion from a sofic coset action; this is a no-go for one proposed construction of that action and asserts no negative conclusion about soficity
---

Keep the opposite-transvection notation and put

```text
J=A B^(-1) A=[[0,1],[-1,0]],       z=J^2=-I.
```

Let

```text
R_+=k[x_1,x_2,x_3,...,x_d],
R_-=k[x_1^(-1),x_2^(-1),x_3,...,x_d],
R_pm=k[x_1^(+-1),x_2^(+-1),x_3,...,x_d],
Gamma_+=EL_r(R_+),       Gamma_-=EL_r(R_-),       E_pm=EL_r(R_pm).
```

Then:

1. The order-two cone flip already generates the full Laurent kernel:

   ```text
   <Gamma_+,z>=E_pm rtimes <z>.                                (FTC1)
   ```

2. Lifting the classical Bass--Serre decomposition
   `SL_2(Z)=C_4 *_(C_2) C_6` gives

   ```text
   P=(E_pm rtimes C_4) *_(E_pm rtimes C_2) (E_pm rtimes C_6).  (FTC2)
   ```

   Thus the first edge group already contains `E_pm); the Farey tree has
   not split the Laurent kernel into directed positive pieces.

3. This failure is witnessed by one explicit relation.  Put
   `R_0=k[x_3,...,x_d]` (with `R_0=k` if `d=2)) and
   `Gamma_0=EL_r(R_0)`.  The natural map

   ```text
   Gamma_+ *_(Gamma_0) Gamma_- -> E_pm
   ```

   has nontrivial kernel.  With elementary root matrices,

   ```text
   g=e_12(x_1),       h=e_23(x_1^(-1)),
   w=[g,h] e_13(-1),                                        (FTC3)
   ```

   the Steinberg commutator formula gives `w=1` in `E_pm`, while `w`
   is a reduced nonidentity word in the free amalgam.

The geometric and algebraic obstructions are the same.  The flip `z` sends
the positive cone to its negative, and no pointed cone can contain both.
Relation (FTC3) multiplies the opposite exponents `1` and `-1` back to
the zero exponent.  A tree of independent cone groups omits precisely this
cross-cone multiplication relation.

Consequently neither external Bass--Serre permanence nor a free amalgam of
one-cone models proves the opposite-pair coset action sofic: the former has
the entire Laurent group in its edge, while the latter constructs a larger
group and must pass to the quotient by (FTC3) and all its translates.
Soficity, hyperlinearity, and `RE/C` have no general quotient permanence
that performs this step.  This is a rigorous firewall for the Farey-tree
route, not a proof that the opposite slice is negative.

DERIVATION
opposite-cones-generate-laurent-kernel-proof
