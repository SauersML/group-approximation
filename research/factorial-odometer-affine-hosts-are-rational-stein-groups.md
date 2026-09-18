---
rg: 2
id: factorial-odometer-affine-hosts-are-rational-stein-groups
kind: claim
title: Radix-changing value-affine homeomorphisms of the factorial odometer form the rational Stein–Thompson group, whose finitely generated subgroups lie in finitely presented Stein interval-exchange groups
distinct_from:
  mixed-radix-prefix-replacement-groups-omit-baumslag-solitar: that treats prefix replacements with identical tails, which are locally finite on the factorial odometer; this adds the radix-changing re-expansions that act at infinitely many depths and identifies the resulting group.
  interval-exchange-pl-groups-act-with-type-a-on-breakpoints: that gives type (A) actions of f.p. V(l;A,P); this shows the factorial-odometer radix-changing host is exactly a union of such groups.
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed).

## Setting

X = ∏_{n≥1} Z/(n+1) (the factorial odometer), with value ν(d) = Σ_n d_n/(n+1)!. Its tail spaces are
X_k = ∏_{n>k} Z/(n+1).

## Statement

1. **The Cantor model is canonical.** A point has two preimages under ν exactly when its value is rational in (0,1), because
   every rational has a finite factorial expansion, and Σ_{n>K} n/(n+1)! = 1/(K+1)! gives the second one. So ν identifies X
   with D = [0,1] with every rational of (0,1) doubled, and the same holds for every tail X_k. So the value-preserving
   re-expansion X_k → X_{k'} (the same real number written in the other tail base) is a homeomorphism. It changes digits at
   infinitely many depths.
2. **The group.** Let Γ_Q be the group of homeomorphisms of X that, on a finite partition into cylinders, map each cylinder
   [u] affinely in value (increasing) onto a cylinder [u']. Each piece is a prefix change followed by a re-expansion of the
   tail. Then Γ_Q is isomorphic to the group V(Q, Q_{>0}) of right-continuous piecewise-affine bijections of [0,1) with
   finitely many pieces, rational breakpoints and positive rational slopes.
3. **Finitely generated subgroups.** Every finitely generated subgroup of Γ_Q lies in some Stein interval-exchange group
   V(1; Z[1/M], ⟨p : p | M⟩). Such a group satisfies the hypotheses of
   `interval-exchange-pl-groups-act-with-type-a-on-breakpoints`: A/I_P·A is finite, since it is a quotient of
   Z[1/M]/(p−1). So whenever it is finitely presented, every subgroup satisfies PBH (Stein's finite-presentation theorem,
   cited there, not re-read).

## Proof

1. Finite expansions: if q = a/b with b | (K+1)!, then q·(K+1)! is an integer, and the greedy digits terminate by depth K.
   The telescoping sum is k/(k+1)! = 1/k! − 1/(k+1)!. Hence ν is injective off the rationals and 2-to-1 on the rationals of
   (0,1). The cylinder topology is the order topology of D, so it does not depend on the base, and the re-expansion is the
   identity of D.
2. An increasing affine map of [ν(u), ν(u) + 1/|u|) onto [ν(u'), ν(u') + 1/|u'|) (|u| is the product of the radices of the
   prefix) is a homeomorphism of the two doubled-rational Cantor intervals, because it maps rationals to rationals. Gluing
   finitely many such maps gives exactly the elements of V(Q, Q_{>0}). Conversely, every breakpoint of an element of
   V(Q, Q_{>0}) is rational, hence a cylinder boundary at some depth. So the element is value-affine on a cylinder
   partition.
3. Take M divisible by every denominator of the breakpoints and affine coefficients of the generators, and by every prime in
   their slopes. Composition preserves both conditions.

## Consequence (the design question for Aff(Q))

A factorial-odometer host built from value-coherent radix changes contains Aff(Q) exactly when some Stein group
V(1; Z[1/M], ⟨p|M⟩) does. That is the OPEN premise `aff-q-embeds-in-a-stein-interval-exchange-group`. The natural affine
action is excluded, because slopes lie in a finitely generated group (root obstruction H3). Only abstract, "wild" copies
remain.
