# Relative Schur maps for the first split-clock group

Date: 2026-08-11

## Computation

The script `split_clock_relative_h2_k1.g` uses GAP/HAP on the exact
`p=3`, `k=1` split-clock group

\[
G_1=J_1\rtimes B_1,
\qquad |G_1|=3^7=2187.
\]

It computes the integral degree-two homology maps induced by the two
subgroups

\[
G_h=J_1\rtimes\langle h\rangle,
\qquad
G_c=J_1\rtimes\langle c\rangle.
\]

The exact output is

```text
ambient_order=2187
ambient_H2=[ 3, 3, 9 ]
positive_h_order=729
positive_h_H2=[ 9, 9, 9 ]
positive_h_image=[ 3, 9 ]
positive_h_image_order=27
positive_h_cokernel=[ 3 ]
cycle_c_order=243
cycle_c_H2=[ 3, 9 ]
cycle_c_image=[ 3, 9 ]
cycle_c_image_order=27
cycle_c_cokernel=[ 3 ]
```

Thus

\[
H_2(G_1;\mathbb Z)\cong C_3\oplus C_3\oplus C_9,
\]

and each subgroup map has image `C_3 directSum C_9` of index three.

## Interpretation

The translation-positive subgroup already carries an order-nine Schur
direction.  This independently confirms the exact Fox/Shapiro conclusion
that the growing clock curvature is not an exactly relative class in the
natural model.  Only a bounded `C_3` quotient remains after either one of
the two displayed subgroup maps at the first level.

This does not obstruct asymptotic branch cutting.  A primitive order-nine
character is close to one on a unit clock coordinate, while its value on the
order-three Bockstein shadow is macroscopic.  The correct next invariant is
therefore the size of the fixed relator coordinates in that character, as
explained in
`notes/FALSE_EXACT_ABSORPTION_BRANCH_CUT_DISTINCTION.md`.

The two HAP calls construct independent target models for the same abstract
ambient homology group, so the script deliberately does not claim the order
of the sum or intersection of their images.  That comparison is unnecessary
for the marked clock conclusion and would require a shared explicit chain
model.

## Reproduction

Run the GAP script with HAP and the polycyclic package available.  It checks
all group orders before computing the induced maps and prints their source,
image, and cokernel invariants.  The MSI run used one CPU and completed in a
few seconds.
