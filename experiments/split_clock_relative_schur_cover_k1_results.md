# The two natural split-clock Schur images fill the first multiplier

Date: 2026-08-11

## Exact result

For the `p=3`, `k=1` split-clock group

\[
G_1=J_1\rtimes(C_9\rtimes_4 C_3),
\qquad |G_1|=3^7,
\]

put

\[
G_h=\langle J_1,h\rangle,
\qquad
G_c=\langle J_1,c\rangle.
\]

The earlier HAP calculation determined the abstract invariants of the two
maps into `H_2(G_1;Z)` separately.  It could not compare their images because
the two calls constructed different target chain models.  The script
`split_clock_relative_schur_cover_k1.g` instead places both maps inside one
Schur extension of one pcp model of `G_1`.

The exact output is

```text
ambient_order=2187
multiplier=[ 3, 3, 9 ]
positive_h_image=[ 3, 9 ]
positive_h_image_order=27
cycle_c_image=[ 3, 9 ]
cycle_c_image_order=27
images_equal=false
intersection=[ 9 ]
intersection_order=9
combined_image=[ 3, 3, 9 ]
combined_image_order=81
combined_cokernel=[  ]
```

Consequently, inside one common explicit multiplier model,

\[
H_2(G_1;\mathbb Z)\cong C_3\oplus C_3\oplus C_9,
\]

\[
\operatorname{im}H_2(G_h)\cong
\operatorname{im}H_2(G_c)\cong C_3\oplus C_9,
\]

but the two images are unequal, their intersection is `C_9`, and

\[
\boxed{
\operatorname{im}H_2(G_h)+\operatorname{im}H_2(G_c)
=H_2(G_1;\mathbb Z).
}
\]

In particular, quotienting the ambient multiplier by both natural subgroup
images gives zero.  The two index-three cokernels observed separately are
different `C_3` directions; neither survives after the other subgroup image
is included.

## Why the Schur-extension calculation gives the induced images

Let

\[
1\longrightarrow K\longrightarrow E\longrightarrow G_1\longrightarrow1
\]

be the Schur extension returned by the polycyclic package and put

\[
M=K\cap[E,E].
\]

The Hopf formula identifies `M` with `H_2(G_1;Z)`.  For a subgroup
`H<=G_1`, let `E_H` be its full preimage.  Naturality of the five-term
sequence identifies the image of

\[
H_2(H;\mathbb Z)\longrightarrow H_2(G_1;\mathbb Z)=M
\]

with

\[
M\cap[E_H,E_H].
\]

This is exactly how the two image subgroups in the script are constructed.
The script additionally asserts all displayed invariants, the unequal-image
test, the intersection, and equality of the combined image with `M`.

## Interpretation

This closes the unresolved comparison left by
`split_clock_relative_h2_k1_results.md`.  There is no hidden first-level
Schur direction surviving both the translation-positive and pure-cycle
subgroups in the natural finite clock.

The result strengthens the exact-absorption diagnosis but does **not** rule
out the asymptotic branch-cut route.  Exact subgroup images may generate the
whole finite multiplier using coefficients which grow with `k`, while a
primitive order-`p^k` character can still approach one on every fixed
bounded coordinate and remain nontrivial on an order-`p` Bockstein shadow.
The live invariant is therefore still the quantitative fixed-window
Schreier/Weyl energy, not another exact relative quotient.

## Reproduction

The GAP script uses the `polycyclic` package.  It converts the finite pc group
to the package's pcp representation before constructing the Schur extension.
The MSI run used one CPU and completed in a few seconds.
