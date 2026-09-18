---
rg: 2
id: commensurating-end-germ-groups-omit-aff-q
kind: claim
title: No finitely generated group of dyadic PL end-germs commensurating the germ of x -> x+1 contains Aff(Q), SL_2(Q) or PSL_2(Q)
distinct_from:
  aff-q-forces-distortion-in-abelian-kernels: that is the general lemma about abelian quotients of overgroups of Aff(Q); this applies it to groups of germs at +infinity that commensurate the deck translation, using periodic extension into copies of T-bar.
  fg-pl-quasi-similarity-groups-contain-no-gl-2-q: that excludes Aff(Q) from finitely generated groups of homeomorphisms of the whole line at bounded distance from similarities; this treats groups of germs at one end, which need not come from homeomorphisms of the line, and draws the consequence for finite germ extensions.
  normal-germ-extensions-of-thompson-v-contain-no-sl3z: that treats germ groups that normalize the local dilation, where every image of BS(1,2) sends a to an element of finite order; this treats germ groups that only commensurate it, where BS(1,2) does embed but Aff(Q) does not.
  aff-q-does-not-embed-in-aut-thompson-f: that excludes T-bar and Aut(F), whose end-germs centralize z; this allows end-germs that conjugate z^a to z^b with a != b.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this closes one family of end-germ designs for n >= 2.
artifacts:
  - research/artifacts/gq-gq-lit-q-embeddings.md
---

**ESTABLISHED** through `commensurating-end-germ-groups-omit-aff-q-proof`. Lane proof,
not independently reviewed. It rests on the unrefereed arXiv:2605.09763v1
(Burillo--Felipe), as does root obstruction O4.

## Setting

An increasing homeomorphism between half-lines `[c, inf) -> [c', inf)` is
**dyadic PL** when all of the following hold:
- it is piecewise linear with finitely many breakpoints in each compact interval;
- its pieces have the form `x -> 2^n x + d` (`n in Z`, `d in Z[1/2]`);
- its breakpoints are dyadic.

Let `z(x) = x + 1`. `Comm_inf` is the group of germs at `+inf` of dyadic PL maps `h`
for which some integers `a, b >= 1` satisfy `h(x + a) = h(x) + b` for all large `x`.
- **In the germ language**, each such germ commensurates `<z>`: `h z^a h^-1 = z^b`.
- **What it contains.** The end-germs of `T-bar` (`a = b`), the germ of
  `x -> 2x` (`a = 1, b = 2`), and hence a copy of `BS(1,2)`.

## Statement

Let `K <= Q^x_{>0}` be a subgroup that is not finitely generated, and
`Aff_K(Q) = Q x| K`. No finitely generated subgroup of `Comm_inf` contains a copy
of `Aff_K(Q)`. This covers the following, and every group containing one of them:
- `Aff(Q)` and `GL_2(Q)` (`K = Q^x_{>0}`);
- `SL_2(Q)` and `PSL_2(Q)` (`K` = the squares, by Corollary (iii) of the lemma);
- `GL_n(Q)`, `SL_n(Q)` and `B_n(Q)`, for `n >= 2`.

`Q x|_a Z` for a single dilation `a` is not addressed.

The same proof, with global maps in place of germs, shows this for the group of
dyadic PL homeomorphisms of `R` with `h(x + a) = h(x) + b`. That case, which is
Spark S1 of `research/artifacts/gq-gq-lit-q-embeddings.md` §7, also follows from
`fg-pl-quasi-similarity-groups-contain-no-gl-2-q`.

## Consequence for finite germ extensions

Consider the design "VA with its end-germ group enlarged by affine or dilation
germs". It is a finite germ extension `E` of `V`, in the sense of
arXiv:2407.03149v1. At a singular point `p` ending in `0-bar`, its germs are
order-preserving and commensurate the prefix replacement `L_p`. Under the standard
dictionary between such germs at `p` and dyadic PL germs at `+inf` (as
Belk--Hyde--Matucci use for `A <= VA`; not re-derived here), the germ group
`(E)_p` is a subgroup of `Comm_inf`.

`(E)_p` is finitely generated whenever `SingFix_E({p},{p})` is, as the finiteness
criterion Theorem 2.1 of arXiv:2407.03149v1 requires. In that case:

1. No subgroup of `Stab_E(p)` isomorphic to `Aff(Q)`, `GL_2(Q)` or `SL_2(Q)` maps
   injectively into `(E)_p`.
2. No subgroup of `SingFix_E({p},{p})` is isomorphic to `Aff(Q)`. The germ map is
   injective on every such copy. Its kernel consists of elements with no singular
   points, so it lies in `V`, and it is normal in the copy. A nontrivial normal
   subgroup of `Aff(Q)` contains `Q`, and `Q` is not in `V` (Higman, survey
   Theorem 4.4).

So a germ-extension host for `Aff(Q)` needs at least one of these:
- germs that do not commensurate the local dilation;
- germs that are not order-preserving (the analogues of `T-bar` built from `V`
  rather than `T`, whose distortion is not settled here);
- copies of `Aff(Q)` that are not seen faithfully by the germ group at any
  singular point they fix.
