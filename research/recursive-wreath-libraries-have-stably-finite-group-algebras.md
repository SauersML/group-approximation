---
rg: 2
id: recursive-wreath-libraries-have-stably-finite-group-algebras
kind: claim
title: Finite-depth wreath libraries and groups separated by them satisfy Kaplansky over every field
distinct_from:
  rf-lamp-permutational-wreaths-satisfy-stable-finiteness: that handles one wreath step over residually finite groups; this allows arbitrary finite nesting with nonsofic intermediate groups and then infinite-depth residual separation.
  recursive-quine-route-to-kaplansky-is-closed: that excludes two particular recursive support families and classifies one compiler; this is a positive finiteness theorem for a precisely defined, much larger hierarchy.
  finite-subgroup-copy-circuits-have-no-recurrent-branching: that constrains exact decompositions of finite-subgroup projectives; this concerns groups obtained by iterated permutation-wreath constructions and separating homomorphisms.
---

Define C_0 to be the class of residually finite groups. Given C_n, let
C_(n+1) consist of subgroups of finite direct products of restricted
permutational wreath products A wr_X G with A,G in C_n and arbitrary
G-sets X. Put C_fin=union_(n>=0) C_n.

Then k[H] is stably finite for every H in C_fin and every field k.
Each C_n, and hence C_fin, is closed under subgroups and finite direct
products. The hierarchy is increasing and C_fin is closed under another
restricted permutational wreath construction.

More generally, suppose a group H is residually C_fin: for every h!=1
there is a homomorphism H->K, K in C_fin, with nonidentity image of h.
Then k[H] is stably finite over every field. This includes subgroups of
arbitrary direct products of C_fin groups and inverse limits of groups
from C_fin. The separating maps need not be finite-dimensional or have
finite group images.

Directed colimits of groups from C_fin also have stably finite group
algebras, including directed unions with unbounded wreath depth. This
conclusion does not require residual separation of the colimit.

Consequently consider a spherically homogeneous rooted tree whose local
permutation groups G_i<=Sym(X_i) are residually finite, allowing infinite
branching sets X_i. The group of automorphisms with these local groups
and only finitely many nonidentity local permutations at each fixed level
has stably finite group algebra over every field. It may have nontrivial
activity at arbitrarily large depths. Any subgroup inherits the result.

The final statement requires faithful detection by finite-depth tree
actions and finite activity at each fixed level. It does not treat an
abstract recursive presentation with a nontrivial kernel invisible at
every truncation, unrestricted infinitely many active sections at one
level, or arbitrary quotients of the displayed groups. No conclusion
about all computational group constructions is asserted.
