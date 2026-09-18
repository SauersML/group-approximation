---
rg: 2
id: gl-n-q-almost-v-hosts-need-lattice-germs
kind: claim
title: A finitely generated almost-V host of GL_n(Q), n >= 3, has one singular germ group containing a finite-index subgroup of every SL_3(Z[1/m])
distinct_from:
  normal-germ-extensions-of-thompson-v-contain-no-sl3z: that puts a finite-index subgroup of SL_3(Z) into a finite PRODUCT of germ groups of a Belk--Hyde--Matucci finite germ extension, and excludes hosts whose germs normalize the local dilation; this uses every S-arithmetic group SL_3(Z[1/m]) inside GL_n(Q), needs no germ complex, and puts all of them into ONE germ group of any finitely generated group of almost-V homeomorphisms.
  almost-v-fw-subgroups-act-through-finitely-many-germs: that is the general germ reduction for FW subgroups; this is its consequence for GL_n(Q), through Margulis's normal subgroup theorem.
  germ-extensions-omit-standard-gl-n-q: that excludes standard analytic copies of GL_n(Q) over piecewise-projective bases; this constrains every copy over the base V.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this is a necessary condition on one class of hosts.
---

**ESTABLISHED** through `gl-n-q-almost-v-lattice-germs-proof` (lane-proved, not
independently reviewed; two standard imports, named in the proof).

**Setting.** `H` is the group of homeomorphisms of the Cantor set `C` that are
locally in Thompson's `V` at all but finitely many points, as in
`almost-v-fw-subgroups-act-through-finitely-many-germs`. For `E <= H` put
`sing(E) = ⋃_{e in E} sing(e)`. For `y in C`, `(E)_y` is the group of germs at
`y` of elements of `E` fixing `y`. Every finite germ extension of `V` (including
`VA`, the shell groups `E_nu`, Röver--Nekrashevych groups `V_2 G` of bounded
automata groups) is a subgroup of `H`.

**Statement.** Let `n >= 3` and let `E <= H` contain a copy of `GL_n(Q)`.
Suppose `sing(E)` lies in finitely many `E`-orbits. This holds whenever `E` is
finitely generated, in particular when `E` is finitely presented. Then there is
a point `p in sing(E)` such that for every `m >= 1` some finite-index subgroup
`L_m <= SL_3(Z[1/m])` embeds in the germ group `(E)_p`.

**Consequences.**
- `(E)_p` contains infinite groups with property (T). So it is neither
  amenable nor a-T-menable, and it embeds in no Brin--Thompson group `nV`
  (`brin-thompson-groups-nv-are-a-t-menable`). In particular `(E)_p` is not
  virtually `(V)_p`, which is cyclic.
- **Transfer.** A germ-extension host over `V` does not make `GL_n(Q)` easier:
  one isotropy germ group must already contain, for every finite set of primes
  `S`, a finite-index subgroup of the `S`-arithmetic group `SL_3(Z[1/S])`, and
  the Belk--Hyde--Matucci finiteness theorem then asks for finite presentation
  of the singular stabilizers carrying that germ group. The shell envelopes of
  `shell-cantor-embeddings-are-finite-germ-extensions` do exactly this: their
  germ group at `0^∞` contains the input.
- The embeddings `L_m -> (E)_p` for different `m` are not claimed to be
  compatible. Whether `(E)_p` must contain `SL_3(Q)` itself is open.

**Scope.**
- **n = 2 is untouched.** Every FW subgroup of `GL_2(Q)` is finite. A finitely
  generated subgroup lies in `GL_2(Z[1/m])` for some `m`. An FW subgroup fixes a
  vertex of the product of the Bruhat--Tits trees of `PGL_2(Q_p)`, `p | m` (a
  CAT(0) cube complex), so its image in `PGL_2(Q)` lies in a group commensurable
  with `PGL_2(Z)`. That group is virtually free, so the image is finite. The
  kernel is central, and an abelian FW group is finite. So the FW method says
  nothing about `GL_2(Q)`, `SL_2(Q)` or `Aff(Q)`. Those need divisibility or
  distortion arguments (root obstruction O4 for `VA`).
- Hosts over other bases (`nV`, twisted Brin--Thompson groups) are not treated.
  The germ reduction adapts to bases that are full and clopen-transitive, but
  the finiteness of FW subgroups of the base is then false or unknown.
