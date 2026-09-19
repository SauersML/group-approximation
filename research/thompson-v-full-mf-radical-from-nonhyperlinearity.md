---
rg: 2
id: thompson-v-full-mf-radical-from-nonhyperlinearity
kind: route
title: A surviving norm model of V Diracizes to a tracial embedding, so nonhyperlinearity forces full MF radical
target: thompson-v-has-full-mf-radical
requires:
  - thompson-v-not-hyperlinear
  - torsion-normal-generator-mf-character-criterion
  - thompson-v-finitely-presented-infinite-simple
---

Suppose `Rad_MF(V) /= V`.  `V` is finitely generated, and the involution
`v=s_00t_01+s_01t_00+s_1t_1` normally generates `V` because `V` is simple.
The reverse direction of `torsion-normal-generator-mf-character-criterion`
(active-core reblocking, Kazhdan-free) gives a nontrivial MF character
`tau = lim tr_n o pi_n`, with `pi_n` an operator-norm asymptotic
representation.

**Scalar kernel.**  `S = {g : |tau(g)|=1}` is a normal subgroup, and
`tau|S` is a homomorphism `S -> T` (a unitary with trace of modulus one
in the limit is asymptotically scalar in normalized HS norm).  If `S=V`,
then `tau` is a homomorphism `V -> T`, trivial because `V` is perfect,
contradicting nontriviality.  So `S=1` by simplicity: `|tau(g)|<1` for
every `g /= 1`.

**Diracization.**  For fixed `k`, `pi_n^(tensor k) tensor conj(pi_n)^(tensor k)`
is again an operator-norm asymptotic representation (telescoping the
defect), and its normalized trace converges to `|tau|^(2k)`.  A diagonal
sequence `k_m -> infinity` gives an operator-norm asymptotic representation
`sigma_m` with `tr o sigma_m -> delta_e` pointwise on the countable group `V`.

**Tracial embedding.**  Operator-norm defect bounds normalized HS defect,
and `||sigma_m(g)-1||_2^2 = 2-2 Re tr sigma_m(g) -> 2` for `g /= 1`.  So
`sigma_m` defines an injective homomorphism of `V` into a tracial matrix
ultraproduct, i.e. `V` is hyperlinear, contradicting
`thompson-v-not-hyperlinear`.  Alternatively,
`thompson-v-character-simplex` writes `tau = t tau_reg + (1-t)` with `t>0`,
and the same tensor-power argument applies.

No property (T), Kazhdan projection or spectral-gap input is used.  The
only analytic input is the reblocking of
`torsion-normal-generator-has-full-support-corona-core`, which the criterion
cites.
