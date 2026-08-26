---
rg: 2
id: remainder-corner-root-character-is-persistently-nonregular
kind: claim
title: On the remainder corner the subgroup character is non-regular on every root subgroup, the non-regularity is invariant under all compression endomorphisms, and exactly substitution-invariant ideals containing a monomial are cofinite
distinct_from:
  kt-remainder-corner-characters-are-infinite-index-induced: that identifies the extremal components on the remainder corner as infinite-index induced characters; this extracts from the finite-dimensional fibers of those components a root-subgroup obstruction that survives the mixture, and a substitution-invariance lemma on ideals.
  tempered-gamma-part-of-a-model-is-compressor-invariant: that shows the tempered corner carries the regular character mod center, hence the regular restriction to every root subgroup; this shows the remainder corner never does, so the two corners are distinguished by a single root subgroup.
  kt-compression-fixed-tracial-states-are-atomic-or-regular: that is the open classification; this records two rigorous constraints on any counterexample and the combinatorial lemma that a proof through substitution-invariant ideals will need.
---

Setting as in `kt-remainder-corner-characters-are-infinite-index-induced`:
`R_+ = F_q[x_1..x_d]`, `d >= 2`, `Gamma = EL_r(R_+)` with `r > sr(R_+)`,
`chi` the compression-fixed character of `Gamma` on the remainder corner of a
model, `chi = int chi_omega dmu`, `chi_omega = Ind_(N_omega) sigma_omega`,
`[Gamma : N_omega] = infinity`, `N_omega cap U_ij = e_ij(I_omega)` for a nonzero
proper ideal `I_omega`.  Fix a root subgroup `U_ij = {e_ij(f)} ~= (R_+, +)`,
let `psi(f) = chi(e_ij(f))`, and let `nu` be the probability measure on the
compact dual `hat R_+ ~= F_q^(N^d)` (coordinates `theta_v = theta(x^v)`) with
`psi = hat nu`.  Write `psi'(f) = psi(f(0))` for the "augmentation-regular"
comparison function.

**Theorem.**
1. For `mu`-a.e. `omega` there is a nonzero ideal `J_omega <= I_omega` with
   `chi_omega(e_ij(a)) = 1` for all `a in J_omega`; hence `nu` charges a
   closed subgroup `J^perp`, `J != 0`, which is Haar-null on the nonzero
   coordinates.
2. Consequently `nu` is not of the form `(law of theta_0) (x) Haar`, i.e.
   `psi != psi'`: there is a nonconstant `f` with
   `chi(e_ij(f)) != chi(e_ij(f(0)))`.  The tempered corner, by contrast, has
   `psi = psi'` (regular character mod center).  So a remainder-corner
   character is detected on a single root subgroup.
3. The set `D = {f : psi(f) != psi'(f)}` satisfies `phi_A^(-1)(D) = D` for
   every compression endomorphism `phi_A`, so it contains the full
   substitution orbit `{f o phi_A}` of each of its elements: the
   non-regularity is compression-persistent.
4. (Monomial lemma.)  If an ideal `J` of `R_+` satisfies `phi_A^(-1)(J) = J`
   for the transvections `A = 1 + E_ij` (all `i != j`) and contains a
   monomial, then `J` contains every non-constant monomial, hence the
   augmentation ideal, and is cofinite.  In particular the sandwich ideals of
   the kernel and of the projective kernel of any compression-fixed tracial
   state are either cofinite or monomial-free, and on the remainder corner of
   a criterion-form model they are zero.

**What this buys.**  A refutation of the remainder corner now has a concrete
target: show that a compression-fixed mixture cannot keep, on a root
subgroup, a non-regular defect along entire substitution orbits while each
component is supported on the annihilator of a nonzero ideal.  The monomial
lemma shows that the ideal-theoretic bookkeeping is rigid as soon as
monomials enter, and (1)--(3) show that the defect cannot be pushed to
"infinitely far out" polynomials -- it sits on an orbit-closed set.
