---
rg: 2
id: remainder-corner-fiber-kernels-are-monomial-free
kind: claim
title: The trivial-mass function of a compression-fixed character is non-increasing along compression orbits, and on the remainder corner the kernel ideals of the fiber representations are almost surely monomial-free
distinct_from:
  remainder-corner-root-character-is-persistently-nonregular: that shows each fiber kernel ideal is nonzero and that the root-subgroup measure charges a Haar-null annihilator; this uses the compression transport of the extremal decomposition to show the kernel ideals contain no monomial, ruling out exactly the compression-friendly components.
  kt-compression-fixed-tracial-states-are-atomic-or-regular: that is the open classification; this is a proved constraint on any counterexample: the random kernel ideal has zero probability of containing any given nonzero monomial.
  model-characters-of-compressed-pairs-are-compression-invariant: that records the fixed-point property `chi o phi_A = chi`; this extracts from it, through uniqueness of the extremal decomposition, a monotonicity of trivial masses that the fixed-point property alone does not display.
---

Setting of `kt-remainder-corner-characters-are-infinite-index-induced`:
`Gamma = EL_r(F_q[x_1..x_d])`, `d >= 3`, `r > sr`, `chi` the
compression-fixed character on the remainder corner, `chi = int chi_omega dmu`
its unique extremal decomposition, `chi_omega = Ind_(N_omega) sigma_omega`
with `[Gamma : N_omega] = infinity`, and `J_omega != 0` the kernel ideal of
the fiber, `ker sigma_omega cap U_ij = e_ij(J_omega)`
(`remainder-corner-root-character-is-persistently-nonregular`).  For `g in
Gamma` write

```text
Psi(g) = mu{ omega : chi_omega(g) = 1 },
```

the mass of the components in which `g` acts trivially; `Psi` depends only
on `chi` (the decomposition is unique).

**Theorem.**
1. (Transport.)  For every compression endomorphism `phi_A`,
   `Psi(g) >= Psi(phi_A(g))` for all `g in Gamma`.
2. (Constancy on monomials.)  On any root subgroup, `m(f) := Psi(e_ij(f)) =
   mu{omega : f in J_omega}` satisfies `m(x^v) = m_0` for every nonzero
   monomial `x^v`, a constant.
3. (Monomial-freeness.)  `m_0 = 0`: for `mu`-almost every `omega` the ideal
   `J_omega` contains no monomial; equivalently, for every nonzero monomial
   `x^v` and almost every component, `chi_omega(e_ij(x^v)) != 1`.

**What this excludes.**  The compression-friendly candidate components --
fibers trivial on `E(R_+, (x^v))`-type relative elementary groups, whose
kernels are the monomial ideals the substitution monoid moves among
themselves -- carry no mass in a compression-fixed remainder character.  Any
counterexample to `kt-compression-fixed-tracial-states-are-atomic-or-regular`
must be built from fibers whose kernel ideals are nonzero but avoid every
monomial, e.g. binomial or non-monomial prime ideals of infinite colength,
and the transport inequality (1) is the tool for the next constraint: the
law of the random ideal `J_omega` is stationary under kernels that move an
ideal `J` to ideals containing `phi_A^(-1)(J)`, whose varieties are the
closures of the images of `V(J)` under the monomial maps.
