---
rg: 2
id: high-type-mass-is-discontinuous-at-exact-code-tuples
kind: claim
title: High irreducible type has full trace arbitrarily close to exact all-dual code tuples
distinct_from:
  bounded-type-balanced-occurrences-synchronize: that rounds a tuple under an a priori bound on the generated algebra's irreducible type; this proves that such a bound cannot be inferred, even approximately, from balanced presentation defect.
  balanced-parity-excludes-perfect-matching-pauli-mixtures: that excludes a far high-type projective construction; this produces genuinely full-matrix high type at vanishing defect but remains inside the correctable local basin.
  positive-rate-tanner-tests-have-contextual-models: that gives exact far class-two models before the complete-pair overlay; this survives the complete balanced presentation only as a near-exact, near-code tuple and is a no-go for PI truncation rather than a rounding counterexample.
---

Let `C_n<=F_2^(L_n)` be any binary code family with `dim C_n->infinity`
and distance at least two, including the all-local-dual DELLm family.  Use its
balanced presentation with all local dual rows, pair-sum faces, equality
copies, and the complete logical-pair overlay.

For arbitrarily large matrix dimensions `d_n` there are reflection tuples
`Q^(n)` such that

```text
 max_(presentation relator r)||r(Q^(n))-I||_2 ->0,        (HTD1)
 C^*(Q^(n))=M_(d_n).                                     (HTD2)
```

Indeed, choose `d_n` distinct codewords and put their coordinate signs on
the diagonal.  This is an exact code representation with simple joint
spectrum.  Choose one active coordinate `i_0`, leave every other coordinate
diagonal, and conjugate its reflection by an arbitrarily small generic
unitary.  Puncturing at `i_0` is injective because the code has no weight-one
word, so the unchanged coordinates still generate the full diagonal masa.
The perturbed `i_0` spectral projection can be chosen to have every
off-diagonal entry nonzero.  Its commutant inside that masa is scalar;
Burnside's theorem gives `(HTD2)`.

Assign the same perturbed reflection to every equality copy.  Equality is
exact.  Every bounded local-dual or pair-sum word differs from its exact
diagonal value by at most a fixed multiple of the perturbation, and the same
is true for every commutator face.  This proves `(HTD1)` even in maximum,
not merely averaged, defect.

Consequently there is no modulus `f_D(epsilon)->0` such that balanced defect
`epsilon` forces the central trace of irreducible blocks larger than `D` to
be at most `f_D(epsilon)`: in this construction that trace is one.  Nor can
the whole generated algebra satisfy any fixed subhomogeneous polynomial
identity approximately.  For every fixed `D`, along dimensions divisible
by `D+1`, `M_(d_n)` contains tensor amplifications of contractions on which
the standard polynomial `s_(2D)` has a fixed positive normalized-HS norm.

This does not refute synchronization or basin capture: the tuple is as close
to the original exact diagonal code tuple as the perturbation size.  It
proves that high-type mass is the wrong outlier statistic.  Any successful
argument must control the particular generators/corrections by metric
distance or bounded-complexity words, not demand a PI for every element of
their generated algebra.  A fixed finite word window is continuous at the
exact tuple and therefore cannot see the ill-conditioned matrix units which
witness `(HTD2)`.
