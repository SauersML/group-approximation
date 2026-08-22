---
rg: 2
id: infinite-character-actor-word-energy-interface
kind: claim
title: Make finite word defects control an infinite character-orbit transport energy
---

OPEN.  Construct one finitely presented actor/module packet whose exact
elementary-abelian module has a nontrivial character set `Omega` satisfying
the infinite Schreier gap `(ISC1)`, and prove that normalized-HS relator
defect controls the summed PVM transport energy `(ISC2)` with a
dimension-independent modulus.

The packet must also exclude fixed or finite character classes which can
carry the D8 seed.  For a permutation module this usually requires removing
the constant character (for example by an augmentation relation); merely
using a transitive nonamenable actor is not sufficient.

Together with `one-seed-infinite-character-expansion-collapses-mark`, this
would be a one-scale capacity backend: no unbounded family, mixed Weyl table,
or post hoc choice of `n` remains.

## Exact reduction to uniform whole-module covariance

Once a same-dimensional exact spectral representation of the whole module
has been decoded, no further infinite-resolution inequality is needed.  Let

```text
rho(m)=sum_(chi in Omega_0) chi(m)P_chi
```

have finite spectral support `Omega_0`, let `C_s` represent one actor
generator, and put

```text
d_s(m)=||C_s rho(m)C_s^*-rho(sm)||_2,
E_s=sum_chi ||C_sP_chi C_s^*-P_(s chi)||_2^2.          (IWE1)
```

> **Whole-module averaging identity.**  There is a finite probability
> average over module elements, depending only on the finite occurring
> character support, for which
>
> ```text
> E_s=Average_m d_s(m)^2.                              (IWE2)
> ```

Indeed the block expansion from
`finite-covariance-energy-sees-only-character-restrictions` gives

```text
d_s(m)^2
 =4 sum_(chi,psi)
    1_(psi(m)!=(s chi)(m)) ||P_psi C_s P_chi||_2^2.   (IWE3)
```

Only finitely many difference characters
`psi(s chi)^(-1)` occur.  Map `M` to their finite joint sign quotient and
average uniformly over its image.  Every nontrivial difference character is
balanced there, while the trivial one is always `+1`.  Averaging `(IWE3)`
therefore gives

```text
Average_m d_s(m)^2
 =2 sum_(psi!=s chi)||P_psi C_sP_chi||_2^2=E_s,       (IWE4)
```

the last equality being `(FCR2)`.  In particular,

```text
E_s<=sup_(m in M)d_s(m)^2.                             (IWE5)
```

Consequently `(ISC2)` follows with no loss once finite presentation defect
produces:

1. one exact finite-support PVM for the whole module; and
2. a dimension-independent bound

   ```text
   sup_(m in M)d_s(m)<=omega(delta)                    (IWE6)
   ```

   for every actor generator.

This identifies the existing claim
`finite-presentation-must-expose-whole-module-with-uniform-defect` as the
exact remaining analytic gate, rather than an additional downstream helper.
Uniform all-pairs module multiplication permits global abelian rounding, and
uniform all-module actor covariance then feeds `(IWE2)`.

The word **uniform** in `(IWE6)` is load-bearing.  For any fixed finite set
of tested module words, distinct characters collide on their restriction to
that set; swapping the corresponding spectral blocks gives zero tested word
defect and positive `E_s`.  Hence neither the known finite covariance words,
finite-depth conjugacy recursion, nor the exact actor/Schreier gap proves
`(IWE6)`.  A bounded compiler must make the finite relators control all
virtual module words with one modulus, or use a genuinely matrix-only
infinite-resolution square function.  The current actor and character nodes
do not provide either mechanism.

## Attempts

- **Regular permutation module.**  The constant character is actor-fixed and
  can support a bounded exact model unless it is quotiented out.
- **Use group expansion without the energy interface.**  Word covariance on
  a few module generators does not automatically bound the sum over all
  spectral characters.  More sharply,
  `finite-covariance-energy-sees-only-character-restrictions` computes the
  exact block quadratic forms: a finite set `T` sees only restriction to
  `sT`, and every infinite character set has invisible same-label fibers.
  Thus finite-depth conjugacy recursion plus Schreier expansion cannot close
  the interface.  Identity `(IWE2)` shows the exact escape from this no-go:
  uniform covariance on the whole module, not another finite test set.  One
  fixed defect must encode that uniform control/infinite spectral resolution,
  or matrix-only rigidity must forbid motion inside those fibers.
- **Finite quotient modules.**  These return to the finite-orbit capacity
  theorem and require an unbounded family.
- **Package infinitely many characters into finitely many bounded diagonal
  operators.**
  `finite-bounded-spectral-probes-cannot-resolve-infinite-character-transport`
  gives the exact block criterion: such probes control fine transport if
  and only if their finite-dimensional bounded feature map is uniformly
  discrete.  An infinite character set never is.  Thus Fourier series,
  heat filters, or resolvents do not constitute the missing
  infinite-resolution square function.  A surviving square function must
  authenticate non-diagonal orthogonal domains through mixed words.
