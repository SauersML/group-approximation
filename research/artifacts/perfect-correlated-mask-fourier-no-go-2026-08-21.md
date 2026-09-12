# Correlated masks cannot give perfect long-code completeness and damping

Primary source architecture: Taller--Vidick, arXiv:2507.22444v2, Definition
4.1, Proposition 4.1 and Lemma 4.2.  This artifact promotes the earlier audit
in `notes/FALSE_PERFECT_COMPLETENESS_MASK_NO_GO.md` to a graph theorem and
states the mask constraints as an exact finite linear program.

## 1. The general correlated-mask linear program

Fix one sampled `W,U,C` in the long-code test.  A mask is a function

```text
mu:{+1,-1}^W -> {+1,-1}.
```

No independence assumption is made.  Let `D` be any finitely supported law
with probabilities `p_mu`.  For an honest long-code dictator indexed by a
satisfying atom `phi`, Taller--Vidick's tested parity is correct exactly when

```text
mu(phi)=1.                                                (1)
```

Let `S` be the union of atoms carrying nonzero projection in the honest
strategy or, for completeness on every satisfying dictator, take `S=C`.
The exact feasibility system for perfect completeness is

```text
p_mu >= 0,
sum_mu p_mu = 1,
sum_mu p_mu (1-mu(phi))/2 = 0       (phi in S).           (2)
```

Every term in the final sums is nonnegative.  Therefore (2) is equivalent to

```text
p_mu=0 whenever mu|_S is not identically one.             (3)
```

In the mask group under pointwise multiplication, the surviving subgroup

```text
H_S={mu:mu|_S=1}
```

is the common kernel, or annihilator, of the coordinate evaluation
characters indexed by `S`.

## 2. Forced Fourier coefficients

For a Fourier set `beta`, write

```text
chi_beta(mu)=prod_(phi in beta) mu(phi),
hat D(beta)=E_(mu~D) chi_beta(mu).
```

If `beta subset S`, then `chi_beta=1` on `H_S`.  Hence every solution of the
perfect-completeness linear program obeys

```text
hat D(beta)=1                         (beta subset S).     (4)
```

Correlations cannot change (4).  Among laws supported on `H_S`, Haar measure
is maximally damping: it makes every character nontrivial on `H_S` vanish.
But it still has value one on the whole annihilator `H_S^perp`, including all
`beta subset S`.

The conditioning lemma in the Taller--Vidick proof places every Fourier set
`beta` measured by the decoder inside the satisfying set `C`.  Therefore, if
perfect completeness is demanded for every satisfying dictator (`S=C`), the
maximally damping correlated mask still satisfies

```text
hat D(beta)=1
```

on every coefficient used by the decoder.  Noise outside `C` is exactly
invisible after conditioning.

## 3. The quantitative floor for smaller honest support

Suppose only one honest strategy with support `S` must be preserved.  A
Taller--Vidick-style Cauchy--Schwarz decoder needs a constant `c` satisfying

```text
|beta|^(-1/2) >= c |hat D(beta)|.                         (5)
```

Taking `beta=S` in (4)--(5) gives

```text
c^2 <= 1/|S|.                                            (6)
```

This is operationally sharp: after the Fourier measurement outputs `S`, the
published decoder chooses one of its elements uniformly and succeeds with
probability only `1/|S|` in the worst case.

If one source question has at most `m` supported honest answers, the `u`-fold
strategy has support at most `m^u`, and (6) gives at best `c^2<=m^(-u)`.
The source game itself has a classical random-guessing strategy of value at
least `m^(-u)`: fix a supported pair answer, and guess uniformly among the at
most `m^u` compatible single-question answers.  Consequently the decoded
lower bound cannot be made strictly larger than the universal source floor.
Parallel repetition shrinks both together and supplies no soundness
separation.

## 4. Exact boundary

The no-go covers every finite correlated mask law in the unchanged
Taller--Vidick three-query equation.  It also covers noise chosen as a
function of `W,U,C` and the source question, since the argument is pointwise
for each such conditioning.

It does not rule out changing the predicate, adding a non-XOR rigidity test,
or constructing a source whose odd-character relaxation is itself robustly
unsatisfiable.  Those changes are precisely new compiler content.  Within
the mask-only architecture, perfect completeness forces the mask into the
honest-spectrum annihilator and destroys the needed damping.

