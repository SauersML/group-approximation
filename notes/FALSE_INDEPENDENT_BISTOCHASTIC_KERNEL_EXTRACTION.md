# Separate bistochastic marginals are not the microstate coupling

Date: 2026-08-13

## Outcome

The convex statement in
`TRUE_ROBUST_PAIRED_QUOTIENT_HAMMING_FLOOR.md` is correct for **independent**
sampling from four doubly stochastic kernels, but that model is too strong to
be inferred from normalized Hilbert--Schmidt block masses alone.

Indeed, let `K : V x V -> [0,1]` and `L : W x W -> [0,1]` be doubly
stochastic.  If `v,w` are uniform and, conditionally on them, `x` and `y` are
sampled independently from `K(v,-)` and `L(w,-)`, then

```text
Pr[x=a,y=b]
  = (1/(|V||W|)) (sum_v K(v,a)) (sum_w L(w,b))
  = 1/(|V||W|).                                      (IBK1)
```

Thus `(x,y)` is already uniform on `V x W`.  For a perfect binary pairing on
two spaces of cardinality `N`,

```text
Pr[b(x,y)=1] = (N-1)/(2N).                           (IBK2)
```

The crossed error has this exact value without using either diagonal error.
The Lean theorems

```text
independentKernelOneMass_eq_oneSet_card
independentKernelOneMass_perfect
```

in `Leavitt/RobustPairedQuotientFloor.lean` encode the unnormalized form of
this observation.

## Why this does not finish the hyperlinear obstruction

A unitary between two equal-rank atomic decompositions does give a doubly
stochastic matrix of squared block Hilbert--Schmidt masses.  But a relation
involving two transported labels is measured by a **joint four-index
coupling**

```text
Q(v,w,x,y),                                           (IBK3)
```

not by the product of the two marginal kernels unless a separate
factorization theorem has been proved.  The two block-mass matrices determine
only the `x` and `y` marginals of `Q`.

This loss is real even for `V=W=F2` with `b(x,y)=xy`.  The two couplings

```text
Qdiag  = uniform on {(0,0),(1,1)},
Qanti  = uniform on {(0,1),(1,0)}                     (IBK4)
```

have identical uniform marginals.  Nevertheless `Pr_Qdiag[b=1]=1/2`, while
`Pr_Qanti[b=1]=0`.  Separate bistochastic marginals therefore cannot control
the crossed pairing phase.

## The corrected common-coupling gate

For the deterministic robust floor to average correctly, one needs a single
classical probability space carrying four random maps

```text
R0,R1 : V -> V,  L0,L1 : W -> W,                    (IBK5)
```

such that the three observed microstate couplings `(00),(11),(01)` are the
corresponding pairwise marginals, up to vanishing total error.  The diagonal
errors then repair the relevant maps to permutations inside each atom of the
latent law.  Equivalently, the pairwise transports must admit one common
latent-map lift.  Once that lift exists, average
`robust_deterministic_floor` over the common latent variable and obtain the
universal floor.

This averaging step is formalized as
`robust_floor_of_common_latent_maps`.  Its three weighted error terms all use
the same finite latent variable, so the compatibility assumption is present
in the theorem statement rather than hidden in a product of marginals.

Requiring the latent maps themselves to be permutations is a stronger
sufficient condition.  In that case the crossed one-density is already fixed
at every atom, so the diagonal errors are unnecessary.

Four unrelated Birkhoff decompositions do not supply this.  Choosing them
independently replaces the observed joint couplings by product couplings;
choosing them pairwise may produce incompatible marginals with no joint lift.
This is the classical marginal problem, and in the present tracial setting
the Pauli/Clifford models show that noncommutative correlations are a genuine
possibility rather than a technical nuisance.

The live analytic statement is therefore:

> Extract common perfect-pairing coordinates and prove that their three
> normalized-HS transport couplings asymptotically admit a common classical
> latent-map lift.

This is narrower and more accurate than general coordinate-commutant
recovery, but stronger than extracting four doubly stochastic block-mass
matrices.  Any future proof must expose the factorization/classicalization
mechanism explicitly; silently multiplying marginal kernels would assume the
missing theorem.

There is, however, no separate four-way compatibility obstruction after
pairwise laws on whole maps have been extracted.  The three contexts form a
tree and compatible shared marginals glue exactly.  See
`TRUE_TREE_GLUE_COMMON_TRANSPORT_LAWS.md`.  The live issue is therefore
pairwise classicalization at whole-map level, not synchronization of three
already-classical edge laws.
