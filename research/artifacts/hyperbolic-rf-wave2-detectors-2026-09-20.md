# Wave 2: an explicit perfect first kernel blocks solvable detector refinements

The residual-finiteness problem remains open. This pass reconstructed a
fully specified perfect-vertex triangle and obtained a stronger obstruction
than the old mod-5 first-homology data: its canonical torsion-free kernel
has **zero integral abelianization**. Consequently no finite quotient
refinement over this particular first quotient can have a nontrivial
solvable kernel, even when that kernel uses several primes. The same is
true of every nonzero central five-twist.

The calculation is exact integer computation, independently reviewed and
fully replayed, with a separate normal-form recheck; it is not Lean
certification. The second-quotient matrix certificate was also independently
reviewed and rerun. See `hyperbolic-rf-wave2-audit-2026-09-20.md`, Section 7
and its subsequent review of the second quotient.

## The pinned triangle

In `Q=PSL_2(F_19)` take the classes of

```
x_12 = [[2,11],[16,3]],
x_13 = [[5,11],[4,9]],
x_23 = [[6,15],[12,8]].
```

All three have order five. Each pair generates all of `Q`, which has
3420 elements. Use three copies of `Q` as the vertex groups and glue
the indicated cyclic groups as edges, with trivial face group. The
canonical colimit map `Λ -> Q` is the identity on each vertex.

Exact enumeration gives link girths `(6,8,6)`. The half-girth reciprocal
sum is `1/3+1/4+1/3=11/12<1`, so the usual triangle-of-groups development
is negatively curved and `Λ` is hyperbolic. The kernel `N` of the
canonical quotient acts freely on that contractible development.

Unlike the earlier seeded GAP output, this record includes the actual
edge generators. It is a specified member of the same family, not a
claim that it coincides with one of the old randomly generated triples.

## Exact integral calculation

The finite classifying complex `N\X` has three vertices, 2052 edges,
and 3420 faces. The boundary of a face indexed by `g in Q` consists of
the three right cosets containing `g`, with signs `+,-,+`. Collapse
one edge of type12 and one of type13, a spanning tree on the three
vertices. The resulting `2050 by 3420` integer matrix presents
`H_1(N;Z)`.

The source script performs 1962 unimodular unit-pivot eliminations.
Its residual is an explicit `88 by 1458` integer matrix. FLINT gives:

- Smith normal form: 88 unit invariant factors, with no nonunit factors.
- Hermite normal form of the transpose: `[I_88;0]`, checked entry by entry.

It follows that `H_1(N;Z)=0`. The Euler characteristic is 1371, and
second homology is a subgroup of a free group of cellular chains, so
`H_2(N;Z)=Z^1370`.

Executable sources and evidence:

- `experiments/hrf-wave2-detectors-2026-09-20/psl19_kernel.py`
- `experiments/hrf-wave2-detectors-2026-09-20/psl19_kernel_result.json`
- `experiments/hrf-wave2-detectors-2026-09-20/psl19_residual.json`
- `experiments/hrf-wave2-detectors-2026-09-20/psl19_kernel.out`
- the adjacent `README.md` pins Python 3.13.13 and python-flint 0.9.0.

The calculation enumerates a finite group and performs integer lattice
operations. It does not sample finite quotients and extrapolate their
behavior. Both normal-form computations use FLINT, so they are not
two independent proof kernels. The reviewer also checked the sparse
elimination code and ran the Hermite calculation independently.

## What perfectness excludes

For any factorization `Λ ->> F ->> Q` of the canonical map, the kernel
of `F -> Q` is an image of `N`. It is perfect, hence cannot be a
nontrivial solvable group. This rules out all solvable-kernel refinements
of this first quotient, including mixed-prime solvable extensions.

There is a corresponding statement for twists. The vertices and `Q`
have `H^2(-;F_5)=0`, and `N` has `H^1(N;F_5)=0`. The reviewed
restriction-injectivity result therefore makes every nonzero twist
remain nonzero on `N`. If `N_c` is its central `C_5` extension, then
`N_c` is perfect too: otherwise its abelianization would be `C_5`,
providing a retraction onto the central kernel and thus a splitting.

Consequently a quotient `Λ_c ->> F ->> Q` with solvable kernel over
`Q` kills the entire `N_c`, including its central `C_5`. Such a quotient
cannot detect any nonzero twist.

Cairn nodes:

- [[wave2-detector-psl19-perfect-first-kernel]] and its proof.
- [[wave2-detector-psl19-no-solvable-refinements]] and its proof.

## The remaining detector shape

An exact second calculation supplies a concrete nonsolvable refinement:
[[wave2-detector-psl19-has-second-simple-quotient]]. Set
`u=[[1,5],[9,17]]` and `v=[[1,14],[12,13]]` in `PGL_2(19)`. Identity
on vertex1 and conjugation by `u,v` on vertices2,3 agree on every edge.
This defines a second quotient to `Q`; paired with the canonical map,
it is surjective onto `Q×Q` by the subdirect-product alternative. In
particular the perfect first kernel has a quotient `Q` and is not
quotientless.

The matrix certificate is in `psl19_quotient_census.py` and its result
JSON in the experiment directory. The exhaustive20-by20 centralizer
search finds exactly two normalized PGL-conjugation configurations,
including the identity. The theorem only uses the explicit second
configuration, not an assertion classifying every abstract map.
The second kernel has index `3420²`; its first homology was not
computed. The product quotient still has no nonzero central five-twist
discrepancy, by the earlier composition-factor theorem.

This does not eliminate all finite perfect quotients with a solvable
radical. A perfect group may have a nontrivial solvable radical and
a nonabelian simple quotient. The result says that, relative to this
canonical first quotient, a detector must first introduce a nonsolvable
image of `N_c`. It does not forbid a solvable radical within that image.

Any detector that does not initially factor through the canonical `Q`
can be combined with the canonical map by taking a product image.
The resulting kernel over `Q` is then a nontrivial finite perfect
image of `N_c`; it must be nonsolvable. The earlier all-PSL2
composition-factor obstruction remains available but does not classify
these perfect images. A successful detector may therefore need both
new nonsolvable finite quotient data and a suitable modular layer.

No such detector was constructed in this pass, and no theorem controlling
all those remaining finite quotients was proved. The advance is a
specific exact kernel computation and the removal of the whole solvable
refinement class for that pinned triangle.
