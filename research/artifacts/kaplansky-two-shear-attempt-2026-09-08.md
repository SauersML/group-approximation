# Two-shear attempt at a literal Kaplansky counterexample

This records an exact construction criterion and a completed negative finite
search. No inverse pair was found and neither Kaplansky nor Gottschalk is
resolved. All executable checks ran on MSI, using one process at a time.

## The candidate and its exact certificate

Work in S=F_2[Q], where Q is the binary Leavitt unit group, and write
evaluation:S->L for the ring homomorphism sending each group label to its
Leavitt unit. Let e=[g]+[g^2], where g has order three and e evaluates to
p=s_0 t_0. Set q=1+e. The prefix permutation u sends 0 to 00, 10 to 01,
and 11 to 1. Thus u p u^-1=p00<p.

For a fixed evaluation-kernel element K, set

    N2=q K e,       W0=(1+N2)[u].

Since eq=0, N2^2=0 and W0 has the explicit inverse [u^-1](1+N2).
For an unknown parameter a in S set N1=q a e. The single linear equation

    q W0 N1 = q W0 e                                      (1)

means that W=W0(1+N1) satisfies qWe=0. It follows that

    A=eWe,       B=eW^-1e=eW0^-1e,       BA=e.              (2)

Indeed We=eWe, so eW^-1eWe=e. The factor B is fixed independently of a
because eN1=0. Its evaluation is b0=p u^-1 p. The nonzero idempotent
r=p+p00 satisfies b0 r=0. Therefore AB=e is impossible: its evaluated
identity would give r=eval(A)b0 r=0. Padding A and B by q would give the
literal scalar counterexample

    (B+q)(A+q)=1,       (A+q)(B+q)!=1.

There is consequently NO need to require eval(N1)=0. Removing that
unnecessary condition enlarges the solve. The earlier, stronger assertion
eval(AB)=p00 is not used in the enlarged search; only AB!=e is needed.

The implemented fixed K=(1+[a1]+[b1]+[a2]+[b2])D uses the four established
atlas generators and D=(1+[p1])(1+[p4]), whose Leavitt evaluation is zero.
Here p1,p4 mean the indexed transvections in the executable atlas, not
prefix projections. The resulting N2 has 108 terms and B has 220 terms.
The exact JSON certificate supplies group elements l,r such that all five
terms l q_i r survive in B for q_i=1,a1,b1,a2,b2. Their ratios generate
r^-1 Q r=Q. Thus the fixed factor passes the support-subgroup test that
excluded earlier amenable and virtually free candidates.

The single-shear version with N2=0 is excluded at every parameter support:
B=e[u^-1]e lies in a locally-finite-by-cyclic subgroup algebra. Conditional
expectation of any proposed inverse into that subgroup, followed by direct
finiteness and uniqueness, would force its proper coisometric evaluation
to be invertible. That version was not searched.

## Completed computation and performance repair

The initial two-shear implementation stopped itself after 23.56 seconds at
30 of 109 columns. This was incomplete, not a negative solve; the original
partial JSON is retained as such.

The bottleneck repeatedly rescanned an entire expanded prefix table after
contracting just one sibling pair. A worklist now visits a newly formed
parent directly. It preserves the same exact reduced keys. Comparison with
the original reducer passed 391 cases: expanded identities, deterministic
mixed-prefix sums, all 144 atlas-generator products, and all 109 elements
of the radius-two atlas ball. That check took 0.49 seconds on MSI; the
reduction portion was 25.3 times faster on its check set.

With the worklist, the complete 109-column system including the old
evaluation constraint finished in 12.19 seconds without a solution. After
removing that constraint, the enlarged system finished in 13.63 seconds:
63,492 literal group-product coordinates, column rank 102, no solution.
No radius-three solve was started. This excludes only the stated fixed K
and parameter universe, not arbitrary K, arbitrary support, or the general
one-sided inverse problem.

The executable rechecks any prospective hit using nonmemoized literal
group-algebra multiplication, both inverse identities for W, qWe=0, BA=e,
AB!=e, and both padded products. No hit reached that verification stage.

Files:

- experiments/kaplansky_prefix_corner_shear_search.py
- experiments/kaplansky_asymmetric_atlas_search.py
- experiments/verify_prefix_key_worklist.py
- research/artifacts/kaplansky-prefix-corner-shear-2026-09-08.json
- research/artifacts/kaplansky-prefix-corner-radius-two-2026-09-08.json
- research/artifacts/kaplansky-prefix-worklist-validation-2026-09-08.json

## Nonlinear cellular-automaton seed checks

The independent Gottschalk lane tested M={1,a1,b1,a2,b2} and decoder memory
M^-1. Both 5-by-5 composition rectangles have the same 21 product classes
as their realization in A8*A8. Every putative pair of local rules with
decoder-encoder composition equal to the identity would therefore transfer,
including its reverse defect, to that surjunctive virtually free group.
No finite alphabet or nonlinear truth tables on these memories can work.

A second candidate added B=[q13(f),q32(F)] to the encoder and
A=[q13(e),q32(E)], C=[q13(1),q32(1)] to the decoder. Although AB=C is a
mixed Leavitt identity, both composition rectangles still match a
realization in (A8*A8)*V4, with fresh A,B and C=AB. Each rectangle has 36
product classes. This candidate is excluded for the same reason. Merely
expressing a memory address as a long word does not force that word's
internal multiplication relations in the composition rectangle.

These exact checks each took about 1.1 seconds on MSI and avoided a truth
table search on impossible windows. Their script and complete partitions
are experiments/gottschalk_atlas_first_seed.py,
experiments/gottschalk-atlas-first-seed-2026-09-08.json, and
experiments/gottschalk-atlas-fresh-v4-seed-2026-09-08.json.
