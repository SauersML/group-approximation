---
rg: 2
id: free-shift-germ-reduction-and-local-certificates-proof
kind: route
title: Reduce the parity germs in two free products and retain every finite domain restriction needed for identity
target: free-shift-shell-relations-are-finitely-certified
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
  - shell-germ-group-has-index-two-fiber-product
artifacts:
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
---

Write R=P*<s>. Its homomorphism eta to Z kills P and sends s to 1.
The shell germ group Q has its known index-two subgroup R x_Z R.
The following calculations first use value oracles for nu and its
inverse, and for the word problem of P. In the effective case these
are the supplied terminating algorithms. An oracle run still makes
only finitely many queries in each terminating branch.

## Germ identities with explicit tail certificates

For a word in rho(S),tau and inverses, odd tau parity proves its
germ nonidentity. With even parity, the Schreier rewriting with
coset representatives 1,tau expresses it using

    rho_g=(lambda_g,1),
    tau*rho_g*tau^-1=(1,lambda_g),
    tau^2=(s,s).

It thus yields two words in P*<s>. Reduce each by combining adjacent
P syllables, deleting identity syllables in P, and combining integer
shift powers. Freeness of the canonical map to R makes the original
germ identity exactly when both resulting normal forms are empty.

When both are empty, this is more than a decision at the abstract
germ level. It gives a finite sequence of identities valid for
EVERY transported regular action lambda(P), because the only
free-product cancellations used are lambda_g*lambda_h=lambda_(gh)
and cancellations of powers of the partial shift. These require no
extra relation between lambda(P) and s. The parity formulas likewise
hold on cofinite domains for every enumeration.

Represent each intermediate map by its word together with finite
excluded-domain and excluded-range sets. They are effective for
lambda_g (both exclusions empty) and for s and s^-1. Under
composition, new exclusions are obtained by inverse images of finite
sets, using the available inverse algorithms. Each rewrite above is
pointwise valid after restricting to an explicitly known cofinite
domain. Pull these finite exclusions back through the preceding
partial maps and retain their union. Once the normal form is empty,
the original map is identity outside that finite union. Taking one
more than its largest element gives a tail bound; the two parity
coordinates give a shell-index bound in the same way.

This process uses only finitely many enumeration and inverse queries.
An inverse query nu^-1(n)=h is recorded by the same finite pair
nu(h)=n. Any other bijection preserving those pairs has the same
finite domain calculations, and the same tail certificate is valid
for it. No test of an infinite set of integers was used.

## Certify a whole shell word

For w=a_k*...*a_1, compute the finite candidate set

    F={(a_(j-1)*...*a_1)^-1(p): a_j is a shell letter}.

Points are finite binary words followed by infinitely many zeros.
Their generator images use finite prefix tables or one shell-index
evaluation. If w moves a point of F, it is nonidentity. Otherwise
follow the trajectory of each q in F and use prefix transporters
t_z(p)=z, with t_p=1, to normalize all letters near p.

A shell letter encountered at p remains that shell letter. Every
other normalized letter agrees near p with a known prefix shift.
The agreement is effective on a specified cone: away from p a
shell letter is a single suffix-preserving prefix replacement.
Compose these local representatives and retain their validity cones.
Pulling a desired tail cone 0^M*C back through a shell map uses only
the finitely many inverse indices rho^-1(j), j<M. Thus all required
neighborhood bounds use finite enumeration data.

Apply the preceding germ decision to each normalized word. A
nonidentity germ makes w nonidentity. An identity germ gives an
explicit cone U_q around q on which w is identity. On the compact
clopen complement D of the union of these cones, every shell letter
is applied to a compact clopen set avoiding p: its preimage was a
candidate in F, which was removed. Such a set meets only finitely
many shells. Compute the resulting finite prefix table for w on D
and compare it with identity. This decides the remaining case.

When w is identity, every germ reduction was to two empty formal
free-product normal forms, and the compact calculation also yielded
identity. Collect ALL finite enumeration pairs queried during this
run, including inverse queries, point trajectories, validity bounds,
and the final prefix table. This is sigma. Any mu extending sigma
repeats the same finite calculations. Its possibly nonfaithful
free-product map still satisfies all the formal identities used in
the positive branch, so every tail certificate and the final table
remain valid. Hence w is identity in E_mu.

For an arbitrary noncomputable nu or undecidable P, run this finite
argument with their value and word-problem oracles. It proves the
existence of sigma without asserting an algorithm for those oracles.
For computable nu and decidable P, all steps are algorithms, giving
the stated decision procedure and finite positive certificates.
