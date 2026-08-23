# Culf--Mastel to singleton synchronization: exact normal forms

Source: Culf--Mastel, *RE-completeness of entangled constraint satisfaction
problems*, arXiv:2410.21223v2, especially Definition 3.3, Theorem 7.31,
Proposition 8.9, Theorem 8.10, and Corollary 4.18.  The supplied source PDF
`/Users/user/Downloads/2410.21223v2.pdf` was checked directly and has SHA-256
`a7e05579303893acb2b4d84e0c8020cb1e9d2fbe43bdc56d9e3af3447378ab98`.
The supplied integration archive has SHA-256
`4d43cbdb0ac679896497d423fc0ccabf73d2f632614445c33e8eddd162daeb67`.

## Exact singleton synchronization

For positive exactly-one-`k`, the constraint-variable incidence defect is
exactly `||Q_j-P_j||_2^2`, with no cross-endpoint commutation assumption.
More generally, for any nonempty proper `B subset Z_k`, the binary relation

```text
D_(j,B)=({j}xB) union ((Z_k\{j})x(Z_k\B))
```

has losing energy

```text
||Pi_j(y)-sum_(b in B)Pi_b(x)||_2^2.
```

The source-to-target split and target-to-source coarse-graining preserve the
defect exactly.  The paper uses `B=Z_k\{0}`; choosing `B={0}` compares one
atom to one atom.

Positive exactly-one-`k` is Boolean TVF and NP-complete for every `k>=3`.
Theorem 7.31 and the exact singleton compiler therefore make the fixed
`k`-relation language `SYNC_k` RE-hard at perfect versus constant gap.  The
finite expansion of Corollary 4.18 is computable and sufficient for reverse
Kleene.

## Four outcomes

After a fixed identification `Z_4=F_2^2`, every four-outcome PVM is generated
by two commuting involutions `A,B`; its atom reflection is

```text
R_(u,v)=1/2(1-(-1)^uA-(-1)^vB-(-1)^(u+v)AB).
```

Every `SYNC_4` edge has exactly one quarter of
`||R_j(y)R_0(x)-1||_2^2` as its losing energy.

The tautological `B_4` signed-permutation representation makes these atom
reflections literal coordinate signs, but its irreducibility forces equal
coordinate multiplicities and is therefore too restrictive for arbitrary
perfect source PVMs.  The correct rank-free packet is the rational corner of
`Q[(C_2)^4]` supported on the four one-negative characters.  It is `Q^4`,
has canonical trace `1/4`, admits arbitrary atom multiplicities, and makes
each atom reflection the restriction of one literal group generator.

The local compiler is therefore complete.  The remaining group-level cell
is global: identify these rank-free local corners on one surviving canonical
carrier around every incidence cycle.  Independent transports retain an
arbitrary multiplicity holonomy, so the missing return must be genuinely
nontransport.
