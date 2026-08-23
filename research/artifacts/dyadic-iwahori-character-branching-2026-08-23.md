# Small-level dyadic Iwahori character branching

Date: 2026-08-23.

The reproducible MSI experiment
`experiments/dyadic_iwahori_character_branching.py` enumerates
`SL_2(Z/2^a)`, its conjugacy classes, and its complex character table from
the commutative class algebra.  It then restricts the level-`a` upper chart
and level-`a+1` opposite chart to their common finite Iwahori quotient and
computes physical common dimensions after decomposing through the Iwahori
irreducibles.

The runs used one process on `acn112` and no local computation:

```text
$ python3 dyadic_iwahori_character_branching.py 2
orders G2=48 G3=384 H=128
class counts 10 30 38
OF->OB rows (source id,dim,target id,dim,common physical dim):
1 1 5 3 1
2 1 20 3 1
4 2 5 3 1
4 2 20 3 1

$ python3 dyadic_iwahori_character_branching.py 3
orders G3=384 G4=3072 H=1024
class counts 30 76 124
OF->OB rows (source id,dim,target id,dim,common physical dim):
9 2 55 6 2
11 4 46 6 2
11 4 54 6 2
12 4 35 6 2
12 4 55 6 2
22 2 46 6 2
24 2 54 6 2
26 2 35 6 2
```

At both adjacent levels every displayed `O_B` target has dimension three
times its common `ell_B` edge slot.  This is a computational sanity check
for the exact Clifford-theory proof in
`adjacent-clifford-rank-deficit-proof`, not an input to that proof.

