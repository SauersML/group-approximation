# Odd native Whitehead factor GL7 audit (MSI, 2026-08-26)

The scoped executable was sent through the MSI wrapper; no local Python or
local build was run.

Command:

```text
/Users/user/msi-node/msi 'module load python3/3.12.4_anaconda2024.06-1_libmamba && PYTHONPATH=. python3 experiments/odd_native_s_factor_return_diamond_gl7_audit.py'
```

Output:

```text
odd native factors and constant swap close in GL7(F2); gauges killed; mark survives
```

The audit retains the complete old private-middle cross-return chart, the
fused native diamond, and the four non-equivariant arm matches.  It adds
`P=(6 9)`, verifies

```text
[P B' P^(-1),A]=x_87(s_00t_0),
[B,P A' P^(-1)]=x_78(s_0t_00),
J_1=FGF,
bar M=[P A' P^(-1),P B' P^(-1)]=x_69(1),
P=[A',B'] bar M [A',B'],
```

and checks that the marked child remains nonidentity.
