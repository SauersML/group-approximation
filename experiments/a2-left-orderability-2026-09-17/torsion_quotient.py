"""Emit a GAP script computing, for each presentation, the quotient of Gamma_T by the normal closure of
its torsion generators a_x ((x,x,x) in T).  If that quotient is finite, 'every action on R is trivial'
follows for free (finite-order homeomorphisms of R are trivial), so the SAT result is only meaningful
when this quotient is infinite.  Usage: torsion_quotient.py file > out.g ; gap -q out.g"""
import json, sys
Ts = json.load(open(sys.argv[1]))
print("SetInfoLevel(InfoWarning,0);")
for i, T in enumerate(Ts):
    n = max(max(t) for t in T) + 1
    rels = [f"f.{x+1}*f.{y+1}*f.{z+1}" for (x, y, z) in T]
    tors = [f"f.{x+1}" for (x, y, z) in T if x == y == z]
    print(f"f := FreeGroup({n}); G := f/[{', '.join(rels)}];")
    print(f"Q := f/[{', '.join(rels + tors)}];")
    print(f'Print("T{i} AbInv(G)=", AbelianInvariants(G), " AbInv(G/torsion)=", AbelianInvariants(Q), " |G/torsion|=", Size(Q), "\\n");')
print("QUIT;")
