import sys, itertools as it
from aut import AUT
from agrp import AG
out,sec=AUT['332V']; t=out[3]
Bo=[tuple(sec[d][x] for d in range(3)) for x in range(3)]
Bs=[tuple(t[out[d][x]] for d in range(3)) for x in range(3)]
G=AG(Bo,Bs)
def schsec(v):
    gens=[(g,) for g in range(6)]
    rep={v:()}; todo=[v]
    while todo:
        u=todo.pop()
        for g in gens:
            u2=G.act(g,u)[0]
            if u2 not in rep: rep[u2]=g+rep[u]; todo.append(u2)
    sch=set()
    for u,r in rep.items():
        for g in gens:
            u2=G.act(g,u)[0]
            w=G.red(G.invw(rep[u2])+g+r)
            y,s=G.act(w,v)
            if s: sch.add(s)
    return sorted(sch,key=len)
f=open('bH.g','w')
for n in range(1,7):
    W=list(it.product(range(3),repeat=n)); idx={w:i for i,w in enumerate(W)}
    P=lambda w:'PermList([%s])'%','.join(str(idx[G.act_path(w,x)[0]]+1) for x in W)
    f.write('B:=Group(%s);;\n'%','.join(P((g,)) for g in range(3)))
    for v in range(3):
        f.write('H:=Group(%s);;\n'%','.join(P(s) for s in schsec(v)))
        f.write('Print(%d," v=",%d," |B|=",Size(B)," [B:H]=",Index(B,H)," b0,b1,b2 in H: ",List(GeneratorsOfGroup(B),g->g in H)," H transitive: ",IsTransitive(H,[1..%d]),"\\n");\n'%(n,v,3**n))
f.write('QUIT;\n')
