# Short exact relations of the dual group B = <b0,b1,b2> (B332V) and a GAP file testing whether
# H = phi_v(St_B(v)) is proper in the finitely presented group A_B = <b | relations of length <= L>.
import sys, itertools as it
from agrp import AG
L=int(sys.argv[1]); v=int(sys.argv[2])
G=AG([(1,2,0),(1,0,2),(1,0,2)],[(1,1,1),(0,2,2),(2,0,0)])
inv=G.inv
rels=[]; seen=set()
def canon(w):
    rs=[w[i:]+w[:i] for i in range(len(w))]
    iw=G.invw(w); rs+=[iw[i:]+iw[:i] for i in range(len(w))]
    return min(rs)
for l in range(1,L+1):
    for w in it.product(range(6),repeat=l):
        if any(w[i+1]==inv[w[i]] for i in range(l-1)) or (l>1 and w[0]==inv[w[-1]]): continue
        c=canon(w)
        if c in seen: continue
        seen.add(c)
        r=G.trivial(w,cap=200000)
        if r is None: print('undecided',w); continue
        if r: rels.append(c)
    print('len',l,'rels',len(rels),flush=True)
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
        y,s=G.act(w,v); assert y==v
        if s: sch.add(s)
nm=lambda g:'b%d'%g if g<3 else 'b%d^-1'%(g-3)
gw=lambda w:'*'.join(nm(g) for g in w)
with open('bobs_%d_%d.g'%(L,v),'w') as f:
    f.write('F:=FreeGroup("b0","b1","b2");; b0:=F.1;; b1:=F.2;; b2:=F.3;;\n')
    f.write('R:=[%s];;\n'%',\n'.join(gw(r) for r in rels))
    f.write('A:=F/R;; ag:=GeneratorsOfGroup(A);;\n')
    f.write('Hw:=[%s];;\n'%','.join(gw(s) for s in sorted(sch,key=len)))
    f.write('H:=Subgroup(A,List(Hw,w->MappedWord(w,GeneratorsOfGroup(F),ag)));;\n')
    f.write('c1:=ag[2]*ag[1]^-1;;\nLI:=LowIndexSubgroupsFpGroup(A,H,6);;\n')
    f.write('Print("L=%d v=%d #rels ",Length(R)," #subgroups of index<=6 containing H: ",Length(LI)," indices ",List(LI,U->Index(A,U))," not containing c1: ",Number(LI,U->not c1 in U),"\\n");\nQUIT;\n'%(L,v))
print('rels',[''.join(map(str,r)) for r in rels])
# every relation found is a consequence of c1^2=c2^2=(c1c2)^2=1, i.e. trivial in V4 * Z = <c1,c2> * <b0>:
# b1 = c1 b0, b2 = c2 b0.  Normal form: syllables alternate between V4 (xor of 2-bit vectors) and Z (integers).
def vz(w):
    img={0:[('Z',1)],1:[('V',(1,0)),('Z',1)],2:[('V',(0,1)),('Z',1)],
         3:[('Z',-1)],4:[('Z',-1),('V',(1,0))],5:[('Z',-1),('V',(0,1))]}
    st=[]
    for g in w:
        for f,x in img[g]:
            if st and st[-1][0]==f:
                y=st.pop()[1]; y=(y[0]^x[0],y[1]^x[1]) if f=='V' else y+x
                if y not in ((0,0),0): st.append((f,y))
            else: st.append((f,x))
    return st==[]
print('all relations of length <=',L,'trivial in V4*Z:',all(vz(r) for r in rels))
