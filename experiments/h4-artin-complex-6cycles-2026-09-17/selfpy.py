import sys
from search import Setup
pre=sys.argv[1]; name=sys.argv[2]; K=int(sys.argv[3])
S=Setup(name,K); A=S.A
lines=open(pre+'.reps').read().split('\n')
def read(pos):
    c=int(lines[pos]); R=[]
    for l in lines[pos+1:pos+1+c]:
        v=list(map(int,l.split())); R.append((v[0],tuple(v[3:3+v[2]])))
    return R,pos+1+c
Ra,p=read(0); Rb,p=read(p)
def fmt(g): return "(%d,(%s))"%(g[0],"".join("%d,"%x for x in g[1]))
bad=0
for l in open('self_c.txt'):
    i,j,ab,iab,one,p1,p2=l.split()
    g=A.mul(Ra[int(i)],Rb[int(j)]); gi=A.inv(g)
    mine=(fmt(g),fmt(gi),'1',str(int(S.adj_YX(g))),str(int(S.adj_YX(gi))))
    if mine!=(ab,iab,one,p1,p2): bad+=1; print(l, mine) if bad<4 else None
print('mismatches',bad)
