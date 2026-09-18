import json, sys, time
from search import Setup
name=sys.argv[1]; Lu=int(sys.argv[2]); K=int(sys.argv[3]); nb=int(sys.argv[4])
recs=[json.loads(l) for l in open('results.jsonl') if json.loads(l)['group']==name]
rec=recs[-1]
S=Setup(name,K); W,A=S.W,S.A
RU=S.reps(S.X,Lu)
print(name,'RU',len(RU))
def T(x): return (x[0],tuple(x[1]))
for t in rec['bad'][:nb]:
    a,b,c,d=[T(x) for x in t]
    abc=A.mulmany(a,b,c)
    # recheck cycle at larger K
    print('cycle', a,b,c,d, 'x1~y3', S.adj_XY(A.mul(abc,d)), 'triv', S.adj_YX(abc), S.adj_XY(A.mul(a,b)), S.adj_XY(A.mulmany(b,c,d)))
    found=None
    for (u,pu) in RU:
        ui=A.inv(u)
        if S.adj_YX(A.mul(ui,a)) and S.adj_YX(A.mul(ui,abc)):
            found=u;break
    print('  qc', found)
