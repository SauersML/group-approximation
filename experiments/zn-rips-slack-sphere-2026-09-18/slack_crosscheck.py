# Independent numpy re-check of slack_crit.cpp at one (n, r) whose unbalanced partitions all have n parts.
# The unbalanced partitions are passed in (from sphere_nop results). For each x and each position k of the last
# lattice coordinate: the slack-1 candidates y (with y_k >= 1) are filtered in a vectorized pass, and each candidate
# is tested against ALL signed arrangements z of every unbalanced partition with z_k > 0.
# Usage: python3 slack_crosscheck.py n r "a,b,c,..;d,e,f,..;..."
import sys, itertools, numpy as np
n=int(sys.argv[1]); r=int(sys.argv[2]); U=[tuple(map(int,p.split(','))) for p in sys.argv[3].split(';')]
assert all(len(p)==n and sum(p)==r for p in U)
S=np.array(list(itertools.product([1,-1],repeat=n)))           # all sign vectors
Z=[]
for p in U:
    perms=np.array(sorted(set(itertools.permutations(p))))
    Z.append((perms[:,None,:]*S[None,:,:]).reshape(-1,n))
Z=np.unique(np.concatenate(Z).astype(np.int16),axis=0)
bad=0
for p in U:
    x=np.array(p); ax=S@x
    Y=np.array(list(itertools.product(*[range(v+1) for v in p])))
    tot=Y.sum(1); Y=Y[(tot>0)&(tot<r)]
    ok_slack=np.all(Y@S.T <= np.maximum(1,ax)[None,:],axis=1); Y=Y[ok_slack]
    dx=np.abs(Z-x).sum(1)
    for k in sorted(set(range(n)), key=lambda i:i):
        if k>0 and p[k]==p[k-1]: continue
        Zk=Z[(Z[:,k]>0)&(dx<=r)]
        Yk=Y[Y[:,k]>=1]
        order=np.argsort(np.abs(Yk.sum(1)-r/2),kind='stable')   # a different search order from slack_crit
        found=None
        for j in order:
            if not np.any(np.abs(Zk-Yk[j]).sum(1)>r): found=Yk[j]; break
        print(p,k,'y=',None if found is None else tuple(found)); bad+= found is None
print(f"n={n} r={r} unbalanced={len(U)} without-y={bad}")
