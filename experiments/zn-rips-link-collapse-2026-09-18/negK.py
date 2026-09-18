# negative control: on a start set f, try every single move "D u | w" and "K u | w" with w admissible (w != u, d <= r, w in hull(0,u,e_k))
# and tally the verifier V's verdicts.  Usage: python3 negK.py k r f V
import sys,subprocess,collections
k,r,f,V=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3],sys.argv[4]
P=[tuple(map(int,l.split())) for l in open(f) if l.strip()]
E=tuple([0]*(k-1)+[1])
d=lambda a,b:sum(abs(x-y) for x,y in zip(a,b))
def inh(w,x): return all(min(0,x[i],E[i])<=w[i]<=max(0,x[i],E[i]) for i in range(k))
cnt=collections.Counter(); n=0
for u in P:
  if u==E: continue
  for w in P:
    if w!=u and d(u,w)<=r and inh(w,u):
      for tag in 'DK':
        open('negK.cert','w').write(f"{tag} {' '.join(map(str,u))} | {' '.join(map(str,w))}\n")
        o=subprocess.run([V,str(k),str(r),f,'negK.cert'],capture_output=True,text=True).stdout.strip()
        cnt[(tag,o.split(':')[-1].strip() if 'FAIL' in o else 'ACCEPT')]+=1
print(cnt)
