# Sound partial Knuth-Bendix (shortlex) for triangle-presentation groups.
# Letters: x in 0..n-1 is a_x, x+n is a_x^{-1}. Every rule lhs->rhs is an equality in the group.
import json, sys
def inv_letter(c,n): return c+n if c<n else c-n
def inv(w,n): return tuple(inv_letter(c,n) for c in reversed(w))
def key(w): return (len(w),w)
class RWS:
    def __init__(self,n,relators):
        self.n=n; self.rules={}
        for x in range(n): self.add((x,x+n),()); self.add((x+n,x),())
        for r in relators:
            self.add_relator(tuple(r))
    def add_relator(self,r):
        n=self.n
        for rr in (r,inv(r,n)):
            L=len(rr)
            for i in range(L):
                c=rr[i:]+rr[:i]
                for k in range(1,L):  # c = u v =1 -> u = v^{-1}
                    u=c[:k]; v=inv(c[k:],n)
                    self.add_pair(u,v)
    def add_pair(self,u,v):
        u=self.reduce(u); v=self.reduce(v)
        if u==v: return False
        if key(u)<key(v): u,v=v,u
        self.add(u,v); return True
    def add(self,l,r):
        self.rules[l]=r
    def reduce(self,w):
        w=list(w); rules=self.rules
        maxl=max((len(l) for l in rules),default=0)
        i=0
        # simple stack-based reduction
        out=[]
        stack=list(reversed(w))
        while stack:
            out.append(stack.pop())
            for L in range(1,min(maxl,len(out))+1):
                t=tuple(out[-L:])
                if t in rules:
                    del out[-L:]
                    stack.extend(reversed(rules[t]))
                    break
        return tuple(out)
    def complete(self,maxlen,maxrounds=50,verbose=True):
        for rd in range(maxrounds):
            new=0
            ls=list(self.rules.items())
            for l1,r1 in ls:
                if self.rules.get(l1)!=r1: continue
                for l2,r2 in ls:
                    if self.rules.get(l2)!=r2: continue
                    for k in range(1,min(len(l1),len(l2))):
                        if l1[-k:]==l2[:k]:
                            if len(l1)+len(l2)-k>maxlen: continue
                            w1=r1+l2[k:]; w2=l1[:-k]+r2
                            if self.add_pair(w1,w2): new+=1
            # interreduce
            rs=dict(self.rules); self.rules={}
            for l,r in sorted(rs.items(),key=lambda t:key(t[0])):
                l2=self.reduce(l); r2=self.reduce(r)
                if l2!=r2:
                    if key(l2)<key(r2): l2,r2=r2,l2
                    self.rules[l2]=r2
            if verbose: print("round",rd,"new",new,"rules",len(self.rules),file=sys.stderr)
            if new==0: break
        return self
