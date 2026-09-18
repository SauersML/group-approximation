# generic invertible automaton group over X={0,1,2}; states with explicit inverses.
# element = tuple of generator indices, rightmost acts first.  g(xw) = out_g(x) g|_x(w)
import itertools as it
class AG:
    def __init__(self, out, sec):
        # out[g]: tuple perm, sec[g]: tuple of states; build inverse states g+n
        n=len(out); self.n=n
        O=list(map(tuple,out)); S=list(map(tuple,sec))
        for g in range(n):
            inv=[0]*3
            for x in range(3): inv[out[g][x]]=x
            O.append(tuple(inv)); S.append(tuple(sec[g][inv[y]]+n for y in range(3)))
        self.O=O; self.S=S
        self.inv=[g+n for g in range(n)]+[g for g in range(n)]
    def red(self,w):
        r=[]
        for g in w:
            if r and r[-1]==self.inv[g]: r.pop()
            else: r.append(g)
        return tuple(r)
    def act(self,w,x):
        s=list(w)
        for j in range(len(w)-1,-1,-1):
            g=s[j]; s[j]=self.S[g][x]; x=self.O[g][x]
        return x,self.red(s)
    def act_path(self,w,v):
        y=[]
        for x in v:
            x,w=self.act(w,x); y.append(x)
        return tuple(y),w
    def invw(self,w): return tuple(self.inv[g] for g in reversed(w))
    def trivial(self,w,cap=2_000_000):
        w=self.red(w); seen={w}; todo=[w]
        while todo:
            u=todo.pop()
            for x in range(3):
                y,u2=self.act(u,x)
                if y!=x: return False
                if u2 not in seen:
                    seen.add(u2); todo.append(u2)
                    if len(seen)>cap: return None
        return True
    def eq(self,u,v): return self.trivial(u+self.invw(v))
