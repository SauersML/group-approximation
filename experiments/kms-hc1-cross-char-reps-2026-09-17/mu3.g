# p=3 instance of mu.g (see its header). The p=3 tower agrees with I_1 through class 5 (pqA2.out), so img_3(I_1)=img_3(Gamma).
# Q_k = Gamma^A2_p / P_k(Gamma) (equal to I_1/P_k(I_1) for k<=31 by pqdeep2.out).
# With F free on a,b,c and R = <<rels>> P_k(F), the p-covering group Q_k* = F/[R,F]R^p is
# F / <<[rel,x], rel^p>> P_{k+1}(F), i.e. the class-k p-quotient of <a,b,c | [rel,a],[rel,b],[rel,c],rel^p>.
# dim H^2(Q_k,F_p) = log_p|Q_k*| - log_p|Q_k|.
# ker(H^2(Q_k) -> H^2(I_1)) has dimension gr_k(I_1) = dim P_k/P_{k+1}, so
# img_k := dim H^2(Q_k) - gr_k is the dimension of the image of inflation from Q_k in H^2(I_1).
mu:=function(p, kmax)
  local F,a,b,c,cm,rels,covrels,G,Gc,k,nq,ncov,nnext,h2,gr,t0;
  F:=FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
  cm:=function(x,y) return x^-1*y^-1*x*y; end;;
  rels:=[a^p,b^p,c^p,cm(cm(a,b),a),cm(cm(a,b),b),cm(cm(b,c),b),cm(cm(b,c),c),cm(cm(a,c),a),cm(cm(a,c),c)];;
  covrels:=Concatenation(List(rels,r->[cm(r,a),cm(r,b),cm(r,c),r^p]));;
  G:=F/rels;; Gc:=F/covrels;;
  for k in [2..kmax] do
    t0:=Runtime();;
    nq:=LogInt(Size(Image(EpimorphismPGroup(G,p,k-1))),p);;
    nnext:=LogInt(Size(Image(EpimorphismPGroup(G,p,k))),p);;
    ncov:=LogInt(Size(Image(EpimorphismPGroup(Gc,p,k))),p);;
    h2:=ncov-nq;; gr:=nnext-nq;;
    Print("p=",p," k=",k," |Q_k|=p^",nq," |Q_k*|=p^",ncov," dimH2(Q_k)=",h2," gr_k=",gr," img_k=",h2-gr," (",Runtime()-t0,"ms)\n");
  od;
end;;
mu(3,7);
QUIT;
