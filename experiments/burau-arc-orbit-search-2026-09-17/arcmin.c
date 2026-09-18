/* arcfast.c -- exhaustive search for Bigelow pairs in D_n, all crossing numbers m <= M at once.
 *
 * Bigelow (GT 3 (1999), Thm 1.4): Burau B_n (n>=3) is unfaithful iff there are embedded arcs
 * alpha: q1->q2 and beta: p0->q3 in minimal position with i(alpha,beta) > 0 and
 * int_beta alpha = sum_k eps_k t^{e_k} = 0.  Up to Stab(beta0) a pair is a crossing sequence in
 * the cut disk D' = D_n \ beta0: boundary line  J | L copy (heights up) | N=q3 | R copy (heights
 * down) | J.  Crossing k arrives at height h_k on side s_k and departs from the other copy.
 * Marks: x0 (q1 side of first crossing), y (q2 = departure copy of last crossing), free punctures
 * q4..qn as marks at side gaps (each owns a height object with a phantom partner) or at J (absent).
 * Minimal position <=> every chord encloses at least one mark (same-side chords must enclose a
 * puncture; L-R chords enclose N).  Exponent change along chord cur->arr = +k if arr is left of
 * cur, -k otherwise (k = marks enclosed); sign eps = +1 if arrival on L, -1 on R.
 *
 * The boundary is a doubly linked list; candidate arrivals are exactly the gaps of cur's region,
 * found by walking the line and jumping over nested chords, so each child costs O(1).
 * Pruning: l1(poly) <= crossings still allowed (each crossing changes one coefficient by 1).
 *
 * usage: arcfast n M [noprune] [printhits]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXP 8192
#define MAXE 16384
enum { FREE=0, MARK=1, NPT=2, SENT=3 };
typedef struct { int prev, next, partner, other, enc, lo, hasN; char kind, side, isA2; } pt_t;
static pt_t P[MAXP]; static int freestk[MAXP], nfreep;
static int n, M, noprune, printhits, nfree;
static long long poly[MAXE]; static long long l1; static int OFF=MAXE/2;
static long long leaves[MAXP], hitsm[MAXP], nodes; static long long minl1[MAXP], nmin[MAXP], minm1[MAXP];
static int JL, JR, NN;
static int seqs[MAXP], seqk[MAXP];

static int newpt(void){ int i=freestk[--nfreep]; memset(&P[i],0,sizeof(pt_t)); P[i].other=-1; P[i].partner=-1; return i; }
static void delpt(int i){ freestk[nfreep++]=i; }
static void ins_after(int p,int a){ int q=P[p].next; P[a].prev=p; P[a].next=q; P[p].next=a; P[q].prev=a; }
static void unlink_pt(int a){ int p=P[a].prev, q=P[a].next; P[p].next=q; P[q].prev=p; }
static inline void addterm(int e,int v){ long long *c=&poly[e+OFF]; l1-=llabs(*c); *c+=v; l1+=llabs(*c); }

static void dfs(int depth,int cur,int e);

static void try_child(int depth,int cur,int e,int p,int q,int dir,int k,int sc,int passN){
  if(k==0) return;                      /* bigon */
  if(depth+1 >= M) return;              /* need room for the final crossing */
  int a=newpt();
  if(dir<0) ins_after(q,a); else ins_after(p,a);   /* gap between p and q */
  P[a].kind=FREE; P[a].side=sc;
  int d=newpt(); P[d].kind=FREE; P[d].side=1-sc;
  if(sc==0){ int o=P[a].prev;            /* nearest lower L copy, or JL */
    if(o==JL) ins_after(P[JR].prev,d); else ins_after(P[P[o].partner].prev,d); }
  else { int o=P[a].next;
    if(o==JR) ins_after(JL,d); else ins_after(P[o].partner,d); }
  P[a].partner=d; P[d].partner=a;
  P[a].other=cur; P[cur].other=a; P[a].enc=P[cur].enc=k; P[a].hasN=P[cur].hasN=passN;
  if(dir<0){ P[a].lo=1; P[cur].lo=0; } else { P[a].lo=0; P[cur].lo=1; }
  int ne=e+(dir<0? k:-k), eps=(sc==0)?1:-1;
  addterm(ne,eps); seqs[depth]=sc; seqk[depth]=ne;
  dfs(depth+1,d,ne);
  addterm(ne,-eps);
  P[cur].other=-1;
  unlink_pt(d); unlink_pt(a); delpt(d); delpt(a);
}

static void report(int m){
  hitsm[m]++;
  if(printhits && hitsm[m]<=printhits){ printf("HIT m=%d seq:",m); for(int i=0;i<m;i++) printf(" %c%d",seqs[i]?'R':'L',seqk[i]); printf("\n"); fflush(stdout);} }

static void dfs(int depth,int cur,int e){
  nodes++;
  if(!noprune && l1 > M-depth) return;
  for(int dir=-1; dir<=1; dir+=2){
    int k=0, p=cur, sc=P[cur].side, passN=0;
    for(;;){
      int q = dir<0 ? P[p].prev : P[p].next;
      try_child(depth,cur,e,p,q,dir,k,sc,passN);
      if(P[q].kind==SENT) break;
      if(P[q].isA2){               /* finish: chord cur -> A2, then depart to y */
        if(k>0){ int ne=e+(dir<0? k:-k), eps=(P[q].side==0)?1:-1;
          addterm(ne,eps); int m=depth+1; leaves[m]++; seqs[depth]=P[q].side; seqk[depth]=ne;
          if(l1<minl1[m]){minl1[m]=l1; nmin[m]=0;} if(l1==minl1[m]) nmin[m]++; { long long v=0; for(int ii=OFF-600;ii<OFF+600;ii++) v+= (ii&1)? -poly[ii]:poly[ii]; if(llabs(v)<minm1[m]) minm1[m]=llabs(v);} if(l1==0) report(m);
          addterm(ne,-eps); }
        p=q; continue;
      }
      if(P[q].other>=0){
        int isnested = (dir<0) ? (P[q].lo==0) : (P[q].lo==1);
        if(!isnested) break;
        k+=P[q].enc; if(P[q].hasN){ passN^=1; sc=1-sc; }
        p=P[q].other; continue;
      }
      if(P[q].kind==MARK){ k++; }
      else if(P[q].kind==NPT){ k++; passN^=1; sc=1-sc; }
      p=q;
    }
  }
}

int main(int argc,char**argv){
  for(int i=0;i<MAXP;i++){minl1[i]=1<<30;minm1[i]=1<<30;}
  n=atoi(argv[1]); M=atoi(argv[2]); noprune=argc>3?atoi(argv[3]):0; printhits=argc>4?atoi(argv[4]):0;
  nfree=n-3;
  int ncomb=1; for(int i=0;i<nfree;i++) ncomb*=3;
  for(int c=0;c<ncomb;c++){
    int fs[8], t=c, nside=0;
    for(int i=0;i<nfree;i++){ fs[i]=(t%3)-1; t/=3; if(fs[i]>=0) nside++; }
    int tot=2+nside; int perm[12]; for(int i=0;i<tot;i++) perm[i]=i;
    for(;;){
      for(int q2s=0;q2s<2;q2s++){
        nfreep=0; for(int i=MAXP-1;i>=0;i--) freestk[nfreep++]=i;
        JL=newpt(); JR=newpt(); NN=newpt(); P[JL].kind=P[JR].kind=SENT; P[NN].kind=NPT;
        P[JL].next=NN; P[NN].prev=JL; P[NN].next=JR; P[JR].prev=NN;
        /* objects by height order perm: obj 0 = x0, obj 1 = q2, obj 2.. = free side punctures */
        int Lc[12], Rc[12];
        int side_of_mark[12]; side_of_mark[0]=0; side_of_mark[1]=q2s;
        { int j=2; for(int i=0;i<nfree;i++) if(fs[i]>=0) side_of_mark[j++]=fs[i]; }
        for(int o=0;o<tot;o++){ Lc[o]=newpt(); Rc[o]=newpt(); P[Lc[o]].partner=Rc[o]; P[Rc[o]].partner=Lc[o];
          P[Lc[o]].side=0; P[Rc[o]].side=1; }
        /* insert L copies ascending height after JL, R copies descending after NN */
        int order[12]; for(int i=0;i<tot;i++) order[perm[i]]=i;   /* order[rank] = obj */
        int last=JL; for(int r=0;r<tot;r++){ ins_after(last,Lc[order[r]]); last=Lc[order[r]]; }
        last=NN; for(int r=tot-1;r>=0;r--){ ins_after(last,Rc[order[r]]); last=Rc[order[r]]; }
        /* marks */
        P[Lc[0]].kind=MARK;                       /* x0 */
        int y = side_of_mark[1]==0? Lc[1]:Rc[1]; int A2 = P[y].partner;
        P[y].kind=MARK; P[A2].isA2=1;
        for(int o=2;o<tot;o++){ int mk = side_of_mark[o]==0? Lc[o]:Rc[o]; P[mk].kind=MARK; }
        memset(poly,0,sizeof(poly)); l1=0;
        addterm(0,1); seqs[0]=0; seqk[0]=0;
        dfs(1, Rc[0], 0);
        addterm(0,-1);
      }
      int i=tot-2; while(i>=0 && perm[i]>perm[i+1]) i--; if(i<0) break;
      int k=tot-1; while(perm[k]<perm[i]) k--; int tmp=perm[i]; perm[i]=perm[k]; perm[k]=tmp;
      for(int a=i+1,b=tot-1;a<b;a++,b--){tmp=perm[a];perm[a]=perm[b];perm[b]=tmp;}
    }
  }
  long long th=0;
  for(int m=1;m<=M;m++){ th+=hitsm[m]; if(noprune || hitsm[m]) printf("m=%d leaves=%lld minl1=%lld (#%lld) min|p(-1)|=%lld\n",m,leaves[m],minl1[m],nmin[m],minm1[m]); }
  printf("n=%d M=%d nodes=%lld total_hits=%lld\n",n,M,nodes,th);
  return 0;
}
