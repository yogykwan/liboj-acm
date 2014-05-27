/////////////////Computational Geometry Library by YogyKwan
#include<cstdio>
#include<cmath>
#include<cstring>
#include<iostream>
#include<algorithm>
#include<vector>
#include<queue>
using namespace std;
const double inf=1e10;
const double eps=1e-8;
const double pi=acos(-1.0);
const int maxn=50010;
void read(){
	freopen("d.in","r",stdin);
}
int dblcmp(double x){
	if(x<-eps) return -1;
	if(x>eps) return 1;
	return 0;
}
struct PT{
	double x,y;
	PT(){}
	PT(double _x,double _y):x(_x),y(_y){}
	PT operator + (const PT&t)const{
		return PT(x+t.x,y+t.y);
	}
	PT operator - (const PT&t)const{
		return PT(x-t.x,y-t.y);
	}
	PT operator *(const double t){
		return PT(x*t,y*t);
	}
	bool operator==(const PT&t)const{
		if(dblcmp(y-t.y)==0 && dblcmp(x-t.x)==0) return 1;
		return 0;
	}
	bool operator<(const PT&t)const{
		if(dblcmp(y-t.y)) return dblcmp(y-t.y)<0;
		return dblcmp(x-t.x)<0;
	}
	void input(){
		scanf("%lf%lf",&x,&y);
	}
	void output(){
		printf("(%f,%f)\n",x,y);
	}
};
struct LI{
	PT a,b;
	LI(){}
	LI(PT _a,PT _b):a(_a),b(_b){}
	void input(){
		a.input();
		b.input();
	}
	void output(){
		printf("(%f,%f)----(%f,%f)\n",a.x,a.y,b.x,b.y);
	}
};
struct LIABC{
	double a,b,c;
	LIABC(){}
	LIABC(double _a,double _b,double _c):a(_a),b(_b),c(_c){}
	LIABC(PT p,PT q){
		a=p.y-q.y;
		b=q.x-p.x;
		c=p.x*q.y-p.y*q.x;
	}
};
struct PO{
	PT p[maxn];
	int n,i;
	PO(){n=0;}
	PO(int _n):n(_n){}
	void input(){
		for(i=0;i<n;++i) p[i].input();
	}
	void output(){
		for(i=0;i<n;++i) p[i].output();
	}
	void add(PT a){
		p[n++]=a;
	}
};
struct CI{
	PT cen;
	double r;
	CI(){}
	CI(PT _cen,double _r):cen(_cen),r(_r){}
};
double dot(PT a,PT b){
	return a.x*b.x+a.y*b.y;
}
inline double xmult(PT a,PT b){
	return a.x*b.y-a.y*b.x;
}
inline double xmult(PT o,PT a,PT b){
	return xmult(a-o,b-o);
}
double length(PT a){
	return sqrt(a.x*a.x+a.y*a.y);
}
double getangle(PT a,PT b){
	if(dblcmp(length(a))==0 || dblcmp(length(b))==0) return 2*pi;
	double temp=acos(dot(a,b)/length(a)/length(b));
	if(dblcmp(xmult(a,b))<0) return -temp;
	return temp;
}
double getpolarangle(PT a){
	return getangle(PT(0,0),a);
}
PT point_rotate_ang(PT p,double ang){
	return PT(p.x*cos(ang)-p.y*sin(ang),p.x*sin(ang)+p.y*cos(ang));
}
double dist(PT a,PT b){
	return sqrt((a.x-b.x)*(a.x-b.x)+(a.y-b.y)*(a.y-b.y));
}
double dist2(PT a,PT b){
	return (a.x-b.x)*(a.x-b.x)+(a.y-b.y)*(a.y-b.y);
}
int which_qua(PT p){
	if(dblcmp(p.x)>0) return dblcmp(p.y)>0?0:3;
	else return dblcmp(p.y)>0?1:2;
}
LI getbisector_line(LI u){
	double &x1=u.a.x,&x2=u.b.x,&y1=u.a.y,&y2=u.b.y;
	return LI(PT((x1+x2+y1-y2)/2,(y1+y2+x2-x1)/2),PT((x1+x2+y2-y1)/2,(y1+y2-x2+x1)/2));
}
bool point_line(PT p,LI u){
	if(dblcmp(xmult(u.b-u.a,p-u.a))==0) return 1;
	return 0;
}
double getdist_point_line(PT p,LI line){
	return fabs(xmult(p-line.a,line.b-line.a)/dist(line.a,line.b));
}
double getdist_point_seg(PT p,LI line){
	if(dblcmp(dot(p-line.a,line.b-line.a))<0) return dist(line.a,p);
	if(dblcmp(dot(p-line.b,line.a-line.b))<0) return dist(line.b,p);
	return getdist_point_line(p,line);
}
double getdist_line_line(LI u,LI v){
	return getdist_point_line(u.a,v);
}
double xmult(LI u,LI v){
	return xmult(u.b-u.a,v.b-v.a);
}
double length(LI u){
	return dist(u.a,u.b);
}
double getangle(LI u,LI v){
	return getangle(u.b-u.a,v.b-v.a);
}
LI line_rotate_ang(LI line,double ang){
	PT temp=point_rotate_ang(line.b-line.a,ang);
	return LI(line.a,line.a+temp);
}
int line_cross_seg(LI u,LI v){
	double a1,a2;
	a1=xmult(u.b-u.a,v.a-u.a);
	a2=xmult(u.b-u.a,v.b-u.a);
	if(dblcmp(a1)*dblcmp(a2)<0) return 1;
	if(dblcmp(a1)==0 || dblcmp(a2)==0) return 2;
	return 0;
}
int line_cross_line(LI u,LI v){
	if(dblcmp(xmult(u.b-u.a,v.b-v.a))==0){
		if(dblcmp(xmult(u.b-u.a,v.b-u.a))==0) return 2;
		else return 0;
	}
	return 1;
}
int seg_cross_seg(LI u,LI v){
	double a1,a2,a3,a4;
	a1=xmult(u.b-u.a,v.a-u.a);
	a2=xmult(u.b-u.a,v.b-u.a);
	a3=xmult(v.b-v.a,u.a-v.a);
	a4=xmult(v.b-v.a,u.b-v.a);
	if(dblcmp(a1)*dblcmp(a2)<0 && dblcmp(a3)*dblcmp(a4)<0) return 1;
	if(dblcmp(a1)==0 && dblcmp(dot(v.a-u.a,v.a-u.b))<=0 || dblcmp(a2)==0 && dblcmp(dot(v.b-u.a,v.b-u.b))<=0 ||
			dblcmp(a3)==0 && dblcmp(dot(u.a-v.a,u.a-v.b))<=0 || dblcmp(a4)==0 && dblcmp(dot(u.b-v.a,u.b-v.b))<=0) return 2;
	return 0;
}
PT getp_line_cross_line(LI u,LI v){
	double a1,a2;
	a1=xmult(v.b-v.a,u.a-v.a);
	a2=xmult(v.b-v.a,u.b-v.a);
	return PT((u.a.x*a2-u.b.x*a1)/(a2-a1),(u.a.y*a2-u.b.y*a1)/(a2-a1));
}
LI line_move_r(LI line,double r){
	PT path;
	path=PT(-line.b.y+line.a.y,line.b.x-line.a.x)*(r/dist(line.a,line.b));
	return LI(line.a+path,line.b+path);
}
double getf_point_lineabc(PT p,LIABC line){
	return line.a*p.x+line.b*p.y+line.c;
}
double getpolarangle(LIABC line){
	return atan2(line.b,line.a);
}
double getdist_point_lineabc(PT p,LIABC line){
	return (line.a*p.x+line.b*p.y+line.c)/sqrt(line.a*line.a+line.b*line.b);
}
PT getp_lineabc_cross_lineabc(LIABC u,LIABC v){
	double x,y;
	x=(u.b*v.c-u.c*v.b)/(u.a*v.b-u.b*v.a);
	y=(u.c*v.a-u.a*v.c)/(u.a*v.b-u.b*v.a);
	return PT(x,y);
}
double getxmult_polygon(PO po){
	double ans=0;
	int j;
	for(int i=0;i<po.n;++i){
		j=i+1;
		if(j==po.n) j=0;
		ans+=xmult(po.p[i],po.p[j]);
	}
	return ans;
}
void unique_polygon(PO &po){
	po.n=unique(po.p,po.p+po.n)-po.p;
}
void norm_polygon(PO &po){
	if(dblcmp(getxmult_polygon(po))<0) reverse(po.p,po.p+po.n);
}
double getarea(PO po){
	if(po.n<3) return 0;
	return fabs(0.5*getxmult_polygon(po));
}
double getarea(PT a,PT b,PT c){
	return fabs(0.5*xmult(a,b,c));
}
double getcircum(PO po){
	double ans=0;
	int j;
	for(int i=0;i<po.n;++i){
		j=i+1;
		if(j==po.n) j=0;
		ans+=dist(po.p[i],po.p[j]);
	}
	return ans;
}
int point_polygon(PT p,PO po){
	int i,a1,a2,cnt=0,j;
	for(i=0;i<po.n;++i){
		j=i+1;
		if(j==po.n) j=0;
		if(point_line(p,LI(po.p[i],po.p[j]))) return 2;
	}
	for(i=0;i<po.n;++i){
		j=i+1;
		if(j==po.n) j=0;
		a1=dblcmp(po.p[i].y-p.y);
		a2=dblcmp(po.p[j].y-p.y);
		if(a1<0 && a2>=0 && dblcmp(xmult(p-po.p[i],po.p[j]-po.p[i]))<0) ++cnt;
		else if(a1>=0 && a2<0 && dblcmp(xmult(p-po.p[i],po.p[j]-po.p[i]))>0) --cnt;
	}
	return cnt!=0;
}
bool is_convex(PO po){
	if(po.n<3) return 0;
	int flag=-2,i,a1,j,k;
	for(i=0;i<po.n;++i){
		j=i+1;
		if(j==po.n) j=0;
		k=j+1;
		if(k==po.n) k=0;
		a1=dblcmp(xmult(po.p[j]-po.p[i],po.p[k]-po.p[j]));
		if(a1){
			if(flag==-2) flag=a1;
			else if(flag!=a1) return 0;
		}
	}
	return flag!=-2;
}
PT pbase;
bool cmp_graham(const PT&a,const PT&b){
	int a1=dblcmp(xmult(a-pbase,b-pbase));
	if(a1) return a1>0;
	return dblcmp(dist(a,pbase)-dist(b,pbase))<0;
}
void graham(PO po,PO &con){
	int i,top;
	if(po.n<3){
		for(i=0;i<po.n;++i) con.p[i]=po.p[i];
		con.n=po.n;
		return;
	}
	pbase=po.p[0];
	for(i=1;i<po.n;++i){
		if(dblcmp(po.p[i].y-pbase.y)<0 || dblcmp(po.p[i].y-pbase.y)==0 && dblcmp(po.p[i].x-pbase.x)<0) pbase=po.p[i];
	}
	sort(po.p,po.p+po.n,cmp_graham);
	unique_polygon(po);
	if(po.n<3){
		for(i=0;i<po.n;++i) con.p[i]=po.p[i];
		con.n=po.n;
		return;
	}
	con.p[0]=po.p[0],con.p[1]=po.p[1];
	top=2;
	for(i=2;i<po.n;++i){
		while(top>1 && dblcmp(xmult(con.p[top-1]-con.p[top-2],po.p[i]-con.p[top-1]))<=0) --top;
		con.p[top++]=po.p[i];
	}
	con.n=top;
}
bool polygon_cross_polygon_side(PO a,PO b){
	int i,j;
	for(i=0;i<a.n;++i){
		for(j=0;j<b.n;++j){
			if(seg_cross_seg(LI(a.p[i],a.p[(i+1)%a.n]),LI(b.p[j],b.p[(j+1)%b.n]))) return 1;
		}
	}
	return 0;
}
void picktheory_polygon(PO po,int &E,int &I){
	double area;
	PT temp;
	E=0;
	int i,j,a,b,t;
	for(i=0;i<po.n;++i){
		j=i+1;
		if(j==po.n) j=0;
		temp=po.p[j]-po.p[i];
		a=(int)(fabs(temp.x)+eps),b=(int)(fabs(temp.y)+eps);
		for(t;t=b;b=a%b,a=t);
		E+=a;
	}
	area=getarea(po);
	I=area+1-0.5*E;
}
bool cmp_halfplane(const LIABC &a,const LIABC &b){
	double a1,a2;
	a1=getpolarangle(a);
	a2=getpolarangle(b);
	if(dblcmp(a1-a2)) return a1<a2;
	return getdist_point_lineabc(PT(0,0),a)<getdist_point_lineabc(PT(0,0),b);
}
void halfplane_offline(LIABC *line,int n,PO &po){
	LIABC cb[maxn];
	PT cc[maxn];
	sort(line,line+n,cmp_halfplane);
	int m=1,i,j,h,t;
	for(i=1;i<n;++i){
		if(dblcmp(getpolarangle(line[i])-getpolarangle(line[i-1]))) line[m++]=line[i];
		if(dblcmp(line[m-1].a)==0 && dblcmp(line[m-1].b)==0){
			if(dblcmp(line[m-1].c)>=0) --m;
			else{
				po.n=-1;
				return;
			}
		}
	}
	h=0,t=1;
	cb[0]=line[0],cb[1]=line[1];
	cc[1]=getp_lineabc_cross_lineabc(cb[0],cb[1]);
	for(i=2;i<m;++i){
		while(h<t && dblcmp(getf_point_lineabc(cc[t],line[i]))<0) --t;
		while(h<t && dblcmp(getf_point_lineabc(cc[h+1],line[i]))<0) ++h;
		cb[++t]=line[i];
		cc[t]=getp_lineabc_cross_lineabc(cb[t-1],cb[t]);
	}
	while(h<t && dblcmp(getf_point_lineabc(cc[t],cb[h]))<0) --t;
	while(h<t && dblcmp(getf_point_lineabc(cc[h+1],cb[t]))<0) ++h;
	if(h+1>=t){
		po.n=-1;
		return;
	}
	po.n=0;
	po.add(getp_lineabc_cross_lineabc(cb[h],cb[t]));
	for(i=h+1;i<=t;++i) po.add(cc[i]);
}
void halfplane_online(PT *a,int n,PT *b,int &m,LI line){
	int i,j;
	m=0;
	PT temp=line.b-line.a;
	for(i=0;i<n;++i){
		if(dblcmp(xmult(line.a-a[i],temp))>=0){
			b[m++]=a[i];
			continue;
		}
		j=(i-1+n)%n;
		if(dblcmp(xmult(line.a-a[j],temp))>0){
			b[m++]=getp_line_cross_line(LI(a[i],a[j]),line);
		}
		j=(i+1)%n;
		if(dblcmp(xmult(line.a-a[j],temp))>0){
			b[m++]=getp_line_cross_line(LI(a[i],a[j]),line);
		}
	}
}
double RC_diameter(PO po){
	if(po.n<2) return 0;
	int u[2],i;
	PT e[4];
	double mmax,temp,sumang=0.0,curang,ang[2];
	memset(u,0,sizeof(u));
	po.p[po.n]=po.p[0];
	for(i=0;i<po.n;++i){
		if(dblcmp(po.p[i].y-po.p[u[0]].y)<0 || dblcmp(po.p[i].y-po.p[u[0]].y)==0 && dblcmp(po.p[i].x-po.p[u[0]].x)>0) u[0]=i;
		if(dblcmp(po.p[i].y-po.p[u[1]].y)>0 || dblcmp(po.p[i].y-po.p[u[1]].y)==0 && dblcmp(po.p[i].x-po.p[u[1]].x)<0) u[1]=i;
	}
	e[0]=PT(1,0),e[1]=PT(-1,0);
	mmax=dist2(po.p[u[0]],po.p[u[1]]);
	while(dblcmp(sumang-pi)<=0){
		curang=inf;
		for(i=0;i<2;++i){
			ang[i]=getangle(e[i],po.p[u[i]+1]-po.p[u[i]]);
			curang=min(curang,ang[i]);
		}
		for(i=0;i<2;++i){
			e[i]=point_rotate_ang(e[i],curang);
			if(dblcmp(ang[i]-curang)==0) u[i]=(u[i]+1)%po.n;
		}
		temp=dist2(po.p[u[0]],po.p[u[1]]);
		mmax=max(mmax,temp);
		sumang+=curang;
	}
	return sqrt(mmax);
}
double RC_min_2convex(PO P,PO Q){
	int u[2],i;
	PT e[2];
	u[0]=u[1]=0;
	P.p[P.n]=P.p[0],Q.p[Q.n]=Q.p[0];
	for(i=0;i<P.n;++i){
		if(dblcmp(P.p[i].y-P.p[u[0]].y)<0 || dblcmp(P.p[i].y-P.p[u[0]].y)==0 && dblcmp(P.p[i].x-P.p[u[0]].x)>0) u[0]=i;
	}
	for(i=0;i<Q.n;++i){
		if(dblcmp(Q.p[i].y-Q.p[u[1]].y)>0 || dblcmp(Q.p[i].y-Q.p[u[1]].y)==0 && dblcmp(Q.p[i].x-Q.p[u[1]].x)<0) u[1]=i;
	}
	e[0]=PT(1,0),e[1]=PT(-1,0);
	double sumang=0,curang,mmin=inf,temp,ang[2];
	int flag=0;
	while(dblcmp(sumang-2*pi)<=0){
		ang[0]=getangle(e[0],P.p[u[0]+1]-P.p[u[0]]);
		ang[1]=getangle(e[1],Q.p[u[1]+1]-Q.p[u[1]]);
		if(dblcmp(ang[0]-ang[1])==0){
			mmin=min(mmin,getdist_point_seg(Q.p[u[1]],LI(P.p[u[0]],P.p[u[0]+1])));
			mmin=min(mmin,getdist_point_seg(Q.p[u[1]+1],LI(P.p[u[0]],P.p[u[0]+1])));
			curang=ang[0];
			u[0]=(u[0]+1)%P.n;
			u[1]=(u[1]+1)%Q.n;
		}else if(dblcmp(ang[0]-ang[1])<0){
			mmin=min(mmin,getdist_point_seg(Q.p[u[1]],LI(P.p[u[0]],P.p[u[0]+1])));
			curang=ang[0];
			u[0]=(u[0]+1)%P.n;
		}else{
			mmin=min(mmin,getdist_point_seg(P.p[u[0]],LI(Q.p[u[1]],Q.p[u[1]+1])));
			curang=ang[1];
			u[1]=(u[1]+1)%Q.n;
		}
		e[0]=point_rotate_ang(e[0],curang);
		e[1]=point_rotate_ang(e[1],curang);
		sumang+=curang;
	}
	return mmin;
}
double RC_min_rectangle(PO po){
	if(po.n<3) return 0;
	int u[4];
	PT e[4];
	int i;
	double mmin,sumang=0.0,curang,ang[4],temp;
	memset(u,0,sizeof(u));
	po.p[po.n]=po.p[0];
	for(i=0;i<po.n;++i){
		if(dblcmp(po.p[i].y-po.p[u[0]].y)<0 || dblcmp(po.p[i].y-po.p[u[0]].y)==0 && dblcmp(po.p[i].x-po.p[u[0]].x)>0) u[0]=i;
		if(dblcmp(po.p[i].x-po.p[u[1]].x)>0 || dblcmp(po.p[i].x-po.p[u[1]].x)==0 && dblcmp(po.p[i].y-po.p[u[1]].y)>0) u[1]=i;
		if(dblcmp(po.p[i].y-po.p[u[2]].y)>0 || dblcmp(po.p[i].y-po.p[u[2]].y)==0 && dblcmp(po.p[i].x-po.p[u[2]].x)<0) u[2]=i;
		if(dblcmp(po.p[i].x-po.p[u[3]].x)<0 || dblcmp(po.p[i].x-po.p[u[3]].x)==0 && dblcmp(po.p[i].y-po.p[u[3]].y)<0) u[3]=i;
	}
	e[0]=PT(1,0),e[1]=PT(0,1),e[2]=PT(-1,0),e[3]=PT(0,-1);
	mmin=getdist_point_line(po.p[u[0]],LI(po.p[u[2]],po.p[u[2]]+e[2]))*getdist_point_line(po.p[u[1]],LI(po.p[u[3]],po.p[u[3]]+e[3]));
	while(dblcmp(sumang-0.5*pi)<=0){
		curang=inf;
		for(i=0;i<4;++i){
			ang[i]=getangle(e[i],po.p[u[i]+1]-po.p[u[i]]);
			curang=min(curang,ang[i]);
		}
		for(i=0;i<4;++i){
			e[i]=point_rotate_ang(e[i],curang);
			if(dblcmp(ang[i]-curang)==0) u[i]=(u[i]+1)%po.n;
		}
		temp=getdist_point_line(po.p[u[0]],LI(po.p[u[2]],po.p[u[2]]+e[2]))*getdist_point_line(po.p[u[1]],LI(po.p[u[3]],po.p[u[3]]+e[3]));
		mmin=min(mmin,temp);
		sumang+=curang;
	}
	return mmin;
}
double getarea_max_emptyconvex(PT* p,int n,PT *eq,int eid[][maxn],int *etop,double es[][maxn]){
	sort(p,p+n);
	double ans=0;
	for(int a=0;a<n;++a){
		double temp;
		int m=n-a-1,i,j,col;
		memcpy(eq,p+a+1,sizeof(PT)*m);
		pbase=p[a];
		sort(eq,eq+m,cmp_graham);
		memset(etop,0,sizeof(etop));
		for(i=0;i<m;++i){
			col=0;
			for(j=i-1;j>=0 && dblcmp(xmult(pbase,eq[i],eq[j]))==0;--j) col=1;
			for(;j>=0;--j){
				if(etop[i] && dblcmp(xmult(eq[i],eq[j],eq[eid[i][etop[i]-1]]))<0) continue;
				temp=getarea(pbase,eq[i],eq[j]);
				while(etop[j]>=2 && dblcmp(xmult(eq[i],eq[j],eq[eid[j][etop[j]-2]]))<0) --etop[j];
				if(etop[j] && dblcmp(xmult(eq[i],eq[j],eq[eid[j][etop[j]-1]]))<=0) temp+=es[j][etop[j]-1];
				while(etop[i] && dblcmp(temp-es[i][etop[i]-1])>=0) --etop[i];
				es[i][etop[i]]=temp;
				eid[i][etop[i]++]=j;
			}
			if(etop[i]) ans=max(ans,es[i][0]);
			if(col) etop[i]=0;
		}
	}
	return ans;
}
//ÍâÐÄ
PT getoutc_tri(PT a,PT b,PT c){
	LI u,v;
	u.a.x=(a.x+b.x)/2;
	u.a.y=(a.y+b.y)/2;
	u.b.x=u.a.x-a.y+b.y;
	u.b.y=u.a.y+a.x-b.x;
	v.a.x=(a.x+c.x)/2;
	v.a.y=(a.y+c.y)/2;
	v.b.x=v.a.x-a.y+c.y;
	v.b.y=v.a.y+a.x-c.x;
	return getp_line_cross_line(u,v);
}
PT getinc_tri(PT a,PT b,PT c){
	LI u,v;
	double m,n;
	u.a=a;
	m=atan2(b.y-a.y,b.x-a.x);
	n=atan2(c.y-a.y,c.x-a.x);
	u.b.x=u.a.x+cos((m+n)/2);
	u.b.y=u.a.y+sin((m+n)/2);
	v.a=b;
	m=atan2(a.y-b.y,a.x-b.x);
	n=atan2(c.y-b.y,c.x-b.x);
	v.b.x=v.a.x+cos((m+n)/2);
	v.b.y=v.a.y+sin((m+n)/2);
	return getp_line_cross_line(u,v);
}
PT getperc_tri(PT a,PT b,PT c){
	LI u,v;
	u.a=c;
	u.b.x=u.a.x-a.y+b.y;
	u.b.y=u.a.y+a.x-b.x;
	v.a=b;
	v.b.x=v.a.x-a.y+c.y;
	v.b.y=v.a.y+a.x-c.x;
	return getp_line_cross_line(u,v);
}
PT getgrac_tri(PT a,PT b,PT c){
	PT ab,bc;
	ab=(a+b)*0.5;
	bc=(b+c)*0.5;
	return getp_line_cross_line(LI(ab,c),LI(bc,a));
}
PT getferc_tri(PT a,PT b,PT c){
    PT u,v;
    double step=fabs(a.x)+fabs(a.y)+fabs(b.x)+fabs(b.y)+fabs(c.x)+fabs(c.y);
    int i,j,k;
    u.x=(a.x+b.x+c.x)/3;
    u.y=(a.y+b.y+c.y)/3;
    while (step>1e-10)
        for (k=0;k<10;step/=2,k++)
            for (i=-1;i<=1;i++)
                for (j=-1;j<=1;j++){
                    v.x=u.x+step*i;
                    v.y=u.y+step*j;
                    if (dist(u,a)+dist(u,b)+dist(u,c)>dist(v,a)+dist(v,b)+dist(v,c)) u=v;
                }
    return u;
}
PT getc_polygon(PO &po){
	double ans=0,tempans;
	PT cen=PT(0,0),tempcen;
	for(int i=1;i<po.n-1;++i){
		tempans=0.5*xmult(po.p[0],po.p[i],po.p[i+1]);
		if(dblcmp(tempans)){
			tempcen=getgrac_tri(po.p[0],po.p[i],po.p[i+1]);
			cen=cen+(tempcen*tempans);
			ans+=tempans;
		}
	}
	cen=cen*(1.0/ans);
	return cen;
}
double getangle_ball(double la1,double lo1,double la2,double lo2){
	return acos(sin(la1)*sin(la2)+cos(la1)*cos(la2)*cos(lo1-lo2));
}
struct PT3{
	double x,y,z;
	PT3(){}
	PT3(double _x,double _y,double _z):x(_x),y(_y),z(_z){}
	void input(){
		scanf("%lf%lf%lf",&x,&y,&z);
	}
	void output(){
		printf("(%f , %f , %f)\n",x,y,z);
	}
	PT3 operator + (const PT3 &t)const{
		return PT3(x+t.x,y+t.y,z+t.z);
	}
	PT3 operator - (const PT3 &t)const{
		return PT3(x-t.x,y-t.y,z-t.z);
	}
	PT3 operator / (double t)const{
		return PT3(x*t,y*t,z*t);
	}
	double operator * (const PT3 &t)const{
		return x*t.x+y*t.y+z*t.z;
	}
	PT3 operator ^ (const PT3 &t)const{
		return PT3(y*t.z-z*t.y,z*t.x-x*t.z,x*t.y-y*t.x);
	}
	bool operator == (const PT3 &t)const{
		return (dblcmp(x-t.x)==0 && dblcmp(y-t.y)==0 && dblcmp(z-t.z)==0);
	}
};
double xmult(PT3 a,PT3 b){
	return a.x*b.y-a.y*b.x+a.y*b.z-a.z*b.y+a.z*b.x-a.x*b.z;
}
double getv(PT3 a,PT3 b,PT3 c,PT3 d){
	return ((b-a)^(c-a))*(d-a)/6.0;
}
struct FA{
	int a,b,c;
	FA(){}
	FA(int _a,int _b,int _c):a(_a),b(_b),c(_c){}
};
bool outside(PT3 p,PT3 a,PT3 b,PT3 c){
	return dblcmp(getv(a,b,c,p))>0;
}
int tot_gm[369][maxn],yh[369][maxn];
struct PO3{
	int n,i,m;
	PT3 p[maxn];
	FA f[maxn<<3];

	void input(){
		m=0;
		for(i=0;i<n;++i) p[i].input();
		n=unique(p,p+n)-p;
	}
	void addfa(int d,int a,int b,int c){
		if(outside(p[d],p[a],p[b],p[c])) f[m++]=FA(a,c,b);
		else f[m++]=FA(a,b,c);
		tot_gm[a][b]++,tot_gm[b][a]++,tot_gm[b][c]++,tot_gm[c][b]++,tot_gm[c][a]++,tot_gm[a][c]++;
	}
};
void update_face(int d,int st,PO3 &po){
	int i,j,cnt=0;
	bool vis[maxn<<3];
	memset(vis,0,sizeof(vis));
	int a,b,c;
	for(i=st;i<po.m;++i){
		a=po.f[i].a,b=po.f[i].b,c=po.f[i].c;
		if(outside(po.p[d],po.p[a],po.p[b],po.p[c])){
			vis[i]=1;
			tot_gm[a][b]--,tot_gm[b][a]--,tot_gm[b][c]--,tot_gm[c][b]--,tot_gm[c][a]--,tot_gm[a][c]--;
			yh[a][b]=c,yh[b][a]=c,yh[b][c]=a,yh[c][b]=a,yh[c][a]=b,yh[a][c]=b;
		}
	}
	for(i=0;i<po.m;++i){
		if(!vis[i]) po.f[cnt++]=po.f[i];
	}
	po.m=cnt;
	for(i=0;i<d;++i){
		for(j=i+1;j<d;++j){
			if(tot_gm[i][j]==1){
				po.addfa(yh[i][j],d,i,j);
			}
		}
	}
}
bool same_face(FA x,FA y,PO3 &po){
	if(dblcmp(getv(po.p[x.a],po.p[x.b],po.p[x.c],po.p[y.a]))) return 0;
	if(dblcmp(getv(po.p[x.a],po.p[x.b],po.p[x.c],po.p[y.b]))) return 0;
	if(dblcmp(getv(po.p[x.a],po.p[x.b],po.p[x.c],po.p[y.c]))) return 0;
	return 1;
}
int get_convex(PO3 &po){
	if(po.n<4) return 0;
	int i,j,a,b,c;
	for(i=2;i<po.n;++i){
		if(dblcmp(xmult(po.p[i]-po.p[0],po.p[i]-po.p[1]))){
			swap(po.p[2],po.p[i]);
			break;
		}
	}
	for(i=3;i<po.n;++i){
		if(dblcmp(getv(po.p[0],po.p[1],po.p[2],po.p[i]))){
			swap(po.p[3],po.p[i]);
			break;
		}
	}
	po.addfa(0,1,2,3),po.addfa(1,0,2,3),po.addfa(2,1,0,3),po.addfa(3,1,2,0);
	for(i=4;i<po.n;++i){
		for(j=0;j<po.m;++j){
			a=po.f[j].a,b=po.f[j].b,c=po.f[j].c;
			if(outside(po.p[i],po.p[a],po.p[b],po.p[c])) break;
		}
		if(j<po.m){
			update_face(i,j,po);
		}
	}
	int cntf=0;
	for(i=0;i<po.m;++i){
		for(j=i+1;j<po.m;++j){
			if(same_face(po.f[i],po.f[j],po)) break;
		}
		if(j==po.m) ++cntf;
	}
	return cntf;
}
typedef pair<int, int> pii;
#define Pconst 359
#define Mprime 100003
#define MASK 0x7FFFFFFF
const int dx[] = {-1, -1, -1, 0, 0, 0, 1, 1, 1};
const int dy[] = {-1, 0, 1, -1, 0, 1, -1, 0, 1};
inline pii getGrid(const PT &p, double r) {
    return make_pair(floor(p.x/r),floor(p.y/r));
}
struct Hash {
    pii _key[maxn];
    PT _val[maxn];
    int _head[maxn], _next[maxn], _tot;
    void clear(){
        memset(_head, -1, sizeof(_head));
        _tot = 0;
    }
    int hashFunc(const pii &key) const {
        return ((key.first * Pconst ^ key.second) & MASK) % Mprime;
    }
    void insert(const pii &key, const PT &val) {
        int k = hashFunc(key);
        _key[_tot] = key; _val[_tot] = val;
        _next[_tot] = _head[k]; _head[k] = _tot++;
    }
    double query(const pii &key, const PT &val) const {
        int i, j, k;
        pii cur;
        double ret = inf;
        for (i = 0; i < 9; ++i) {
            cur = make_pair(key.first + dx[i], key.second + dy[i]);
            for (j = _head[hashFunc(cur)]; ~j; j = _next[j]) {
                if (cur == _key[j]) ret = min(ret, dist(val, _val[j]));
            }
        }
        return ret;
    }
};
void rebuild(const PT *p, int n, double r,Hash &mp) {
    mp.clear();
    for(int i=0;i<n;++i) mp.insert(getGrid(p[i],r),p[i]);
}
double get_mdis_pts(PT *p,int n) {
    Hash mp;
    srand(NULL);
    int i;
    double ret,cur;
    random_shuffle(p,p+n);
    if (dblcmp(ret=dist(p[0],p[1]))==0) return 0;
    rebuild(p,2,ret,mp);
    for (i=2;i<n;++i){
        if(dblcmp(cur=mp.query(getGrid(p[i],ret),p[i]))==0) return 0;
        if(cur<ret) rebuild(p,i+1,ret=cur,mp);
        else mp.insert(getGrid(p[i],ret),p[i]);
    }
    return ret;
}
/////////////////Computational Geometry Library by YogyKwan
int main(){
}
