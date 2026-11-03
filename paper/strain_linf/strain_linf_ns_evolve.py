"""Evolve 2D NS (= z-independent 3D NS with u3=0) from omega_K data; record ||S||_inf/||omega||_inf.
NUMERICS, NOT PROOFS. Usage: python3 strain_linf_ns_evolve.py K nu T out.jsonl"""
import numpy as np, json, sys
K=int(sys.argv[1]); nu=float(sys.argv[2]); T=float(sys.argv[3]); out=open(sys.argv[4],'w')
N=max(256, 4*K); x=2*np.pi*np.arange(N)/N; X,Y=np.meshgrid(x,x,indexing='ij')
k=np.fft.fftfreq(N,1/N); KX,KY=np.meshgrid(k,k,indexing='ij'); K2=KX**2+KY**2; K2i=np.where(K2==0,0,1/np.where(K2==0,1,K2))
deal=(np.abs(KX)<N/3)&(np.abs(KY)<N/3)
f=lambda z: 4/np.pi*sum(np.sin(j*z)/j for j in range(1,K+1,2))
wh=np.fft.fft2(f(X)*f(Y))
def rhs(wh):
    ph=-wh*K2i; u=np.real(np.fft.ifft2(-1j*KY*ph)); v=np.real(np.fft.ifft2(1j*KX*ph))
    wx=np.real(np.fft.ifft2(1j*KX*wh)); wy=np.real(np.fft.ifft2(1j*KY*wh))
    return -np.fft.fft2(u*wx+v*wy)*deal - nu*K2*wh
def diag(t,wh):
    ph=-wh*K2i; s11=np.real(np.fft.ifft2(KX*KY*ph)); s12=0.5*np.real(np.fft.ifft2((KY**2-KX**2)*ph))
    w=np.real(np.fft.ifft2(wh)); M=np.abs(w).max(); S=np.sqrt(s11**2+s12**2).max()
    r=dict(K=K,nu=nu,N=N,t=round(t,4),M=float(M),Sinf=float(S),ratio=float(S/M)); out.write(json.dumps(r)+'\n'); out.flush(); print(r,flush=True)
dt=0.2/ (N); t=0.; nxt=0.; 
while t<=T+1e-12:
    if t>=nxt-1e-12: diag(t,wh); nxt+=T/20
    a=rhs(wh); b=rhs(wh+dt/2*a); c=rhs(wh+dt/2*b); d=rhs(wh+dt*c); wh=wh+dt/6*(a+2*b+2*c+d); t+=dt
