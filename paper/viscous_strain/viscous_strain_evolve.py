"""Evolve z-independent 3D NS (2D NS, u3=0) from Bahouri-Chemin data omega_K=f_K(x)f_K(y)e_z.
Integrating-factor RK4 (heat part exact), 2/3 dealiasing. Records ||S||_inf/||omega||_inf at
log-spaced times. Also records the pure heat flow e^{nu t Delta}omega_K (exact in Fourier).
NUMERICS, NOT PROOFS. Usage: python3 viscous_strain_evolve.py K nu T out.jsonl [A amplitude] [N]"""
import numpy as np, json, sys
K=int(sys.argv[1]); nu=float(sys.argv[2]); T=float(sys.argv[3]); out=open(sys.argv[4],'w')
A=float(sys.argv[5]) if len(sys.argv)>5 else 1.0
N=int(sys.argv[6]) if len(sys.argv)>6 else max(256,4*K); x=2*np.pi*np.arange(N)/N; X,Y=np.meshgrid(x,x,indexing='ij')
k=np.fft.fftfreq(N,1/N); KX,KY=np.meshgrid(k,k,indexing='ij'); K2=KX**2+KY**2
K2i=np.where(K2==0,0,1/np.where(K2==0,1,K2)); deal=(np.abs(KX)<N/3)&(np.abs(KY)<N/3)
f=lambda z: 4/np.pi*sum(np.sin(j*z)/j for j in range(1,K+1,2))
w0=A*np.fft.fft2(f(X)*f(Y))
def nl(wh):
    ph=-wh*K2i; u=np.real(np.fft.ifft2(-1j*KY*ph)); v=np.real(np.fft.ifft2(1j*KX*ph))
    wx=np.real(np.fft.ifft2(1j*KX*wh)); wy=np.real(np.fft.ifft2(1j*KY*wh))
    return -np.fft.fft2(u*wx+v*wy)*deal
def SM(wh):
    ph=-wh*K2i; s11=np.real(np.fft.ifft2(KX*KY*ph)); s12=0.5*np.real(np.fft.ifft2((KY**2-KX**2)*ph))
    M=np.abs(np.real(np.fft.ifft2(wh))).max(); S=np.sqrt(s11**2+s12**2).max(); return float(M),float(S)
times=sorted(set([0.0]+list(np.round(np.geomspace(1e-4,T,25),6))))
dt=0.2/(N*max(1.0,A)); t=0.; wh=w0.copy(); i=0
while i<len(times):
    if t>=times[i]-1e-12:
        M,S=SM(wh); Mh,Sh=SM(w0*np.exp(-nu*K2*t))
        r=dict(K=K,nu=nu,A=A,N=N,t=t,nut=nu*t,M=M,Sinf=S,ratio=S/M,heat_ratio=Sh/Mh); out.write(json.dumps(r)+'\n'); out.flush(); i+=1
        if i==len(times): break
    h=min(dt,times[i]-t) if times[i]-t>1e-14 else dt
    E=np.exp(-nu*K2*h/2); E2=E*E
    a=nl(wh); b=nl(E*(wh+h/2*a)); c=nl(E*wh+h/2*b); d=nl(E2*wh+h*E*c)
    wh=E2*wh+h/6*(E2*a+2*E*(b+c)+d); t+=h
out.write(json.dumps(dict(done=True))+'\n'); out.close()
