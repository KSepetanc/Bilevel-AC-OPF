var dfi   {time, bus};
var dV    {t in time, n in bus};
var cos_f {time, buspair}:=1;
var v_soa {time, line};

subject to bus_p_soa {t in time, n in bus}:
 sum {(n,g) in bus_gen} Pgen[t,g] - sum {(n,lo) in bus_load} pd[lo]*load_f[t] 
-sum {(l,n,m) in branch} P[t,l,n,m] - sum{(n,sh) in bus_shunt} (Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*gs[sh]
- (if n in es_bus then qbat_fix[t]) = 0;

subject to bus_q_soa {t in time, n in bus}:
 sum {(n,g) in bus_gen} Qgen[t,g] - sum {(n,lo) in bus_load} qd[lo]*load_f[t] 
-sum {(l,n,m) in branch} Q[t,l,n,m] + sum{(n,sh) in bus_shunt} (Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*bs[sh] 
- (if n in es_bus then qqbat_fix[t]) = 0;


subject to power_f_soa {t in time, (l,n,m) in branch_from}:
 P[t,l,n,m] = (Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*(gl[l]+gl_fr[l])/tap[l]^2 + v_soa[t,l]/2
 			- cospsin[t,l,n,m]*(Vt[t,n]*Vt[t,m]*cos_f[t,n,m] + dV[t,n]*Vt[t,m] + dV[t,m]*Vt[t,n])/tap[l]
 			- cosmsin[t,l,n,m]*Vt[t,n]*Vt[t,m]*(dfi[t,n]-dfi[t,m])/tap[l];
 			
subject to power_t_soa {t in time, (l,n,m) in branch_to}:
 P[t,l,n,m] = (Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*(gl[l]+gl_to[l])          + v_soa[t,l]/2
  			- cospsin[t,l,n,m]*(Vt[t,n]*Vt[t,m]*cos_f[t,m,n] + dV[t,n]*Vt[t,m] + dV[t,m]*Vt[t,n])/tap[l]
 			- cosmsin[t,l,n,m]*Vt[t,n]*Vt[t,m]*(dfi[t,n]-dfi[t,m])/tap[l];
 			
 			
subject to reactive_f_soa {t in time, (l,n,m) in branch_from}:
 Q[t,l,n,m] =-(Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*(bl[l]+bl_fr[l])/tap[l]^2
 			+ cosmsin[t,l,n,m]*(Vt[t,n]*Vt[t,m]*cos_f[t,n,m] + dV[t,n]*Vt[t,m] + dV[t,m]*Vt[t,n])/tap[l]
 			- cospsin[t,l,n,m]*Vt[t,n]*Vt[t,m]*(dfi[t,n]-dfi[t,m])/tap[l];
 			
subject to reactive_t_soa {t in time, (l,n,m) in branch_to}:
 Q[t,l,n,m] =-(Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*(bl[l]+bl_to[l])
 			+ cosmsin[t,l,n,m]*(Vt[t,n]*Vt[t,m]*cos_f[t,m,n] + dV[t,n]*Vt[t,m] + dV[t,m]*Vt[t,n])/tap[l]
 			- cospsin[t,l,n,m]*Vt[t,n]*Vt[t,m]*(dfi[t,n]-dfi[t,m])/tap[l];

 			
subject to v_soa0_soa_n {t in time, (l,n,m) in branch_from}:
 v_soa[t,l] = (gl[l] + gl_fr[l])*dV[t,n]^2/tap[l]^2
 			- 2*gl[l]*cos(fit[t,n]-fit[t,m]-shift[l])*dV[t,n]*dV[t,m]/tap[l]
 			+ (gl[l] + gl_to[l])*dV[t,m]^2;
 			
subject to cos0_soa_n {t in time, (n,m) in buspair}:
 cos_f[t,n,m] = 1 - (dfi[t,n]-dfi[t,m])^2/2;
  
subject to volt12_soa {t in time, n in bus}:
 vmin[n]-Vt[t,n] <= dV[t,n] <= vmax[n]-Vt[t,n];
 
subject to linemax_soa {t in time, (l,n,m) in branch: Scond[t,l,n,m]}:
 P[t,l,n,m]^2 + Q[t,l,n,m]^2 <= Sl_max[l]^2;
 
subject to refc_soa {t in time, n in refbus}:
 dfi[t,n] = -fit[t,n];