var lambda1  {time, bus};
var lambda2  {time, bus};
var lambda3  {time, branch_from};
var lambda4  {time, branch_to};
var lambda5  {time, branch_from};
var lambda6  {time, branch_to};
var lambda7  {time, refbus};
var lambda11 {t in time, (l,n,m) in branch: Scond[t,l,n,m]};
var lambda12 {t in time, (l,n,m) in branch: Scond[t,l,n,m]};
var lambda13 {t in time, (l,n,m) in branch: Scond[t,l,n,m]} >= 0;
var lambda14 {t in time, (n,m) in buspair: Ccond[t,n,m]};
var lambda15 {t in time, (n,m) in buspair: Ccond[t,n,m]};
var lambda16 {t in time, (n,m) in buspair: Ccond[t,n,m]} >= 0;
var lambda17 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]};
var lambda18 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]};
var lambda19 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]};
var lambda20 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]} >= 0;
var lambda21 {t in time, (l,n,m) in branch_from:!Vcond[t,l,n,m]};
var lambda22 {t in time, (n,m) in buspair:!Ccond[t,n,m]};

var mi1max {time, gen};
var mi1min {time, gen};
var mi2max {time, gen};
var mi2min {time, gen};
var mi3max {time, bus};
var mi3min {time, bus};


maximize DualOFQP: 
-sum {t in time, es in es_bus}							 (qbat_fix[t]*lambda1[t,es]+qqbat_fix[t]*lambda2[t,es])
-sum {t in time, g in gen: c2[g]>0}                      (c1[g]+mi1max[t,g]-mi1min[t,g]+sum{(n,g) in bus_gen} lambda1[t,n])^2/(4*c2[g])
+sum {t in time, n in refbus}                            fit[t,n]*lambda7[t,n]
+sum {t in time, g in gen}                               (c0[g]-pg_max[g]*mi1max[t,g]+pg_min[g]*mi1min[t,g]-qg_max[g]*mi2max[t,g]+qg_min[g]*mi2min[t,g])
-sum {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]} (lambda17[t,l,n,m]+lambda20[t,l,n,m])/2
+sum {t in time, n in bus}                               ((Vt[t,n]-vmax[n])*mi3max[t,n] + (vmin[n]-Vt[t,n])*mi3min[t,n])
-sum {t in time, (n,lo) in bus_load}                     (pd[lo]*load_f[t]*lambda1[t,n]+qd[lo]*load_f[t]*lambda2[t,n]) 
-sum {t in time, (n,sh) in bus_shunt}                    (gs[sh]*Vt[t,n]^2*lambda1[t,n]-bs[sh]*Vt[t,n]^2*lambda2[t,n])
+sum {t in time, (n,m) in buspair: Ccond[t,n,m]}         ((3/4)*lambda15[t,n,m] - (5/4)*lambda16[t,n,m]) 
-sum {t in time, (n,m) in buspair:!Ccond[t,n,m]}         lambda22[t,n,m]
-sum {t in time, (l,n,m) in branch_from}                 ((gl[l]+gl_fr[l])*lambda3[t,l,n,m]-(bl[l]+bl_fr[l])*lambda5[t,l,n,m])*Vt[t,n]^2/tap[l]^2
-sum {t in time, (l,n,m) in branch_to}                   ((gl[l]+gl_to[l])*lambda4[t,l,n,m]-(bl[l]+bl_to[l])*lambda6[t,l,n,m])*Vt[t,n]^2
-sum {t in time, (l,n,m) in branch: Scond[t,l,n,m]}      Sl_max[l]*lambda13[t,l,n,m];

subject to dual_dfi {t in time, n in bus}:
(if n in refbus then lambda7[t,n])
-sum {(n,m) in buspair: Ccond[t,n,m]} lambda14[t,n,m]/sqrt(2) 
+sum {(m,n) in buspair: Ccond[t,m,n]} lambda14[t,m,n]/sqrt(2) 
+sum {(l,n,m) in branch_from} Vt[t,n]*Vt[t,m]*(cosmsin[t,l,n,m]*lambda3[t,l,n,m]+cospsin[t,l,n,m]*lambda5[t,l,n,m]-cosmsin[t,l,m,n]*lambda4[t,l,m,n]-cospsin[t,l,m,n]*lambda6[t,l,m,n])/tap[l]
-sum {(l,n,m) in branch_to}   Vt[t,n]*Vt[t,m]*(cosmsin[t,l,m,n]*lambda3[t,l,m,n]+cospsin[t,l,m,n]*lambda5[t,l,m,n]-cosmsin[t,l,n,m]*lambda4[t,l,n,m]-cospsin[t,l,n,m]*lambda6[t,l,n,m])/tap[l]
= 0;

subject to dual_dV {t in time, n in bus}:
 mi3max[t,n]-mi3min[t,n]
+2*Vt[t,n]*(lambda2[t,n]*sum {(n,sh) in bus_shunt} bs[sh] - lambda1[t,n]*sum {(n,sh) in bus_shunt} gs[sh])

+sum {(l,n,m) in branch_from} (
-2*(gl[l]+gl_fr[l])*Vt[t,n]*lambda3[t,l,n,m]/tap[l]^2 + Vt[t,m]*cospsin[t,l,n,m]*lambda3[t,l,n,m]/tap[l]
+2*(bl[l]+bl_fr[l])*Vt[t,n]*lambda5[t,l,n,m]/tap[l]^2 - Vt[t,m]*cosmsin[t,l,n,m]*lambda5[t,l,n,m]/tap[l]
+Vt[t,m]*cospsin[t,l,m,n]*lambda4[t,l,m,n]/tap[l]
-Vt[t,m]*cosmsin[t,l,m,n]*lambda6[t,l,m,n]/tap[l])

+sum {(l,n,m) in branch_to} (
-2*(gl[l]+gl_to[l])*Vt[t,n]*lambda4[t,l,n,m]          + Vt[t,m]*cospsin[t,l,n,m]*lambda4[t,l,n,m]/tap[l]
+2*(bl[l]+bl_to[l])*Vt[t,n]*lambda6[t,l,n,m]          - Vt[t,m]*cosmsin[t,l,n,m]*lambda6[t,l,n,m]/tap[l]
+Vt[t,m]*cospsin[t,l,m,n]*lambda3[t,l,m,n]/tap[l]
-Vt[t,m]*cosmsin[t,l,m,n]*lambda5[t,l,m,n]/tap[l])

-sum {(l,n,m) in branch_from: Vcond[t,l,n,m]} (vm1[t,l,n,m]*lambda18[t,l,n,m] + vm3[t,l,n,m]*lambda19[t,l,n,m])
+sum {(l,n,m) in branch_to:   Vcond[t,l,m,n]}  vm2[l]*lambda18[t,l,m,n] = 0;

subject to dual_P {t in time, (l,n,m) in branch}:
 -lambda1[t,n] + (if (l,n,m) in branch_from then lambda3[t,l,n,m]) + (if (l,n,m) in branch_to then lambda4[t,l,n,m]) - (if Scond[t,l,n,m] then lambda11[t,l,n,m]) = 0;
 
subject to dual_Q {t in time, (l,n,m) in branch}:
 -lambda2[t,n] + (if (l,n,m) in branch_from then lambda5[t,l,n,m]) + (if (l,n,m) in branch_to then lambda6[t,l,n,m]) - (if Scond[t,l,n,m] then lambda12[t,l,n,m]) = 0;

subject to dual_Pgen {t in time, g in gen: c2[g]=0}:
 c1[g] + mi1max[t,g] - mi1min[t,g] + sum {(n,g) in bus_gen} lambda1[t,n] = 0;
 
subject to dual_Qgen {t in time, g in gen}:
         mi2max[t,g] - mi2min[t,g] + sum {(n,g) in bus_gen} lambda2[t,n] = 0;
 
subject to dual_cosf {t in time, (n,m) in buspair}:
(if Ccond[t,n,m] then -lambda15[t,n,m]+lambda16[t,n,m] else lambda22[t,n,m])
+sum {(l,n,m) in branch_from}
 Vt[t,n]*Vt[t,m]*(cospsin[t,l,n,m]*lambda3[t,l,n,m]+cospsin[t,l,m,n]*lambda4[t,l,m,n]-cosmsin[t,l,n,m]*lambda5[t,l,n,m]-cosmsin[t,l,m,n]*lambda6[t,l,m,n])/tap[l]
 = 0;

subject to dual_vsoa {t in time, l in line}:
 sum {(l,n,m) in branch_from: Vcond[t,l,n,m]} (lambda17[t,l,n,m]-lambda20[t,l,n,m])/2
-sum {(l,n,m) in branch_from} (lambda3[t,l,n,m]+lambda4[t,l,m,n])/2
+sum {(l,n,m) in branch_from: !Vcond[t,l,n,m]} lambda21[t,l,n,m] = 0; 
 
subject to dual_cone_cosf {t in time, (n,m) in buspair: Ccond[t,n,m]}:
 lambda14[t,n,m]^2 + lambda15[t,n,m]^2 <= lambda16[t,n,m]^2;

subject to dual_cone_vsoa {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]}:
 lambda17[t,l,n,m]^2 + lambda18[t,l,n,m]^2 + lambda19[t,l,n,m]^2 <= lambda20[t,l,n,m]^2;

subject to dual_cone_PQ {t in time, (l,n,m) in branch: Scond[t,l,n,m]}:
 lambda11[t,l,n,m]^2 + lambda12[t,l,n,m]^2 <= lambda13[t,l,n,m]^2;
 
 
subject to mi1maxc {t in time, g in gen}:
 mi1max[t,g] >= 0;

subject to mi1minc {t in time, g in gen}:
 mi1min[t,g] >= 0;

subject to mi2maxc {t in time, g in gen}:
 mi2max[t,g] >= 0;

subject to mi2minc {t in time, g in gen}:
 mi2min[t,g] >= 0;
 
subject to mi3maxc {t in time, n in bus}:
 mi3max[t,n] >= 0;

subject to mi3minc {t in time, n in bus}:
 mi3min[t,n] >= 0;





