# Bilevel-AC-OPF

This repository contains optimization code of the paper "Solving Bilevel AC OPF Problems Using Smoothing Solution Techniques".

To run the code:

	Use AMPL
	
	Bilevel-AC-OPF folder should be project directory
	
	run free\QP\SM2.run (other files in that directory solve using different solution techniques)
	
	transmission network can be changed in "input_data.run"
	
In the path, i.e. folder name, "free" refers to variable bounds (they are +-Inf) while QP refers to the lower-level objective function treatment for derivng the dual.

By default, KNITRO and Xpress solvers are used.