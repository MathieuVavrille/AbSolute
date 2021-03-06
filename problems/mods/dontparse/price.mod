# price.mod	OBR2-AN-2-4
# Original AMPL coding by Elena Bobrovnikova (summer 1996 at Bell Labs).

# Ref.: C. Jansson and O. Knueppel, "A Global Minimization Method:
# the Multi-Dimensional Case", Technische Informatik III,
# TU Hamburg-Hamburg, Jan. 1992, p. 69 (problem "P").

# Price function

# Number of variables: 2
# Number of constraints: 4
# Objective nonseparable, nonconvex
# Simple bound constraints

# There are three global minima with Fprice = 0. x = (0,0), x = (2,4) and
# x = (1.464352,-2.506012).

var x{1 .. 2} <= 10, >= -10;

param best_val_found := 1.007582517e-13;
param eps := 1; 		# = max(1, 1% x best_val_found)

subject to Fprice:
         (2 * x[1]^3 * x[2] - x[2]^3)^2 + (6*x[1] - x[2]^2 + x[2])^2 <= best_val_found + eps;


data;
var x :=
    1   1
    2   1;

#solve;

##display Fprice;

##display Fprice - 0;
#display x;
