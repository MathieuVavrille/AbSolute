var a;
var b;
var x;
var y;

subject to

cons1:  3*x^2-2*x-a = 0;
cons2:  x^3-x^2-x*a+a-2*b-2 = 0;
cons3:  3*y^2-2*y-a = 0;
cons4:  y^3-y^2-y*a-a+2 = 0;

#solve;
#display a, b, x, y;

# TITLE : the system of Solotarev from the PoSSo test suite

# ROOT COUNTS :

# total degree : 36
# 4-homogeneous Bezout number : 10
#   with partition {{x }{a }{b }{y }}
# generalized Bezout number : 8
#   with the set structure :
#     {x a }{x }
#     {x b }{x a }{x }
#     {a y }{y }
#     {a y }{y }{y }
# mixed volume : 6

# REFERENCES :

# See the PoSSo test suite.

# THE SOLUTIONS :

# 6 4
# ===========================================================
# solution 1 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x : -1.00000016764979E+00   8.30237643136911E-08
#  a :  5.00000134119829E+00  -6.64190114509508E-07
#  b :  3.00000134119829E+00  -6.64190114509508E-07
#  y : -1.00000016764979E+00   8.30237643136911E-08
# == err :  1.497E-06 = rco :  1.393E-08 = res :  1.402E-13 ==
# solution 2 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x :  1.66666683444954E+00  -8.29578757360181E-08
#  a :  5.00000134226302E+00  -6.63663005888127E-07
#  b : -1.74074118816175E+00   2.21221001962709E-07
#  y : -1.00000016778288E+00   8.29578757360185E-08
# == err :  1.496E-06 = rco :  1.980E-08 = res :  1.400E-13 ==
# solution 3 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x : -3.33333333333333E-01   0.00000000000000E+00
#  a :  1.00000000000000E+00   0.00000000000000E+00
#  b : -4.07407407407407E-01   0.00000000000000E+00
#  y :  1.00000000000000E+00   0.00000000000000E+00
# == err :  4.163E-16 = rco :  2.522E-01 = res :  5.551E-17 ==
# solution 4 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x : -9.99999867089384E-01  -1.49761124852549E-07
#  a :  4.99999893671507E+00   1.19808899882038E-06
#  b :  2.99999893671507E+00   1.19808899882038E-06
#  y : -9.99999867089384E-01  -1.49761124852549E-07
# == err :  1.602E-06 = rco :  1.570E-08 = res :  1.604E-13 ==
# solution 5 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x :  1.00000000000000E+00   0.00000000000000E+00
#  a :  1.00000000000000E+00   0.00000000000000E+00
#  b : -1.00000000000000E+00   0.00000000000000E+00
#  y :  1.00000000000000E+00   0.00000000000000E+00
# == err :  0.000E+00 = rco :  4.667E-01 = res :  0.000E+00 ==
# solution 6 :
# t :  1.00000000000000E+00   0.00000000000000E+00
# m : 1
# the solution for t :
#  x :  1.66666653366608E+00   1.49659837765391E-07
#  a :  4.99999893599533E+00   1.19727870212311E-06
#  b : -1.74074038607252E+00  -3.99092900707705E-07
#  y : -9.99999866999416E-01  -1.49659837765391E-07
# == err :  1.602E-06 = rco :  2.232E-08 = res :  1.604E-13 ==
