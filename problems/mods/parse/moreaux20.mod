# Domains
var x1 >= -4, <= 5;
var x2 >= -4, <= 5;
var x3 >= -4, <= 5;
var x4 >= -4, <= 5;
var x5 >= -4, <= 5;
var x6 >= -4, <= 5;
var x7 >= -4, <= 5;
var x8 >= -4, <= 5;
var x9 >= -4, <= 5;
var x10 >= -4, <= 5;
var x11 >= -4, <= 5;
var x12 >= -4, <= 5;
var x13 >= -4, <= 5;
var x14 >= -4, <= 5;
var x15 >= -4, <= 5;
var x16 >= -4, <= 5;
var x17 >= -4, <= 5;
var x18 >= -4, <= 5;
var x19 >= -4, <= 5;
var x20 >= -4, <= 5;
var l0 >= -1.0e16, <= 1.0e16;
var l1 >= -1.0e16, <= 1.0e16;
var l2 >= -1.0e16, <= 1.0e16;
var l3 >= -1.0e16, <= 1.0e16;
var l4 >= -1.0e16, <= 1.0e16;
var l5 >= -1.0e16, <= 1.0e16;
var l6 >= -1.0e16, <= 1.0e16;
var l7 >= -1.0e16, <= 1.0e16;
var l8 >= -1.0e16, <= 1.0e16;
var l9 >= -1.0e16, <= 1.0e16;
var l10 >= -1.0e16, <= 1.0e16;
var l11 >= -1.0e16, <= 1.0e16;
var l12 >= -1.0e16, <= 1.0e16;
var l13 >= -1.0e16, <= 1.0e16;
var l14 >= -1.0e16, <= 1.0e16;
var l15 >= -1.0e16, <= 1.0e16;
var l16 >= -1.0e16, <= 1.0e16;
var l17 >= -1.0e16, <= 1.0e16;
var l18 >= -1.0e16, <= 1.0e16;
var l19 >= -1.0e16, <= 1.0e16;
var l20 >= -1.0e16, <= 1.0e16;
var u1 >= -1.0e16, <= 1.0e16;
var u2 >= -1.0e16, <= 1.0e16;
var u3 >= -1.0e16, <= 1.0e16;
var u4 >= -1.0e16, <= 1.0e16;
var u5 >= -1.0e16, <= 1.0e16;
var u6 >= -1.0e16, <= 1.0e16;
var u7 >= -1.0e16, <= 1.0e16;
var u8 >= -1.0e16, <= 1.0e16;
var u9 >= -1.0e16, <= 1.0e16;
var u10 >= -1.0e16, <= 1.0e16;
var u11 >= -1.0e16, <= 1.0e16;
var u12 >= -1.0e16, <= 1.0e16;
var u13 >= -1.0e16, <= 1.0e16;
var u14 >= -1.0e16, <= 1.0e16;
var u15 >= -1.0e16, <= 1.0e16;
var u16 >= -1.0e16, <= 1.0e16;
var u17 >= -1.0e16, <= 1.0e16;
var u18 >= -1.0e16, <= 1.0e16;
var u19 >= -1.0e16, <= 1.0e16;
var u20 >= -1.0e16, <= 1.0e16;
var u21 >= -1.0e16, <= 1.0e16;

# Constants
param h := 1/(20+1);
param t1 := 1 * h;
param t2 := 2 * h;
param t3 := 3 * h;
param t4 := 4 * h;
param t5 := 5 * h;
param t6 := 6 * h;
param t7 := 7 * h;
param t8 := 8 * h;
param t9 := 9 * h;
param t10 := 10 * h;
param t11 := 11 * h;
param t12 := 12 * h;
param t13 := 13 * h;
param t14 := 14 * h;
param t15 := 15 * h;
param t16 := 16 * h;
param t17 := 17 * h;
param t18 := 18 * h;
param t19 := 19 * h;
param t20 := 20 * h;

subject to
cons1 : l0 = 0;
cons2 : l1 = l0 + t1*(x1+t1+1)^3;
cons3 : l2 = l1 + t2*(x2+t2+1)^3;
cons4 : l3 = l2 + t3*(x3+t3+1)^3;
cons5 : l4 = l3 + t4*(x4+t4+1)^3;
cons6 : l5 = l4 + t5*(x5+t5+1)^3;
cons7 : l6 = l5 + t6*(x6+t6+1)^3;
cons8 : l7 = l6 + t7*(x7+t7+1)^3;
cons9 : l8 = l7 + t8*(x8+t8+1)^3;
cons10 : l9 = l8 + t9*(x9+t9+1)^3;
cons11 : l10 = l9 + t10*(x10+t10+1)^3;
cons12 : l11 = l10 + t11*(x11+t11+1)^3;
cons13 : l12 = l11 + t12*(x12+t12+1)^3;
cons14 : l13 = l12 + t13*(x13+t13+1)^3;
cons15 : l14 = l13 + t14*(x14+t14+1)^3;
cons16 : l15 = l14 + t15*(x15+t15+1)^3;
cons17 : l16 = l15 + t16*(x16+t16+1)^3;
cons18 : l17 = l16 + t17*(x17+t17+1)^3;
cons19 : l18 = l17 + t18*(x18+t18+1)^3;
cons20 : l19 = l18 + t19*(x19+t19+1)^3;
cons21 : l20 = l19 + t20*(x20+t20+1)^3;
cons22 : u21 = 0;
cons23 : u1 = u2 + (1-t1)*(x1+t1+1)^3;
cons24 : u2 = u3 + (1-t2)*(x2+t2+1)^3;
cons25 : u3 = u4 + (1-t3)*(x3+t3+1)^3;
cons26 : u4 = u5 + (1-t4)*(x4+t4+1)^3;
cons27 : u5 = u6 + (1-t5)*(x5+t5+1)^3;
cons28 : u6 = u7 + (1-t6)*(x6+t6+1)^3;
cons29 : u7 = u8 + (1-t7)*(x7+t7+1)^3;
cons30 : u8 = u9 + (1-t8)*(x8+t8+1)^3;
cons31 : u9 = u10 + (1-t9)*(x9+t9+1)^3;
cons32 : u10 = u11 + (1-t10)*(x10+t10+1)^3;
cons33 : u11 = u12 + (1-t11)*(x11+t11+1)^3;
cons34 : u12 = u13 + (1-t12)*(x12+t12+1)^3;
cons35 : u13 = u14 + (1-t13)*(x13+t13+1)^3;
cons36 : u14 = u15 + (1-t14)*(x14+t14+1)^3;
cons37 : u15 = u16 + (1-t15)*(x15+t15+1)^3;
cons38 : u16 = u17 + (1-t16)*(x16+t16+1)^3;
cons39 : u17 = u18 + (1-t17)*(x17+t17+1)^3;
cons40 : u18 = u19 + (1-t18)*(x18+t18+1)^3;
cons41 : u19 = u20 + (1-t19)*(x19+t19+1)^3;
cons42 : u20 = u21 + (1-t20)*(x20+t20+1)^3;
cons43 : 0 = x1+0.5*h*((1-t1)*l1 + t1*u2);
cons44 : 0 = x2+0.5*h*((1-t2)*l2 + t2*u3);
cons45 : 0 = x3+0.5*h*((1-t3)*l3 + t3*u4);
cons46 : 0 = x4+0.5*h*((1-t4)*l4 + t4*u5);
cons47 : 0 = x5+0.5*h*((1-t5)*l5 + t5*u6);
cons48 : 0 = x6+0.5*h*((1-t6)*l6 + t6*u7);
cons49 : 0 = x7+0.5*h*((1-t7)*l7 + t7*u8);
cons50 : 0 = x8+0.5*h*((1-t8)*l8 + t8*u9);
cons51 : 0 = x9+0.5*h*((1-t9)*l9 + t9*u10);
cons52 : 0 = x10+0.5*h*((1-t10)*l10 + t10*u11);
cons53 : 0 = x11+0.5*h*((1-t11)*l11 + t11*u12);
cons54 : 0 = x12+0.5*h*((1-t12)*l12 + t12*u13);
cons55 : 0 = x13+0.5*h*((1-t13)*l13 + t13*u14);
cons56 : 0 = x14+0.5*h*((1-t14)*l14 + t14*u15);
cons57 : 0 = x15+0.5*h*((1-t15)*l15 + t15*u16);
cons58 : 0 = x16+0.5*h*((1-t16)*l16 + t16*u17);
cons59 : 0 = x17+0.5*h*((1-t17)*l17 + t17*u18);
cons60 : 0 = x18+0.5*h*((1-t18)*l18 + t18*u19);
cons61 : 0 = x19+0.5*h*((1-t19)*l19 + t19*u20);
cons62 : 0 = x20+0.5*h*((1-t20)*l20 + t20*u21);

#solve;
#display l0, l1, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19, l2, l20, l3, l4, l5, l6, l7, l8, l9, u1, u10, u11, u12, u13, u14, u15, u16, u17, u18, u19, u2, u20, u21, u3, u4, u5, u6, u7, u8, u9, x1, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x2, x20, x3, x4, x5, x6, x7, x8, x9;
