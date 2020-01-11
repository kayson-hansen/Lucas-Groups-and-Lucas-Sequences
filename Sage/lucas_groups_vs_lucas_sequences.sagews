︠f93b2ff2-b3c3-4bfe-bc0d-34e0eb671cf2s︠
import random
from math import sqrt
#from arith_lib import gcd
from fractions import Fraction
from itertools import product
from collections import OrderedDict
from random import choice

#finds the elements of a Lucas Group
def elements(D, p):
    solutions = []
    for X in range(0, p):
        for Y in range(0, p):
            if (X**2 - D*Y**2)%p == 4%p:
                solutions.append((X,Y))
    solutions = set(solutions)
    return solutions

def bin_op(x, y, D, p):
    return ((x[0]*y[0]+D*x[1]*y[1])*2.inverse_mod(p) % p, (x[0]*y[1]+x[1]*y[0])*2.inverse_mod(p) % p)

#tests if an element is a generator of the Lucas Group
def gen_test(element, D, p):
    order_ele = 0
    new_element = element
    f = factor(p)
    max_order = 1
    for i in f:
        max_order *= 3*i[0]**i[1]/2
    for i in range(2, max_order):
        new_element = bin_op(new_element, element, D, p)
        if new_element == (2,0):
            order_ele = i
            break
    if p in Primes():
        if order_ele == p-1 or order_ele == p+1:
            return True
        elif order_ele == (p+1)/2:
            return "Almost"
        else:
            return False
    elif p not in Primes() and is_prime_power(p):
        p0 = divisors(p)[1]
        if jacobi_symbol(D, p0) == 1:
            if order_ele == p*(p0-1)/p0:
                return True
            else:
                return False
        elif jacobi_symbol(D, p0) == -1:
            if order_ele == p*(p0+1)/p0:
                return True
            else:
                return False
        elif jacobi_symbol(D, p0) == 0:
            if order_ele == 2*p:
                return True
            else:
                return False
    else:
        new_order = 1
        for i in f:
            new_order = lcm(new_order, len(elements(D,i[0])))
        if order_ele == new_order:
            return True
        else:
            return False


#because the Lucas Sequence mod p forms a cyclic subgroup, we can compute it by finding the order of the generator, (P,1)
def lucas_sequence(P, p, D):
    #code to test your conjecture that \Omega = 2\omega
    sequence_ = [(2,0), (-P,1)]
    while sequence_[-1] != (2,0):
        sequence_.append(((sequence_[-1][0]*(-P)-sequence_[-2][0]) % p, (sequence_[-1][1]*(-P)-sequence_[-2][1]) % p))
    order1 = len(sequence_) - 1
    generator = (P,1)
    element = (P,1)
    sequence = [(2,0), (P,1)]
    while sequence[-1] != (2,0):
        sequence.append(((sequence[-1][0]*P-sequence[-2][0]) % p , (sequence[-1][1]*P-sequence[-2][1]) % p))
    order2 = len(sequence) - 1
    #if order1 % 2 == 1:
    #    if sequence[order2/2][1] == 0:
    #        print "True"
    #    else:
    #        print "False"
    #if order2 % 2 == 1:
    #    if sequence_[order1/2][1] == 0:
    #        print "True"
    #    else:
    #        print "False"
    return len(sequence) - 1
    for i in range(1, p**2):
        element = bin_op(generator, element, D, p)
        if element == (2,0):
            return i+1


#this was for testing irreducibility
#for i in range(5, 37):
#    if i in Primes():
#        print "p=", i
#        lucas_sequence_polys(i)

def order(x, p):
    order_x = 0
    for i in range(1, p):
        if x**i % p == 1:
            order_x = i
            break
    return order_x

def is_prime(p):
	prime = True
	for i in range(2, int(sqrt(p)+1)):
		if p % i == 0:
			prime = False
			break
	return prime

def probable_test(n, P):
    generator = (P,1)
    element = (P,1)
    for i in range(1, n - jacobi_symbol(P^2-4, n)):
        element = bin_op(generator, element, P^2-4, n)
    if element[1] == 0:
        return "Pseudoprime"
    else:
        return "Not Pseudoprime"

#implements the Strong Lucas Pseudoprime test
def strong_test(n, P):
    f = list(factor(p-jacobi_symbol(P^2-4 % n, p)))
    s = 0
    for j in f:
        if j[0] == 2:
            s = j[1]
            break
    q = (p-jacobi_symbol(D, p))/2**s
    generator = (P,1)
    element = (P,1)
    lucas_sequence = [(2,0), (P,1)]
    for i in range(2, n - jacobi_symbol(P^2-4, n)+1):
        element = bin_op(generator, element, P^2-4, n)
        lucas_sequence.append(element)
    if lucas_sequence[q][1] == 0:
        return "Strong Pseudoprime"
    else:
        for r in range(0, s):
            if lucas_sequence[q*2**r][0] == 0:
                return "Strong Pseudoprime"
        return "Not Strong Pseudoprime"


#also for jacobi_symbol = 1
def gen_order(p, a, P):
    order_P = 0
    d = Mod(P**2-4,p).sqrt()
    b = Integer(a).inverse_mod(p)
    element = ((a+b) % p , (a-b)*(Integer(d).inverse_mod(p)) % p)
    if p in Primes():
        for i in range(1, p+1):
            if ((a**i+b**i) % p , (a**i-b**i)*(Integer(d).inverse_mod(p)) % p) == (P,1):
                order_P = i
                break
    elif p not in Primes():
        for i in range(1, euler_phi(p)+1):
            if ((a**i+b**i) % p , (a**i-b**i)*(Integer(d).inverse_mod(p)) % p) == (P,1):
                order_P = i
    return [element, order_P]


#tests if an ordered pair (a,b) is a primitive element in the field F_q^2
def primitive_test(p, D):
    generators = []
    for a in range(1, p):
        for b in range(1, p):
            element = (a,b)
            order_ab = 0
            for i in range(2, p**2):
                element = ((a*element[0] + D*b*element[1]) % p , (a*element[1] + b*element[0]) % p)
                if element == (1,0):
                    order_ab = i
                    break
            if order_ab == p**2-1:
                generators.append((a,b))
    return generators

def simple_primitive_test(p):
    generators = []
    for x in range(2, p):
        if Mod(x,p).multiplicative_order() == p-1:
            generators.append((x+x^{-1}) % p)
    return generators

def new_weak_primality_test(P, D, p):
    lucas_group = list(elements(D,p))
    generator = choice(lucas_group)
    element = generator
    for i in range(2, p - jacobi_symbol(D, p)+1):
        element = bin_op(generator, element, D, p)
    if element == (2,0):
        return True

def new_strong_primality_test(P, D, p):
    solutions = []
    for X in range(0, p):
        for Y in range(0, p):
            if (X**2 - D*Y**2)%p == 1%p:
                solutions.append((X,Y))
    lucas_group = list(set(solutions))
    generator = choice(lucas_group)
    element = generator
    f = list(factor(p-jacobi_symbol(D, p)))
    s = 0
    for j in f:
        if j[0] == 2:
            s = j[1]
            break
    q = (p-jacobi_symbol(D, p))/2**s
    powers = [(1,0), generator]
    for i in range(2, p-jacobi_symbol(D, p)+1):
        element = ((element[0]*generator[0]+D*element[1]*generator[1]) % p, (element[0]*generator[1]+element[1]*generator[0]) % p)
        powers.append(element)
    if powers[q] == (1,0):
        return True
    else:
        for r in range(0, s):
            if powers[q*(2**r)] == (-1,0):
                return True

def new_primality_test(P, D, p):
    lucas_group = list(elements(D,p))
    generator = choice(lucas_group)
    lucas_group = [(2,0), generator]
    element = generator
    f = list(factor(p-jacobi_symbol(D, p)))
    s = 0
    for j in f:
        if j[0] == 2:
            s = j[1]
            break
    q = (p-jacobi_symbol(D, p))/2**s
    for i in range(2, p-jacobi_symbol(D, p)+1):
        element = bin_op(generator, element, D, p)
        lucas_group.append(element)
    if lucas_group[q][1] == 0:
        return True
    else:
        for r in range(0, s):
            if lucas_group[q*2**r][0] == 0:
                return True
    return False

print("p | Order of Lucas Group | P | Order of Lucas Sequence | Ratio of Orders\n")
for p in range(3, 100):
    if p % 2 == 1:
        i = 0
        strong_pseudos = 0
        pseudos = 0
        luc_group_pseudos = 0
        weak_luc_group_pseudos = 0
        n = 0
        print p
        for P in range(1, p):
            D = (P**2-4) % p
            ratio = len(elements(D,p))/lucas_sequence(P,p,D)
            if ratio == 1:
                n += 1
            print p, "\t", len(elements(D,p)), "\t\t", P, "\t\t\t", lucas_sequence(P,p,D), "\t\t\t", ratio
            if strong_test(p, P) == "Strong Pseudoprime":
                strong_pseudos += 1
            if probable_test(p, P) == "Pseudoprime":
                pseudos += 1
            if new_strong_primality_test(P,D,p) == True:
                luc_group_pseudos += 1
            if new_weak_primality_test(P,D,p) == True:
                weak_luc_group_pseudos += 1
        print "Number of Strong Pseudoprimes: ", Rational(strong_pseudos)
        print "Number of Pseudoprimes: ", Rational(pseudos)
        print "Number of Lucas Group Pseudoprimes: ", Rational(weak_luc_group_pseudos)
        print "Number of Strong Lucas Group Pseudoprimes: ", Rational(luc_group_pseudos)
        print n

        print "\n"
︡527aebc4-3027-49a6-ae7c-fbff1992bc2d︡{"stdout":"p | Order of Lucas Group | P | Order of Lucas Sequence | Ratio of Orders\n\n"}︡{"stdout":"3\n3 \t6 \t\t1 \t\t\t6 \t\t\t1\n3 \t6 \t\t2 \t\t\t3 \t\t\t2\nNumber of Strong Pseudoprimes:  2\nNumber of Pseudoprimes:  2\nNumber of Lucas Group Pseudoprimes:  1\nNumber of Strong Lucas Group Pseudoprimes:  2\n1\n\n\n5\n5 \t6 \t\t1 \t\t\t6 \t\t\t1\n5 \t10 \t\t2 \t\t\t5 \t\t\t2\n5 \t10 \t\t3 \t\t\t10 \t\t\t1\n5 \t6 \t\t4 \t\t\t3 \t\t\t2\nNumber of Strong Pseudoprimes:  4\nNumber of Pseudoprimes:  4\nNumber of Lucas Group Pseudoprimes:  2\nNumber of Strong Lucas Group Pseudoprimes:  1\n2\n\n\n7\n7 \t6 \t\t1 \t\t\t6 \t\t\t1\n7 \t14 \t\t2 \t\t\t7 \t\t\t2\n7 \t8 \t\t3 \t\t\t8 \t\t\t1\n7 \t8 \t\t4 \t\t\t8 \t\t\t1\n7 \t14 \t\t5 \t\t\t14 \t\t\t1\n7 \t6 \t\t6 \t\t\t3 \t\t\t2\nNumber of Strong Pseudoprimes:  6\nNumber of Pseudoprimes:  6\nNumber of Lucas Group Pseudoprimes:  6\nNumber of Strong Lucas Group Pseudoprimes:  1\n4\n\n\n9\n9 \t18 \t\t1 \t\t\t6 \t\t\t3\n9 \t18 \t\t2 \t\t\t9 \t\t\t2\n9 \t12 \t\t3 \t\t\t12 \t\t\t1\n9 \t18 \t\t4 \t\t\t18 \t\t\t1\n9 \t18 \t\t5 \t\t\t9 \t\t\t2\n9 \t12 \t\t6 \t\t\t12 \t\t\t1\n9 \t18 \t\t7 \t\t\t18 \t\t\t1\n9 \t18 \t\t8 \t\t\t3 \t\t\t6\nNumber of Strong Pseudoprimes:  6\nNumber of Pseudoprimes:  6\nNumber of Lucas Group Pseudoprimes:  3\nNumber of Strong Lucas Group Pseudoprimes:  5\n4\n\n\n11\n11 \t12 \t\t1 \t\t\t6 \t\t\t2\n11 \t22 \t\t2 \t\t\t11 \t\t\t2\n11 \t10 \t\t3 \t\t\t5 \t\t\t2\n11 \t10 \t\t4 \t\t\t10 \t\t\t1\n11 \t12 \t\t5 \t\t\t12 \t\t\t1\n11 \t12 \t\t6 \t\t\t12 \t\t\t1\n11 \t10 \t\t7 \t\t\t5 \t\t\t2\n11 \t10 \t\t8 \t\t\t10 \t\t\t1\n11 \t22 \t\t9 \t\t\t22 \t\t\t1\n11 \t12 \t\t10 \t\t\t3 \t\t\t4\nNumber of Strong Pseudoprimes:  10\nNumber of Pseudoprimes:  10\nNumber of Lucas Group Pseudoprimes:  10\nNumber of Strong Lucas Group Pseudoprimes:  4\n5\n\n\n13\n13 \t12 \t\t1 \t\t\t6 \t\t\t2\n13 \t26 \t\t2 \t\t\t13 \t\t\t2\n13 \t14 \t\t3 \t\t\t14 \t\t\t1\n13 \t12 \t\t4 \t\t\t12 \t\t\t1\n13 \t14 \t\t5 \t\t\t14 \t\t\t1\n13 \t14 \t\t6 \t\t\t14 \t\t\t1\n13 \t14 \t\t7 \t\t\t7 \t\t\t2\n13 \t14 \t\t8 \t\t\t7 \t\t\t2\n13 \t12 \t\t9 \t\t\t12 \t\t\t1\n13 \t14 \t\t10 \t\t\t7 \t\t\t2\n13 \t26 \t\t11 \t\t\t26 \t\t\t1\n13 \t12 \t\t12 \t\t\t3 \t\t\t4\nNumber of Strong Pseudoprimes:  12\nNumber of Pseudoprimes:  12\nNumber of Lucas Group Pseudoprimes:  10\nNumber of Strong Lucas Group Pseudoprimes:  5\n6\n\n\n15\n15 \t36 \t\t1 \t\t\t6 \t\t\t6\n15 \t60 \t\t2 \t\t\t15 \t\t\t4\n15 \t40 \t\t3 \t\t\t20 \t\t\t2\n15 \t36 \t\t4 \t\t\t6 \t\t\t6\n15 \t24 \t\t5 \t\t\t12 \t\t\t2\n15 \t24 \t\t6 \t\t\t12 \t\t\t2\n15 \t60 \t\t7 \t\t\t30 \t\t\t2\n15"}︡{"stdout":" \t60 \t\t8 \t\t\t30 \t\t\t2\n15 \t24 \t\t9 \t\t\t12 \t\t\t2\n15 \t24 \t\t10 \t\t\t12 \t\t\t2\n15 \t36 \t\t11 \t\t\t6 \t\t\t6\n15 \t40 \t\t12 \t\t\t20 \t\t\t2\n15 \t60 \t\t13 \t\t\t30 \t\t\t2\n15 \t36 \t\t14 \t\t\t3 \t\t\t12\nNumber of Strong Pseudoprimes:  8\nNumber of Pseudoprimes:  8\nNumber of Lucas Group Pseudoprimes:  3\nNumber of Strong Lucas Group Pseudoprimes:  2\n0\n\n\n17\n17 \t18 \t\t1 \t\t\t6 \t\t\t3\n17 \t34 \t\t2 \t\t\t17 \t\t\t2\n17 \t18 \t\t3 \t\t\t18 \t\t\t1\n17 \t18 \t\t4 \t\t\t18 \t\t\t1\n17 \t16 \t\t5 \t\t\t16 \t\t\t1\n17 \t16 \t\t6 \t\t\t8 \t\t\t2\n17 \t18 \t\t7 \t\t\t9 \t\t\t2\n17 \t16 \t\t8 \t\t\t16 \t\t\t1\n17 \t16 \t\t9 \t\t\t16 \t\t\t1\n17 \t18 \t\t10 \t\t\t18 \t\t\t1\n17 \t16 \t\t11 \t\t\t8 \t\t\t2\n17 \t16 \t\t12 \t\t\t16 \t\t\t1\n17 \t18 \t\t13 \t\t\t9 \t\t\t2\n17 \t18 \t\t14 \t\t\t9 \t\t\t2\n17 \t34 \t\t15 \t\t\t34 \t\t\t1\n17 \t18 \t\t16 \t\t\t3 \t\t\t6\nNumber of Strong Pseudoprimes:  16\nNumber of Pseudoprimes:  16\nNumber of Lucas Group Pseudoprimes:  15\nNumber of Strong Lucas Group Pseudoprimes:  6\n8\n\n\n19\n19 \t18 \t\t1 \t\t\t6 \t\t\t3\n19 \t38 \t\t2 \t\t\t19 \t\t\t2\n19 \t18 \t\t3 \t\t\t9 \t\t\t2\n19 \t20 \t\t4 \t\t\t5 \t\t\t4\n19 \t20 \t\t5 \t\t\t10 \t\t\t2\n19 \t20 \t\t6 \t\t\t20 \t\t\t1\n19 \t18 \t\t7 \t\t\t9 \t\t\t2\n19"}︡{"stdout":" \t20 \t\t8 \t\t\t20 \t\t\t1\n19 \t18 \t\t9 \t\t\t9 \t\t\t2\n19 \t18 \t\t10 \t\t\t18 \t\t\t1\n19 \t20 \t\t11 \t\t\t20 \t\t\t1\n19 \t18 \t\t12 \t\t\t18 \t\t\t1\n19 \t20 \t\t13 \t\t\t20 \t\t\t1\n19 \t20 \t\t14 \t\t\t5 \t\t\t4\n19 \t20 \t\t15 \t\t\t10 \t\t\t2\n19 \t18 \t\t16 \t\t\t18 \t\t\t1\n19 \t38 \t\t17 \t\t\t38 \t\t\t1\n19"}︡{"stdout":" \t18 \t\t18 \t\t\t3 \t\t\t6\nNumber of Strong Pseudoprimes:  18\nNumber of Pseudoprimes:  18\nNumber of Lucas Group Pseudoprimes:  16\nNumber of Strong Lucas Group Pseudoprimes:  8\n8\n\n\n21\n21 \t36 \t\t1 \t\t\t6 \t\t\t6\n21 \t84 \t\t2 \t\t\t21 \t\t\t4\n21 \t32 \t\t3 \t\t\t8 \t\t\t4\n21 \t48 \t\t4 \t\t\t24 \t\t\t2\n21 \t84 \t\t5 \t\t\t42 \t\t\t2\n21 \t24 \t\t6 \t\t\t12 \t\t\t2\n21 \t48 \t\t7 \t\t\t12 \t\t\t4\n21 \t36 \t\t8 \t\t\t6 \t\t\t6\n21 \t56 \t\t9 \t\t\t28 \t\t\t2\n21 \t48 \t\t10 \t\t\t24 \t\t\t2\n21 \t48 \t\t11 \t\t\t24 \t\t\t2\n21 \t56 \t\t12 \t\t\t28 \t\t\t2\n21 \t36 \t\t13 \t\t\t6 \t\t\t6\n21 \t48 \t\t14 \t\t\t12 \t\t\t4\n21 \t24 \t\t15 \t\t\t12 \t\t\t2\n21 \t84 \t\t16 \t\t\t42 \t\t\t2\n21 \t48 \t\t17 \t\t\t24 \t\t\t2\n21 \t32 \t\t18 \t\t\t8 \t\t\t4\n21"}︡{"stdout":" \t84 \t\t19 \t\t\t42 \t\t\t2\n21 \t36 \t\t20 \t\t\t3 \t\t\t12\nNumber of Strong Pseudoprimes:  8\nNumber of Pseudoprimes:  10\nNumber of Lucas Group Pseudoprimes:  2\nNumber of Strong Lucas Group Pseudoprimes:  1\n0\n\n\n23\n23 \t24 \t\t1 \t\t\t6 \t\t\t4\n23 \t46 \t\t2 \t\t\t23 \t\t\t2\n23 \t24 \t\t3 \t\t\t24 \t\t\t1\n23 \t22 \t\t4 \t\t\t11 \t\t\t2\n23 \t24 \t\t5 \t\t\t8 \t\t\t3\n23 \t22 \t\t6 \t\t\t11 \t\t\t2\n23 \t24 \t\t7 \t\t\t12 \t\t\t2\n23 \t24 \t\t8 \t\t\t24 \t\t\t1\n23 \t22 \t\t9 \t\t\t22 \t\t\t1\n23 \t22 \t\t10 \t\t\t11 \t\t\t2\n23"}︡{"stdout":" \t22 \t\t11 \t\t\t11 \t\t\t2\n23 \t22 \t\t12 \t\t\t22 \t\t\t1\n23 \t22 \t\t13 \t\t\t22 \t\t\t1\n23 \t22 \t\t14 \t\t\t11 \t\t\t2\n23 \t24 \t\t15 \t\t\t24 \t\t\t1\n23 \t24 \t\t16 \t\t\t12 \t\t\t2\n23 \t22 \t\t17 \t\t\t22 \t\t\t1\n23 \t24 \t\t18 \t\t\t8 \t\t\t3\n23 \t22 \t\t19 \t\t\t22 \t\t\t1\n23 \t24"}︡{"stdout":" \t\t20 \t\t\t24 \t\t\t1\n23 \t46 \t\t21 \t\t\t46 \t\t\t1\n23 \t24 \t\t22 \t\t\t3 \t\t\t8\nNumber of Strong Pseudoprimes:  22\nNumber of Pseudoprimes:  22\nNumber of Lucas Group Pseudoprimes:  22\nNumber of Strong Lucas Group Pseudoprimes:  8\n10\n\n\n25\n25 \t30 \t\t1 \t\t\t6 \t\t\t5\n25 \t50 \t\t2 \t\t\t25 \t\t\t2\n25 \t50 \t\t3 \t\t\t50 \t\t\t1\n25 \t30 \t\t4 \t\t\t15 \t\t\t2\n25 \t20 \t\t5 \t\t\t20 \t\t\t1\n25"}︡{"stdout":" \t30 \t\t6 \t\t\t30 \t\t\t1\n25 \t50 \t\t7 \t\t\t25 \t\t\t2\n25 \t50 \t\t8 \t\t\t50 \t\t\t1\n25 \t30 \t\t9 \t\t\t15 \t\t\t2\n25 \t20 \t\t10 \t\t\t20 \t\t\t1\n25 \t30 \t\t11 \t\t\t30 \t\t\t1\n25 \t50 \t\t12 \t\t\t25 \t\t\t2\n25 \t50 \t\t13 \t\t\t50 \t\t\t1\n25 \t30 \t\t14 \t\t\t15 \t\t\t2\n25 \t20"}︡{"stdout":" \t\t15 \t\t\t20 \t\t\t1\n25 \t30 \t\t16 \t\t\t30 \t\t\t1\n25 \t50 \t\t17 \t\t\t25 \t\t\t2\n25 \t50 \t\t18 \t\t\t50 \t\t\t1\n25 \t30 \t\t19 \t\t\t15 \t\t\t2\n25 \t20 \t\t20 \t\t\t20 \t\t\t1\n25 \t30 \t\t21 \t\t\t30 \t\t\t1\n25 \t50 \t\t22 \t\t\t25 \t\t\t2\n25 \t50 \t\t23 \t\t\t50 \t\t\t1\n25 \t30 \t\t24 \t\t\t3 \t\t\t10\nNumber of Strong Pseudoprimes:  12\nNumber of Pseudoprimes:  12\nNumber of Lucas Group Pseudoprimes:  9\nNumber of Strong Lucas Group Pseudoprimes:  7\n13\n\n\n27\n27 \t54 \t\t1 \t\t\t6 \t\t\t9\n27 \t54 \t\t2 \t\t\t27 \t\t\t2\n27"}︡{"stdout":" \t36 \t\t3 \t\t\t36 \t\t\t1\n27 \t54 \t\t4 \t\t\t54 \t\t\t1\n27 \t54 \t\t5 \t\t\t27 \t\t\t2\n27 \t36 \t\t6 \t\t\t36 \t\t\t1\n27 \t54 \t\t7 \t\t\t54 \t\t\t1\n27 \t54 \t\t8 \t\t\t9 \t\t\t6\n27 \t36 \t\t9 \t\t\t12 \t\t\t3\n27 \t54 \t\t10 \t\t\t18 \t\t\t3\n27 \t54 \t\t11 \t\t\t27 \t\t\t2\n27 \t36 \t\t12 \t\t\t36 \t\t\t1\n27 \t54 \t\t13 \t\t\t54 \t\t\t1\n27 \t54"}︡{"stdout":" \t\t14 \t\t\t27 \t\t\t2\n27 \t36 \t\t15 \t\t\t36 \t\t\t1\n27 \t54 \t\t16 \t\t\t54 \t\t\t1\n27 \t54 \t\t17 \t\t\t9 \t\t\t6\n27 \t36 \t\t18 \t\t\t12 \t\t\t3\n27 \t54 \t\t19 \t\t\t18 \t\t\t3\n27 \t54 \t\t20 \t\t\t27 \t\t\t2\n27 \t36 \t\t21 \t\t\t36 \t\t\t1\n27"}︡{"stdout":" \t54 \t\t22 \t\t\t54 \t\t\t1\n27 \t54 \t\t23 \t\t\t27 \t\t\t2\n27 \t36 \t\t24 \t\t\t36 \t\t\t1\n27 \t54 \t\t25 \t\t\t54 \t\t\t1\n27 \t54 \t\t26 \t\t\t3 \t\t\t18\nNumber of Strong Pseudoprimes:  18\nNumber of Pseudoprimes:  18\nNumber of Lucas Group Pseudoprimes:  7\nNumber of Strong Lucas Group Pseudoprimes:  9\n12\n\n\n29\n29 \t30 \t\t1 \t\t\t6 \t\t\t5\n29 \t58 \t\t2 \t\t\t29 \t\t\t2\n29 \t28 \t\t3 \t\t\t7 \t\t\t4\n29"}︡{"stdout":" \t30 \t\t4 \t\t\t15 \t\t\t2\n29 \t30 \t\t5 \t\t\t5 \t\t\t6\n29 \t30 \t\t6 \t\t\t10 \t\t\t3\n29 \t28 \t\t7 \t\t\t7 \t\t\t4\n29 \t30 \t\t8 \t\t\t30 \t\t\t1\n29 \t30 \t\t9 \t\t\t30 \t\t\t1\n29 \t28 \t\t10 \t\t\t28"}︡{"stdout":" \t\t\t1\n29 \t28 \t\t11 \t\t\t14 \t\t\t2\n29 \t28 \t\t12 \t\t\t28 \t\t\t1\n29 \t28 \t\t13 \t\t\t28 \t\t\t1\n29 \t30 \t\t14 \t\t\t15 \t\t\t2\n29 \t30 \t\t15 \t\t\t30 \t\t\t1\n29 \t28 \t\t16 \t\t\t28 \t\t\t1\n29"}︡{"stdout":" \t28 \t\t17 \t\t\t28 \t\t\t1\n29 \t28 \t\t18 \t\t\t7 \t\t\t4\n29 \t28 \t\t19 \t\t\t28 \t\t\t1\n29 \t30 \t\t20 \t\t\t15 \t\t\t2\n29 \t30 \t\t21 \t\t\t15 \t\t\t2\n29 \t28 \t\t22 \t\t\t14 \t\t\t2\n29 \t30 \t\t23 \t\t\t5 \t\t\t6\n29 \t30 \t\t24 \t\t\t10 \t\t\t3\n29"}︡{"stdout":" \t30 \t\t25 \t\t\t30 \t\t\t1\n29 \t28 \t\t26 \t\t\t14 \t\t\t2\n29 \t58 \t\t27 \t\t\t58 \t\t\t1\n29 \t30 \t\t28 \t\t\t3 \t\t\t10\nNumber of Strong Pseudoprimes:  28\nNumber of Pseudoprimes:  28\nNumber of Lucas Group Pseudoprimes:  27\nNumber of Strong Lucas Group Pseudoprimes:  14\n11\n\n\n31\n31 \t30 \t\t1 \t\t\t6 \t\t\t5\n31 \t62 \t\t2 \t\t\t31 \t\t\t2\n31"}︡{"stdout":" \t30 \t\t3 \t\t\t15 \t\t\t2\n31 \t32 \t\t4 \t\t\t32 \t\t\t1\n31 \t32 \t\t5 \t\t\t16 \t\t\t2\n31 \t30 \t\t6 \t\t\t15 \t\t\t2\n31 \t30 \t\t7 \t\t\t15 \t\t\t2\n31 \t32 \t\t8 \t\t\t8 \t\t\t4\n31"}︡{"stdout":" \t32 \t\t9 \t\t\t32 \t\t\t1\n31 \t32 \t\t10 \t\t\t32 \t\t\t1\n31 \t32 \t\t11 \t\t\t32 \t\t\t1\n31 \t30 \t\t12 \t\t\t5 \t\t\t6\n31 \t30 \t\t13 \t\t\t10 \t\t\t3\n31 \t32 \t\t14 \t\t\t16 \t\t\t2\n31 \t30 \t\t15 \t\t\t30 \t\t\t1\n31 \t30 \t\t16 \t\t\t15 \t\t\t2\n31 \t32 \t\t17 \t\t\t16 \t\t\t2\n31"}︡{"stdout":" \t30 \t\t18 \t\t\t5 \t\t\t6\n31 \t30 \t\t19 \t\t\t10 \t\t\t3\n31 \t32 \t\t20 \t\t\t32 \t\t\t1\n31 \t32 \t\t21 \t\t\t32 \t\t\t1\n31 \t32 \t\t22 \t\t\t32 \t\t\t1\n31 \t32 \t\t23 \t\t\t8 \t\t\t4\n31 \t30 \t\t24 \t\t\t30 \t\t\t1\n31 \t30 \t\t25 \t\t\t30 \t\t\t1\n31 \t32 \t\t26 \t\t\t16 \t\t\t2\n31 \t32"}︡{"stdout":" \t\t27 \t\t\t32 \t\t\t1\n31 \t30 \t\t28 \t\t\t30 \t\t\t1\n31 \t62 \t\t29 \t\t\t62 \t\t\t1\n31 \t30 \t\t30 \t\t\t3 \t\t\t10\nNumber of Strong Pseudoprimes:  30\nNumber of Pseudoprimes:  30\nNumber of Lucas Group Pseudoprimes:  29\nNumber of Strong Lucas Group Pseudoprimes:  10\n13\n\n\n33\n33 \t72 \t\t1 \t\t\t6 \t\t\t12\n33 \t132 \t\t2 \t\t\t33 \t\t\t4\n33 \t40 \t\t3 \t\t\t20 \t\t\t2\n33"}︡{"stdout":" \t60 \t\t4 \t\t\t30 \t\t\t2\n33 \t72 \t\t5 \t\t\t12 \t\t\t6\n33 \t48 \t\t6 \t\t\t12 \t\t\t4\n33 \t60 \t\t7 \t\t\t30 \t\t\t2\n33 \t60 \t\t8 \t\t\t30 \t\t\t2\n33 \t88 \t\t9 \t\t\t44 \t\t\t2\n33"}︡{"stdout":" \t72 \t\t10 \t\t\t6 \t\t\t12\n33 \t72 \t\t11 \t\t\t12 \t\t\t6\n33 \t48 \t\t12 \t\t\t12 \t\t\t4\n33 \t132 \t\t13 \t\t\t66 \t\t\t2\n33 \t60 \t\t14 \t\t\t15 \t\t\t4\n33 \t40 \t\t15 \t\t\t20 \t\t\t2\n33 \t72 \t\t16 \t\t\t12 \t\t\t6\n33"}︡{"stdout":" \t72 \t\t17 \t\t\t12 \t\t\t6\n33 \t40 \t\t18 \t\t\t20 \t\t\t2\n33 \t60 \t\t19 \t\t\t30 \t\t\t2\n33 \t132 \t\t20 \t\t\t66 \t\t\t2\n33 \t48 \t\t21 \t\t\t12 \t\t\t4\n33 \t72 \t\t22 \t\t\t12 \t\t\t6\n33 \t72 \t\t23 \t\t\t6 \t\t\t12\n33 \t88 \t\t24 \t\t\t44 \t\t\t2\n33"}︡{"stdout":" \t60 \t\t25 \t\t\t30 \t\t\t2\n33 \t60 \t\t26 \t\t\t30 \t\t\t2\n33 \t48 \t\t27 \t\t\t12 \t\t\t4\n33 \t72 \t\t28 \t\t\t12 \t\t\t6\n33 \t60 \t\t29 \t\t\t15 \t\t\t4\n33 \t40 \t\t30 \t\t\t20 \t\t\t2\n33 \t132 \t\t31 \t\t\t66 \t\t\t2\n33 \t72 \t\t32 \t\t\t3 \t\t\t24\nNumber of Strong Pseudoprimes:  8\nNumber of Pseudoprimes:  8\nNumber of Lucas Group Pseudoprimes:  2\nNumber of Strong Lucas Group Pseudoprimes:  3\n0\n\n\n35\n35 \t36 \t\t1 \t\t\t6 \t\t\t6\n35"}︡{"stdout":" \t140 \t\t2 \t\t\t35 \t\t\t4\n35 \t80 \t\t3 \t\t\t40 \t\t\t2\n35 \t48 \t\t4 \t\t\t24 \t\t\t2\n35 \t56 \t\t5 \t\t\t28 \t\t\t2\n35 \t36 \t\t6 \t\t\t6 \t\t\t6\n35"}︡{"stdout":" \t80 \t\t7 \t\t\t20 \t\t\t4\n35 \t60 \t\t8 \t\t\t30 \t\t\t2\n35 \t84 \t\t9 \t\t\t21 \t\t\t4\n35 \t32 \t\t10 \t\t\t8 \t\t\t4\n35 \t48 \t\t11 \t\t\t24 \t\t\t2\n35 \t140 \t\t12 \t\t\t70 \t\t\t2\n35 \t60 \t\t13 \t\t\t30 \t\t\t2\n35 \t48 \t\t14 \t\t\t12 \t\t\t4\n35 \t24"}︡{"stdout":" \t\t15 \t\t\t12 \t\t\t2\n35 \t84 \t\t16 \t\t\t42 \t\t\t2\n35 \t80 \t\t17 \t\t\t40 \t\t\t2\n35 \t80 \t\t18 \t\t\t40 \t\t\t2\n35 \t84 \t\t19 \t\t\t42 \t\t\t2\n35 \t24 \t\t20 \t\t\t12 \t\t\t2\n35"}︡{"stdout":" \t48 \t\t21 \t\t\t12 \t\t\t4\n35 \t60 \t\t22 \t\t\t30 \t\t\t2\n35 \t140 \t\t23 \t\t\t70 \t\t\t2\n35 \t48 \t\t24 \t\t\t24 \t\t\t2\n35 \t32 \t\t25 \t\t\t8 \t\t\t4\n35 \t84 \t\t26 \t\t\t42 \t\t\t2\n35"}︡{"stdout":" \t60 \t\t27 \t\t\t15 \t\t\t4\n35 \t80 \t\t28 \t\t\t20 \t\t\t4\n35 \t36 \t\t29 \t\t\t6 \t\t\t6\n35 \t56 \t\t30 \t\t\t28 \t\t\t2\n35 \t48 \t\t31 \t\t\t24 \t\t\t2\n35 \t80 \t\t32 \t\t\t40 \t\t\t2\n35 \t140 \t\t33 \t\t\t70 \t\t\t2\n35 \t36 \t\t34 \t\t\t3 \t\t\t12\nNumber of Strong Pseudoprimes: "}︡{"stdout":" 8\nNumber of Pseudoprimes:  10\nNumber of Lucas Group Pseudoprimes:  7\nNumber of Strong Lucas Group Pseudoprimes:  5\n0\n\n\n37\n37 \t36 \t\t1 \t\t\t6 \t\t\t6\n37 \t74 \t\t2 \t\t\t37 \t\t\t2\n37 \t38 \t\t3 \t\t\t38 \t\t\t1\n37 \t36 \t\t4 \t\t\t36 \t\t\t1\n37"}︡{"stdout":" \t36 \t\t5 \t\t\t9 \t\t\t4\n37 \t38 \t\t6 \t\t\t38 \t\t\t1\n37 \t38 \t\t7 \t\t\t19 \t\t\t2\n37 \t38 \t\t8 \t\t\t19 \t\t\t2\n37 \t36 \t\t9 \t\t\t9 \t\t\t4\n37"}︡{"stdout":" \t38 \t\t10 \t\t\t19 \t\t\t2\n37 \t38 \t\t11 \t\t\t38 \t\t\t1\n37 \t38 \t\t12 \t\t\t38 \t\t\t1\n37 \t38 \t\t13 \t\t\t38 \t\t\t1\n37 \t36"}︡{"stdout":" \t\t14 \t\t\t18 \t\t\t2\n37 \t36 \t\t15 \t\t\t12 \t\t\t3\n37 \t36 \t\t16 \t\t\t36 \t\t\t1\n37 \t36 \t\t17 \t\t\t36 \t\t\t1\n37 \t38 \t\t18 \t\t\t38 \t\t\t1\n37 \t38 \t\t19 \t\t\t19 \t\t\t2\n37 \t36 \t\t20 \t\t\t36 \t\t\t1\n37 \t36"}︡{"stdout":" \t\t21 \t\t\t36 \t\t\t1\n37 \t36 \t\t22 \t\t\t12 \t\t\t3\n37 \t36 \t\t23 \t\t\t9 \t\t\t4\n37 \t38 \t\t24 \t\t\t19 \t\t\t2\n37 \t38 \t\t25 \t\t\t19 \t\t\t2\n37 \t38 \t\t26 \t\t\t19 \t\t\t2\n37 \t38 \t\t27 \t\t\t38 \t\t\t1\n37 \t36 \t\t28 \t\t\t18 \t\t\t2\n37"}︡{"stdout":" \t38 \t\t29 \t\t\t38 \t\t\t1\n37 \t38 \t\t30 \t\t\t38 \t\t\t1\n37 \t38 \t\t31 \t\t\t19 \t\t\t2\n37 \t36 \t\t32 \t\t\t18 \t\t\t2\n37 \t36 \t\t33 \t\t\t36 \t\t\t1\n37 \t38 \t\t34 \t\t\t19 \t\t\t2\n37 \t74 \t\t35 \t\t\t74 \t\t\t1\n37"}︡{"stdout":" \t36 \t\t36 \t\t\t3 \t\t\t12\nNumber of Strong Pseudoprimes:  36\nNumber of Pseudoprimes:  36\nNumber of Lucas Group Pseudoprimes:  35\nNumber of Strong Lucas Group Pseudoprimes:  13\n16\n\n\n39\n39 \t72 \t\t1 \t\t\t6 \t\t\t12\n39 \t156 \t\t2 \t\t\t39 \t\t\t4\n39 \t56 \t\t3 \t\t\t28 \t\t\t2\n39 \t72 \t\t4 \t\t\t12 \t\t\t6\n39 \t84 \t\t5 \t\t\t42 \t\t\t2\n39"}︡{"stdout":" \t56 \t\t6 \t\t\t28 \t\t\t2\n39 \t84 \t\t7 \t\t\t42 \t\t\t2\n39 \t84 \t\t8 \t\t\t21 \t\t\t4\n39 \t48 \t\t9 \t\t\t12 \t\t\t4\n39 \t84 \t\t10 \t\t\t42 \t\t\t2\n39"}︡{"stdout":" \t156 \t\t11 \t\t\t78 \t\t\t2\n39 \t48 \t\t12 \t\t\t12 \t\t\t4\n39 \t72 \t\t13 \t\t\t12 \t\t\t6\n39 \t72 \t\t14 \t\t\t6 \t\t\t12\n39 \t104 \t\t15 \t\t\t52 \t\t\t2\n39 \t84 \t\t16 \t\t\t42 \t\t\t2\n39 \t72 \t\t17 \t\t\t12 \t\t\t6\n39"}︡{"stdout":" \t56 \t\t18 \t\t\t28 \t\t\t2\n39 \t84 \t\t19 \t\t\t42 \t\t\t2\n39 \t84 \t\t20 \t\t\t21 \t\t\t4\n39 \t56 \t\t21 \t\t\t28 \t\t\t2\n39 \t72 \t\t22 \t\t\t12 \t\t\t6\n39 \t84 \t\t23 \t\t\t21 \t\t\t4\n39"}︡{"stdout":" \t104 \t\t24 \t\t\t52 \t\t\t2\n39 \t72 \t\t25 \t\t\t6 \t\t\t12\n39 \t72 \t\t26 \t\t\t12 \t\t\t6\n39 \t48 \t\t27 \t\t\t12 \t\t\t4\n39 \t156 \t\t28 \t\t\t78 \t\t\t2\n39 \t84 \t\t29 \t\t\t42 \t\t\t2\n39 \t48 \t\t30 \t\t\t12 \t\t\t4\n39"}︡{"stdout":" \t84 \t\t31 \t\t\t42 \t\t\t2\n39 \t84 \t\t32 \t\t\t42 \t\t\t2\n39 \t56 \t\t33 \t\t\t28 \t\t\t2\n39 \t84 \t\t34 \t\t\t42 \t\t\t2\n39 \t72 \t\t35 \t\t\t12 \t\t\t6\n39 \t56 \t\t36 \t\t\t28 \t\t\t2\n39 \t156 \t\t37 \t\t\t78 \t\t\t2\n39 \t72"}︡{"stdout":" \t\t38 \t\t\t3 \t\t\t24\nNumber of Strong Pseudoprimes:  8\nNumber of Pseudoprimes:  8\nNumber of Lucas Group Pseudoprimes:  5\nNumber of Strong Lucas Group Pseudoprimes:  0\n0\n\n\n41\n41 \t42 \t\t1 \t\t\t6 \t\t\t7\n41 \t82 \t\t2 \t\t\t41 \t\t\t2\n41 \t40 \t\t3 \t\t\t20 \t\t\t2\n41 \t42 \t\t4 \t\t\t14 \t\t\t3\n41 \t40 \t\t5 \t\t\t40 \t\t\t1\n41 \t40"}︡{"stdout":" \t\t6 \t\t\t5 \t\t\t8\n41 \t40 \t\t7 \t\t\t10 \t\t\t4\n41 \t42 \t\t8 \t\t\t21 \t\t\t2\n41 \t40 \t\t9 \t\t\t40 \t\t\t1\n41 \t42 \t\t10 \t\t\t42 \t\t\t1\n41"}︡{"stdout":" \t42 \t\t11 \t\t\t14 \t\t\t3\n41 \t42 \t\t12 \t\t\t42 \t\t\t1\n41 \t40 \t\t13 \t\t\t40 \t\t\t1\n41 \t42 \t\t14 \t\t\t7 \t\t\t6\n41 \t40 \t\t15 \t\t\t40 \t\t\t1\n41 \t42 \t\t16 \t\t\t21"}︡{"stdout":" \t\t\t2\n41 \t40 \t\t17 \t\t\t8 \t\t\t5\n41 \t40 \t\t18 \t\t\t20 \t\t\t2\n41 \t42 \t\t19 \t\t\t21 \t\t\t2\n41 \t42"}︡{"stdout":" \t\t20 \t\t\t42 \t\t\t1\n41 \t42 \t\t21 \t\t\t21 \t\t\t2\n41 \t42 \t\t22 \t\t\t42 \t\t\t1\n41 \t40 \t\t23 \t\t\t20 \t\t\t2\n41 \t40 \t\t24 \t\t\t8 \t\t\t5\n41"}︡{"stdout":" \t42 \t\t25 \t\t\t42 \t\t\t1\n41 \t40 \t\t26 \t\t\t40 \t\t\t1\n41 \t42 \t\t27 \t\t\t14 \t\t\t3\n41 \t40 \t\t28 \t\t\t40 \t\t\t1\n41 \t42 \t\t29 \t\t\t21 \t\t\t2\n41 \t42"}︡{"stdout":" \t\t30 \t\t\t7 \t\t\t6\n41 \t42 \t\t31 \t\t\t21 \t\t\t2\n41 \t40 \t\t32 \t\t\t40 \t\t\t1\n41 \t42 \t\t33 \t\t\t42 \t\t\t1\n41 \t40 \t\t34 \t\t\t5 \t\t\t8\n41 \t40 \t\t35 \t\t\t10 \t\t\t4\n41"}︡{"stdout":" \t40 \t\t36 \t\t\t40 \t\t\t1\n41 \t42 \t\t37 \t\t\t7 \t\t\t6\n41 \t40 \t\t38 \t\t\t20 \t\t\t2\n41 \t82 \t\t39 \t\t\t82 \t\t\t1\n41 \t42 \t\t40 \t\t\t3 \t\t\t14\nNumber of Strong Pseudoprimes:  40\nNumber of Pseudoprimes:  40\nNumber of Lucas Group Pseudoprimes:  39\nNumber of Strong Lucas Group Pseudoprimes:  12\n15\n\n\n43\n43 \t42 \t\t1 \t\t\t6 \t\t\t7\n43 \t86 \t\t2 \t\t\t43 \t\t\t2\n43"}︡{"stdout":" \t44 \t\t3 \t\t\t44 \t\t\t1\n43 \t44 \t\t4 \t\t\t11 \t\t\t4\n43 \t42 \t\t5 \t\t\t42 \t\t\t1\n43 \t44 \t\t6 \t\t\t44 \t\t\t1\n43 \t44 \t\t7 \t\t\t22 \t\t\t2\n43"}︡{"stdout":" \t42 \t\t8 \t\t\t7 \t\t\t6\n43 \t44 \t\t9 \t\t\t11 \t\t\t4\n43 \t42 \t\t10 \t\t\t42 \t\t\t1\n43 \t42 \t\t11 \t\t\t21 \t\t\t2\n43 \t42 \t\t12 \t\t\t21 \t\t\t2\n43 \t42 \t\t13 \t\t\t21 \t\t\t2\n43"}︡{"stdout":" \t44 \t\t14 \t\t\t11 \t\t\t4\n43 \t42 \t\t15 \t\t\t7 \t\t\t6\n43 \t44 \t\t16 \t\t\t44 \t\t\t1\n43 \t44 \t\t17 \t\t\t44 \t\t\t1\n43 \t44 \t\t18 \t\t\t44 \t\t\t1\n43 \t42 \t\t19 \t\t\t7 \t\t\t6\n43"}︡{"stdout":" \t42 \t\t20 \t\t\t42 \t\t\t1\n43 \t44 \t\t21 \t\t\t22 \t\t\t2\n43 \t44 \t\t22 \t\t\t11 \t\t\t4\n43 \t42 \t\t23 \t\t\t21 \t\t\t2\n43 \t42 \t\t24 \t\t\t14 \t\t\t3\n43 \t44 \t\t25 \t\t\t44 \t\t\t1\n43 \t44"}︡{"stdout":" \t\t26 \t\t\t44 \t\t\t1\n43 \t44 \t\t27 \t\t\t44 \t\t\t1\n43 \t42 \t\t28 \t\t\t14 \t\t\t3\n43 \t44 \t\t29 \t\t\t22 \t\t\t2\n43 \t42 \t\t30 \t\t\t42 \t\t\t1\n43"}︡{"stdout":" \t42 \t\t31 \t\t\t42 \t\t\t1\n43 \t42 \t\t32 \t\t\t42 \t\t\t1\n43 \t42 \t\t33 \t\t\t21 \t\t\t2\n43 \t44 \t\t34 \t\t\t22 \t\t\t2\n43 \t42 \t\t35 \t\t\t14 \t\t\t3\n43 \t44 \t\t36 \t\t\t11 \t\t\t4\n43 \t44 \t\t37 \t\t\t44 \t\t\t1\n43"}︡{"stdout":" \t42 \t\t38 \t\t\t21 \t\t\t2\n43 \t44 \t\t39 \t\t\t22 \t\t\t2\n43 \t44 \t\t40 \t\t\t44 \t\t\t1\n43 \t86 \t\t41 \t\t\t86 \t\t\t1\n43 \t42 \t\t42 \t\t\t3 \t\t\t14\nNumber of Strong Pseudoprimes:  42\nNumber of Pseudoprimes:  42\nNumber of Lucas Group Pseudoprimes:  42\nNumber of Strong Lucas Group Pseudoprimes:  14\n17\n\n\n45\n45 \t108"}︡{"stdout":" \t\t1 \t\t\t6 \t\t\t18\n45 \t180 \t\t2 \t\t\t45 \t\t\t4\n45 \t120 \t\t3 \t\t\t60 \t\t\t2\n45 \t108 \t\t4 \t\t\t18 \t\t\t6\n45 \t72 \t\t5 \t\t\t36 \t\t\t2\n45 \t72 \t\t6 \t\t\t12 \t\t\t6\n45"}︡{"stdout":" \t180 \t\t7 \t\t\t90 \t\t\t2\n45 \t180 \t\t8 \t\t\t30 \t\t\t6\n45 \t72 \t\t9 \t\t\t12 \t\t\t6\n45 \t72 \t\t10 \t\t\t12 \t\t\t6\n45"}︡{"stdout":" \t108 \t\t11 \t\t\t18 \t\t\t6\n45 \t120 \t\t12 \t\t\t60 \t\t\t2\n45 \t180 \t\t13 \t\t\t90 \t\t\t2\n45 \t108 \t\t14 \t\t\t9 \t\t\t12\n45 \t48 \t\t15 \t\t\t12 \t\t\t4\n45"}︡{"stdout":" \t108 \t\t16 \t\t\t18 \t\t\t6\n45 \t180 \t\t17 \t\t\t15 \t\t\t12\n45 \t120 \t\t18 \t\t\t20 \t\t\t6\n45 \t108 \t\t19 \t\t\t6 \t\t\t18\n45 \t72 \t\t20 \t\t\t36 \t\t\t2\n45"}︡{"stdout":" \t72 \t\t21 \t\t\t12 \t\t\t6\n45 \t180 \t\t22 \t\t\t90 \t\t\t2\n45 \t180 \t\t23 \t\t\t90 \t\t\t2\n45 \t72 \t\t24 \t\t\t12 \t\t\t6\n45 \t72 \t\t25 \t\t\t36 \t\t\t2\n45 \t108 \t\t26 \t\t\t6 \t\t\t18\n45"}︡{"stdout":" \t120 \t\t27 \t\t\t20 \t\t\t6\n45 \t180 \t\t28 \t\t\t30 \t\t\t6\n45 \t108 \t\t29 \t\t\t9 \t\t\t12\n45 \t48 \t\t30 \t\t\t12 \t\t\t4\n45 \t108 \t\t31 \t\t\t18 \t\t\t6\n45 \t180 \t\t32 \t\t\t45 \t\t\t4\n45"}︡{"stdout":" \t120 \t\t33 \t\t\t60 \t\t\t2\n45 \t108 \t\t34 \t\t\t18 \t\t\t6\n45 \t72 \t\t35 \t\t\t12 \t\t\t6\n45 \t72 \t\t36 \t\t\t12 \t\t\t6\n45 \t180 \t\t37 \t\t\t30 \t\t\t6\n45 \t180 \t\t38 \t\t\t90 \t\t\t2\n45"}︡{"stdout":" \t72 \t\t39 \t\t\t12 \t\t\t6\n45 \t72 \t\t40 \t\t\t36 \t\t\t2\n45 \t108 \t\t41 \t\t\t18 \t\t\t6\n45 \t120 \t\t42 \t\t\t60 \t\t\t2\n45 \t180 \t\t43 \t\t\t90 \t\t\t2\n45 \t108 \t\t44 \t\t\t3 \t\t\t36\nNumber of Strong Pseudoprimes: "}︡{"stdout":" 24\nNumber of Pseudoprimes:  24\nNumber of Lucas Group Pseudoprimes:  6\nNumber of Strong Lucas Group Pseudoprimes:  5\n0\n\n\n47\n47 \t48 \t\t1 \t\t\t6 \t\t\t8\n47 \t94 \t\t2 \t\t\t47 \t\t\t2\n47 \t48 \t\t3 \t\t\t16 \t\t\t3\n47 \t46 \t\t4 \t\t\t23 \t\t\t2\n47 \t46 \t\t5 \t\t\t23 \t\t\t2\n47 \t46"}︡{"stdout":" \t\t6 \t\t\t23 \t\t\t2\n47 \t48 \t\t7 \t\t\t8 \t\t\t6\n47 \t48 \t\t8 \t\t\t48 \t\t\t1\n47 \t48 \t\t9 \t\t\t48 \t\t\t1\n47 \t46 \t\t10 \t\t\t23 \t\t\t2\n47 \t48 \t\t11 \t\t\t48 \t\t\t1\n47"}︡{"stdout":" \t48 \t\t12 \t\t\t12 \t\t\t4\n47 \t46 \t\t13 \t\t\t46 \t\t\t1\n47 \t46 \t\t14 \t\t\t23 \t\t\t2\n47 \t48 \t\t15 \t\t\t24 \t\t\t2\n47 \t46 \t\t16 \t\t\t23 \t\t\t2\n47 \t46 \t\t17 \t\t\t46 \t\t\t1\n47"}︡{"stdout":" \t48 \t\t18 \t\t\t16 \t\t\t3\n47 \t46 \t\t19 \t\t\t23 \t\t\t2\n47 \t48 \t\t20 \t\t\t48 \t\t\t1\n47 \t46 \t\t21 \t\t\t46 \t\t\t1\n47 \t48 \t\t22 \t\t\t24 \t\t\t2\n47 \t46 \t\t23 \t\t\t23 \t\t\t2\n47"}︡{"stdout":" \t46 \t\t24 \t\t\t46 \t\t\t1\n47 \t48 \t\t25 \t\t\t24 \t\t\t2\n47 \t46 \t\t26 \t\t\t23 \t\t\t2\n47 \t48 \t\t27 \t\t\t48 \t\t\t1\n47 \t46 \t\t28 \t\t\t46 \t\t\t1\n47 \t48"}︡{"stdout":" \t\t29 \t\t\t16 \t\t\t3\n47 \t46 \t\t30 \t\t\t23 \t\t\t2\n47 \t46 \t\t31 \t\t\t46 \t\t\t1\n47 \t48 \t\t32 \t\t\t24 \t\t\t2\n47"}︡{"stdout":" \t46 \t\t33 \t\t\t46 \t\t\t1\n47 \t46 \t\t34 \t\t\t23 \t\t\t2\n47 \t48 \t\t35 \t\t\t12 \t\t\t4\n47 \t48 \t\t36 \t\t\t48 \t\t\t1\n47 \t46 \t\t37 \t\t\t46 \t\t\t1\n47"}︡{"stdout":" \t48 \t\t38 \t\t\t48 \t\t\t1\n47 \t48 \t\t39 \t\t\t48 \t\t\t1\n47 \t48 \t\t40 \t\t\t8 \t\t\t6\n47 \t46 \t\t41 \t\t\t46 \t\t\t1\n47 \t46 \t\t42 \t\t\t46 \t\t\t1\n47 \t46 \t\t43 \t\t\t46 \t\t\t1\n47"}︡{"stdout":" \t48 \t\t44 \t\t\t16 \t\t\t3\n47 \t94 \t\t45 \t\t\t94 \t\t\t1\n47 \t48 \t\t46 \t\t\t3 \t\t\t16\nNumber of Strong Pseudoprimes:  46\nNumber of Pseudoprimes:  46\nNumber of Lucas Group Pseudoprimes:  44\nNumber of Strong Lucas Group Pseudoprimes:  14\n20\n\n\n49\n49 \t42 \t\t1 \t\t\t6 \t\t\t7\n49 \t98 \t\t2 \t\t\t49 \t\t\t2\n49"}︡{"stdout":" \t56 \t\t3 \t\t\t56 \t\t\t1\n49 \t56 \t\t4 \t\t\t56 \t\t\t1\n49 \t98 \t\t5 \t\t\t98 \t\t\t1\n49 \t42 \t\t6 \t\t\t21 \t\t\t2\n49 \t56 \t\t7 \t\t\t28 \t\t\t2\n49 \t42 \t\t8 \t\t\t42"}︡{"stdout":" \t\t\t1\n49 \t98 \t\t9 \t\t\t49 \t\t\t2\n49 \t56 \t\t10 \t\t\t8 \t\t\t7\n49 \t56 \t\t11 \t\t\t56 \t\t\t1\n49 \t98 \t\t12 \t\t\t98 \t\t\t1\n49 \t42 \t\t13 \t\t\t21"}︡{"stdout":" \t\t\t2\n49 \t56 \t\t14 \t\t\t28 \t\t\t2\n49 \t42 \t\t15 \t\t\t42 \t\t\t1\n49 \t98 \t\t16 \t\t\t49 \t\t\t2\n49 \t56 \t\t17 \t\t\t56 \t\t\t1\n49 \t56 \t\t18 \t\t\t56 \t\t\t1\n49"}︡{"stdout":" \t98 \t\t19 \t\t\t98 \t\t\t1\n49 \t42 \t\t20 \t\t\t21 \t\t\t2\n49 \t56 \t\t21 \t\t\t28 \t\t\t2\n49 \t42 \t\t22 \t\t\t42 \t\t\t1\n49 \t98 \t\t23 \t\t\t49 \t\t\t2\n49"}︡{"stdout":" \t56 \t\t24 \t\t\t56 \t\t\t1\n49 \t56 \t\t25 \t\t\t56 \t\t\t1\n49 \t98 \t\t26 \t\t\t98 \t\t\t1\n49 \t42 \t\t27 \t\t\t21 \t\t\t2\n49 \t56 \t\t28 \t\t\t28 \t\t\t2\n49"}︡{"stdout":" \t42 \t\t29 \t\t\t42 \t\t\t1\n49 \t98 \t\t30 \t\t\t49 \t\t\t2\n49 \t56 \t\t31 \t\t\t56 \t\t\t1\n49 \t56 \t\t32 \t\t\t56 \t\t\t1\n49 \t98 \t\t33 \t\t\t98 \t\t\t1\n49"}︡{"stdout":" \t42 \t\t34 \t\t\t21 \t\t\t2\n49 \t56 \t\t35 \t\t\t28 \t\t\t2\n49 \t42 \t\t36 \t\t\t42 \t\t\t1\n49 \t98 \t\t37 \t\t\t49 \t\t\t2\n49 \t56 \t\t38 \t\t\t56 \t\t\t1\n49"}︡{"stdout":" \t56 \t\t39 \t\t\t8 \t\t\t7\n49 \t98 \t\t40 \t\t\t98 \t\t\t1\n49 \t42 \t\t41 \t\t\t21 \t\t\t2\n49 \t56 \t\t42 \t\t\t28 \t\t\t2\n49 \t42 \t\t43 \t\t\t42 \t\t\t1\n49 \t98"}︡{"stdout":" \t\t44 \t\t\t49 \t\t\t2\n49 \t56 \t\t45 \t\t\t56 \t\t\t1\n49 \t56 \t\t46 \t\t\t56 \t\t\t1\n49 \t98 \t\t47 \t\t\t98 \t\t\t1\n49 \t42 \t\t48 \t\t\t3 \t\t\t14\nNumber of Strong Pseudoprimes:  18\nNumber of Pseudoprimes:  18\nNumber of Lucas Group Pseudoprimes:  13\nNumber of Strong Lucas Group Pseudoprimes:  7\n25\n\n\n51\n51 \t108 \t\t1 \t\t\t6 \t\t\t18\n51"}︡{"stdout":" \t204 \t\t2 \t\t\t51 \t\t\t4\n51 \t72 \t\t3 \t\t\t36 \t\t\t2\n51 \t108 \t\t4 \t\t\t18 \t\t\t6\n51 \t96 \t\t5 \t\t\t48 \t\t\t2\n51 \t64 \t\t6 \t\t\t8 \t\t\t8\n51"}︡{"stdout":" \t108 \t\t7 \t\t\t18 \t\t\t6\n51 \t96 \t\t8 \t\t\t48 \t\t\t2\n51 \t64 \t\t9 \t\t\t16 \t\t\t4\n51 \t108 \t\t10 \t\t\t18 \t\t\t6\n51 \t96 \t\t11 \t\t\t24 \t\t\t4\n51"}︡{"stdout":" \t64 \t\t12 \t\t\t16 \t\t\t4\n51 \t108 \t\t13 \t\t\t18 \t\t\t6\n51 \t108 \t\t14 \t\t\t9 \t\t\t12\n51 \t136 \t\t15 \t\t\t68 \t\t\t2\n51"}︡{"stdout":" \t108 \t\t16 \t\t\t6 \t\t\t18\n51 \t96 \t\t17 \t\t\t12 \t\t\t8\n51 \t72 \t\t18 \t\t\t12 \t\t\t6\n51 \t204 \t\t19 \t\t\t102 \t\t\t2\n51 \t108 \t\t20 \t\t\t18 \t\t\t6\n51"}︡{"stdout":" \t72 \t\t21 \t\t\t36 \t\t\t2\n51 \t96 \t\t22 \t\t\t48 \t\t\t2\n51 \t96 \t\t23 \t\t\t24 \t\t\t4\n51 \t72 \t\t24 \t\t\t36 \t\t\t2\n51 \t96 \t\t25 \t\t\t48 \t\t\t2\n51"}︡{"stdout":" \t96 \t\t26 \t\t\t48 \t\t\t2\n51 \t72 \t\t27 \t\t\t36 \t\t\t2\n51 \t96 \t\t28 \t\t\t24 \t\t\t4\n51 \t96 \t\t29 \t\t\t48 \t\t\t2\n51 \t72 \t\t30 \t\t\t36 \t\t\t2\n51 \t108"}︡{"stdout":" \t\t31 \t\t\t18 \t\t\t6\n51 \t204 \t\t32 \t\t\t102 \t\t\t2\n51 \t72 \t\t33 \t\t\t12 \t\t\t6\n51 \t96 \t\t34 \t\t\t12 \t\t\t8\n51 \t108 \t\t35 \t\t\t6 \t\t\t18\n51 \t136"}︡{"stdout":" \t\t36 \t\t\t68 \t\t\t2\n51 \t108 \t\t37 \t\t\t18 \t\t\t6\n51 \t108 \t\t38 \t\t\t18 \t\t\t6\n51 \t64 \t\t39 \t\t\t16 \t\t\t4\n51 \t96 \t\t40 \t\t\t24 \t\t\t4\n51"}︡{"stdout":" \t108 \t\t41 \t\t\t9 \t\t\t12\n51 \t64 \t\t42 \t\t\t16 \t\t\t4\n51 \t96 \t\t43 \t\t\t48 \t\t\t2\n51 \t108 \t\t44 \t\t\t18 \t\t\t6\n51 \t64 \t\t45 \t\t\t8 \t\t\t8\n51"}︡{"stdout":" \t96 \t\t46 \t\t\t48 \t\t\t2\n51 \t108 \t\t47 \t\t\t9 \t\t\t12\n51 \t72 \t\t48 \t\t\t36 \t\t\t2\n51 \t204 \t\t49 \t\t\t102 \t\t\t2\n51 \t108 \t\t50 \t\t\t3 \t\t\t36\nNumber of Strong Pseudoprimes:  8\nNumber of Pseudoprimes:  10\nNumber of Lucas Group Pseudoprimes:  6\nNumber of Strong Lucas Group Pseudoprimes:  1\n0\n\n\n53\n53"}︡{"stdout":" \t54 \t\t1 \t\t\t6 \t\t\t9\n53 \t106 \t\t2 \t\t\t53 \t\t\t2\n53 \t54 \t\t3 \t\t\t54 \t\t\t1\n53 \t54 \t\t4 \t\t\t9 \t\t\t6\n53 \t54 \t\t5 \t\t\t27 \t\t\t2\n53"}︡{"stdout":" \t54 \t\t6 \t\t\t54 \t\t\t1\n53 \t54 \t\t7 \t\t\t27 \t\t\t2\n53 \t52 \t\t8 \t\t\t13 \t\t\t4\n53 \t52 \t\t9 \t\t\t13 \t\t\t4\n53 \t52"}︡{"stdout":" \t\t10 \t\t\t52 \t\t\t1\n53 \t52 \t\t11 \t\t\t13 \t\t\t4\n53 \t54 \t\t12 \t\t\t54 \t\t\t1\n53 \t52 \t\t13 \t\t\t13 \t\t\t4\n53 \t54 \t\t14 \t\t\t9 \t\t\t6\n53"}︡{"stdout":" \t52 \t\t15 \t\t\t26 \t\t\t2\n53 \t52 \t\t16 \t\t\t52 \t\t\t1\n53 \t54 \t\t17 \t\t\t54 \t\t\t1\n53 \t54 \t\t18 \t\t\t18 \t\t\t3\n53 \t54 \t\t19 \t\t\t54 \t\t\t1\n53"}︡{"stdout":" \t52 \t\t20 \t\t\t52 \t\t\t1\n53 \t52 \t\t21 \t\t\t52 \t\t\t1\n53 \t54 \t\t22 \t\t\t27 \t\t\t2\n53 \t54 \t\t23 \t\t\t27 \t\t\t2\n53 \t52 \t\t24 \t\t\t52 \t\t\t1\n53"}︡{"stdout":" \t52 \t\t25 \t\t\t52 \t\t\t1\n53 \t52 \t\t26 \t\t\t13 \t\t\t4\n53 \t52 \t\t27 \t\t\t26 \t\t\t2\n53 \t52 \t\t28 \t\t\t52 \t\t\t1\n53 \t52 \t\t29 \t\t\t52 \t\t\t1\n53"}︡{"stdout":" \t54 \t\t30 \t\t\t54 \t\t\t1\n53 \t54 \t\t31 \t\t\t54 \t\t\t1\n53 \t52 \t\t32 \t\t\t52 \t\t\t1\n53 \t52 \t\t33 \t\t\t52 \t\t\t1\n53"}︡{"stdout":" \t54 \t\t34 \t\t\t27 \t\t\t2\n53 \t54 \t\t35 \t\t\t9 \t\t\t6\n53 \t54 \t\t36 \t\t\t27 \t\t\t2\n53 \t52 \t\t37 \t\t\t52 \t\t\t1\n53 \t52 \t\t38 \t\t\t13 \t\t\t4\n53"}︡{"stdout":" \t54 \t\t39 \t\t\t18 \t\t\t3\n53 \t52 \t\t40 \t\t\t26 \t\t\t2\n53 \t54 \t\t41 \t\t\t27 \t\t\t2\n53 \t52 \t\t42 \t\t\t26 \t\t\t2\n53 \t52 \t\t43 \t\t\t52 \t\t\t1\n53"}︡{"stdout":" \t52 \t\t44 \t\t\t26 \t\t\t2\n53 \t52 \t\t45 \t\t\t26 \t\t\t2\n53 \t54 \t\t46 \t\t\t54 \t\t\t1\n53 \t54 \t\t47 \t\t\t27 \t\t\t2\n53 \t54"}︡{"stdout":" \t\t48 \t\t\t54 \t\t\t1\n53 \t54 \t\t49 \t\t\t18 \t\t\t3\n53 \t54 \t\t50 \t\t\t27 \t\t\t2\n53 \t106 \t\t51 \t\t\t106 \t\t\t1\n53 \t54 \t\t52 \t\t\t3 \t\t\t18\nNumber of Strong Pseudoprimes: "}︡{"stdout":" 52\nNumber of Pseudoprimes:  52\nNumber of Lucas Group Pseudoprimes:  50\nNumber of Strong Lucas Group Pseudoprimes:  17\n22\n\n\n55\n55 \t72 \t\t1 \t\t\t6 \t\t\t12\n55 \t220 \t\t2 \t\t\t55 \t\t\t4\n55 \t100 \t\t3 \t\t\t10 \t\t\t10\n55 \t60 \t\t4 \t\t\t30 \t\t\t2\n55"}︡{"stdout":" \t48 \t\t5 \t\t\t12 \t\t\t4\n55 \t72 \t\t6 \t\t\t12 \t\t\t6\n55 \t100 \t\t7 \t\t\t5 \t\t\t20\n55 \t100 \t\t8 \t\t\t10 \t\t\t10\n55 \t132"}︡{"stdout":" \t\t9 \t\t\t66 \t\t\t2\n55 \t48 \t\t10 \t\t\t12 \t\t\t4\n55 \t72 \t\t11 \t\t\t12 \t\t\t6\n55 \t120 \t\t12 \t\t\t30 \t\t\t4\n55"}︡{"stdout":" \t220 \t\t13 \t\t\t110 \t\t\t2\n55 \t60 \t\t14 \t\t\t15 \t\t\t4\n55 \t40 \t\t15 \t\t\t20 \t\t\t2\n55 \t72 \t\t16 \t\t\t12 \t\t\t6\n55 \t120"}︡{"stdout":" \t\t17 \t\t\t60 \t\t\t2\n55 \t100 \t\t18 \t\t\t10 \t\t\t10\n55 \t60 \t\t19 \t\t\t30 \t\t\t2\n55 \t88 \t\t20 \t\t\t44 \t\t\t2\n55 \t72 \t\t21 \t\t\t6 \t\t\t12\n55"}︡{"stdout":" \t120 \t\t22 \t\t\t20 \t\t\t6\n55 \t120 \t\t23 \t\t\t30 \t\t\t4\n55 \t132 \t\t24 \t\t\t33 \t\t\t4\n55 \t40 \t\t25 \t\t\t20 \t\t\t2\n55"}︡{"stdout":" \t60 \t\t26 \t\t\t30 \t\t\t2\n55 \t120 \t\t27 \t\t\t60 \t\t\t2\n55 \t120 \t\t28 \t\t\t60 \t\t\t2\n55 \t60 \t\t29 \t\t\t15 \t\t\t4\n55"}︡{"stdout":" \t40 \t\t30 \t\t\t20 \t\t\t2\n55 \t132 \t\t31 \t\t\t66 \t\t\t2\n55 \t120 \t\t32 \t\t\t15 \t\t\t8\n55 \t120 \t\t33 \t\t\t20 \t\t\t6\n55"}︡{"stdout":" \t72 \t\t34 \t\t\t6 \t\t\t12\n55 \t88 \t\t35 \t\t\t44 \t\t\t2\n55 \t60 \t\t36 \t\t\t30 \t\t\t2\n55 \t100 \t\t37 \t\t\t10 \t\t\t10\n55"}︡{"stdout":" \t120 \t\t38 \t\t\t60 \t\t\t2\n55 \t72 \t\t39 \t\t\t12 \t\t\t6\n55 \t40 \t\t40 \t\t\t20 \t\t\t2\n55 \t60 \t\t41 \t\t\t30 \t\t\t2\n55"}︡{"stdout":" \t220 \t\t42 \t\t\t110 \t\t\t2\n55 \t120 \t\t43 \t\t\t30 \t\t\t4\n55 \t72 \t\t44 \t\t\t12 \t\t\t6\n55 \t48 \t\t45 \t\t\t12 \t\t\t4\n55"}︡{"stdout":" \t132 \t\t46 \t\t\t66 \t\t\t2\n55 \t100 \t\t47 \t\t\t5 \t\t\t20\n55 \t100 \t\t48 \t\t\t10 \t\t\t10\n55 \t72 \t\t49 \t\t\t12 \t\t\t6\n55"}︡{"stdout":" \t48 \t\t50 \t\t\t12 \t\t\t4\n55 \t60 \t\t51 \t\t\t30 \t\t\t2\n55 \t100 \t\t52 \t\t\t10 \t\t\t10\n55 \t220 \t\t53 \t\t\t110 \t\t\t2\n55"}︡{"stdout":" \t72 \t\t54 \t\t\t3 \t\t\t24\nNumber of Strong Pseudoprimes:  16\nNumber of Pseudoprimes:  22\nNumber of Lucas Group Pseudoprimes:  16\nNumber of Strong Lucas Group Pseudoprimes:  6\n0\n\n\n57\n57 \t108 \t\t1 \t\t\t6 \t\t\t18\n57 \t228 \t\t2 \t\t\t57 \t\t\t4\n57 \t72 \t\t3 \t\t\t36 \t\t\t2\n57"}︡{"stdout":" \t120 \t\t4 \t\t\t30 \t\t\t4\n57 \t120 \t\t5 \t\t\t30 \t\t\t4\n57 \t80 \t\t6 \t\t\t20 \t\t\t4\n57 \t108 \t\t7 \t\t\t18 \t\t\t6\n57 \t120 \t\t8 \t\t\t60 \t\t\t2\n57"}︡{"stdout":" \t72 \t\t9 \t\t\t36 \t\t\t2\n57 \t108 \t\t10 \t\t\t18 \t\t\t6\n57 \t120 \t\t11 \t\t\t60 \t\t\t2\n57 \t72 \t\t12 \t\t\t36 \t\t\t2\n57"}︡{"stdout":" \t120 \t\t13 \t\t\t60 \t\t\t2\n57 \t120 \t\t14 \t\t\t15 \t\t\t8\n57 \t80 \t\t15 \t\t\t20 \t\t\t4\n57 \t108 \t\t16 \t\t\t18 \t\t\t6\n57"}︡{"stdout":" \t228 \t\t17 \t\t\t114 \t\t\t2\n57 \t72 \t\t18 \t\t\t12 \t\t\t6\n57 \t120 \t\t19 \t\t\t12 \t\t\t10\n57 \t108 \t\t20 \t\t\t6 \t\t\t18\n57"}︡{"stdout":" \t152 \t\t21 \t\t\t76 \t\t\t2\n57 \t108 \t\t22 \t\t\t18 \t\t\t6\n57 \t120 \t\t23 \t\t\t15 \t\t\t8\n57 \t80 \t\t24 \t\t\t20 \t\t\t4\n57"}︡{"stdout":" \t120 \t\t25 \t\t\t60 \t\t\t2\n57 \t108 \t\t26 \t\t\t9 \t\t\t12\n57 \t80 \t\t27 \t\t\t20 \t\t\t4\n57 \t108 \t\t28 \t\t\t18 \t\t\t6\n57"}︡{"stdout":" \t108 \t\t29 \t\t\t18 \t\t\t6\n57 \t80 \t\t30 \t\t\t20 \t\t\t4\n57 \t108 \t\t31 \t\t\t18 \t\t\t6\n57 \t120"}︡{"stdout":" \t\t32 \t\t\t60 \t\t\t2\n57 \t80 \t\t33 \t\t\t20 \t\t\t4\n57 \t120 \t\t34 \t\t\t30 \t\t\t4\n57 \t108 \t\t35 \t\t\t18 \t\t\t6\n57 \t152"}︡{"stdout":" \t\t36 \t\t\t76 \t\t\t2\n57 \t108 \t\t37 \t\t\t6 \t\t\t18\n57 \t120 \t\t38 \t\t\t12 \t\t\t10\n57"}︡{"stdout":" \t72 \t\t39 \t\t\t12 \t\t\t6\n57 \t228 \t\t40 \t\t\t114 \t\t\t2\n57 \t108 \t\t41 \t\t\t9 \t\t\t12\n57"}︡{"stdout":" \t80 \t\t42 \t\t\t20 \t\t\t4\n57 \t120 \t\t43 \t\t\t30 \t\t\t4\n57 \t120 \t\t44 \t\t\t60 \t\t\t2\n57"}︡{"stdout":" \t72 \t\t45 \t\t\t36 \t\t\t2\n57 \t120 \t\t46 \t\t\t60 \t\t\t2\n57 \t108 \t\t47 \t\t\t9 \t\t\t12\n57"}︡{"stdout":" \t72 \t\t48 \t\t\t36 \t\t\t2\n57 \t120 \t\t49 \t\t\t60 \t\t\t2\n57 \t108 \t\t50 \t\t\t18 \t\t\t6\n57"}︡{"stdout":" \t80 \t\t51 \t\t\t20 \t\t\t4\n57 \t120 \t\t52 \t\t\t30 \t\t\t4\n57 \t120 \t\t53 \t\t\t30 \t\t\t4\n57"}︡{"stdout":" \t72 \t\t54 \t\t\t36 \t\t\t2\n57 \t228 \t\t55 \t\t\t114 \t\t\t2\n57 \t108 \t\t56 \t\t\t3 \t\t\t36\nNumber of Strong Pseudoprimes: "}︡{"stdout":" 8\nNumber of Pseudoprimes:  8\nNumber of Lucas Group Pseudoprimes:  7\nNumber of Strong Lucas Group Pseudoprimes:  5\n0\n\n\n59\n59 \t60 \t\t1 \t\t\t6 \t\t\t10\n59 \t118 \t\t2 \t\t\t59 \t\t\t2\n59"}︡{"stdout":" \t58 \t\t3 \t\t\t29 \t\t\t2\n59 \t58 \t\t4 \t\t\t58 \t\t\t1\n59"}︡{"stdout":" \t58 \t\t5 \t\t\t29 \t\t\t2\n59 \t60 \t\t6 \t\t\t20 \t\t\t3\n59"}︡{"stdout":" \t58 \t\t7 \t\t\t29 \t\t\t2\n59 \t58 \t\t8 \t\t\t58 \t\t\t1\n59"}︡{"stdout":" \t60 \t\t9 \t\t\t60 \t\t\t1\n59 \t60 \t\t10 \t\t\t30 \t\t\t2\n59 \t60 "}︡{"stdout":"\t\t11 \t\t\t12 \t\t\t5\n59 \t58 \t\t12 \t\t\t58 \t\t\t1\n59 \t60 \t\t13 \t\t\t30 \t\t\t2\n59 \t58"}︡{"stdout":" \t\t14 \t\t\t29 \t\t\t2\n59 \t60 \t\t15 \t\t\t30 \t\t\t2\n59 \t58"}︡{"stdout":" \t\t16 \t\t\t58 \t\t\t1\n59 \t58 \t\t17 \t\t\t29 \t\t\t2\n59 \t58 \t\t18 \t\t\t29 \t\t\t2\n59 \t58"}︡{"stdout":" \t\t19 \t\t\t29 \t\t\t2\n59 \t60 \t\t20 \t\t\t30 \t\t\t2\n59 \t60 \t\t21 \t\t\t20 \t\t\t3\n59 \t60 \t\t22 \t\t\t60 \t\t\t1\n59"}︡{"stdout":" \t58 \t\t23 \t\t\t29 \t\t\t2\n59 \t58 \t\t24 \t\t\t29 \t\t\t2\n59 \t60 \t\t25 \t\t\t5 \t\t\t12\n59"}︡{"stdout":" \t60 \t\t26 \t\t\t10 \t\t\t6\n59 \t58 \t\t27 \t\t\t29 \t\t\t2\n59"}︡{"stdout":" \t60 \t\t28 \t\t\t60 \t\t\t1\n59 \t60 \t\t29 \t\t\t60 \t\t\t1\n59"}︡{"stdout":" \t60 \t\t30 \t\t\t60 \t\t\t1\n59 \t60"}︡{"stdout":" \t\t31 \t\t\t60 \t\t\t1\n59 \t58 \t\t32 \t\t\t58 \t\t\t1\n59"}︡{"stdout":" \t60 \t\t33 \t\t\t5 \t\t\t12\n59 \t60 \t\t34 \t\t\t10 \t\t\t6\n59 \t58 \t\t35 \t\t\t58 \t\t\t1\n59"}︡{"stdout":" \t58 \t\t36 \t\t\t58 \t\t\t1\n59 \t60 \t\t37 \t\t\t60 \t\t\t1\n59 \t60 \t\t38 \t\t\t20 \t\t\t3\n59"}︡{"stdout":" \t60 \t\t39 \t\t\t15 \t\t\t4\n59 \t58 \t\t40 \t\t\t58 \t\t\t1\n59 \t58 \t\t41 \t\t\t58 \t\t\t1\n59 \t58"}︡{"stdout":" \t\t42 \t\t\t58 \t\t\t1\n59 \t58 \t\t43 \t\t\t29 \t\t\t2\n59 \t60 \t\t44 \t\t\t15 \t\t\t4\n59"}︡{"stdout":" \t58 \t\t45 \t\t\t58 \t\t\t1\n59 \t60 \t\t46 \t\t\t15 \t\t\t4\n59 \t58 \t\t47 \t\t\t29 \t\t\t2\n59"}︡{"stdout":" \t60 \t\t48 \t\t\t12 \t\t\t5\n59 \t60 \t\t49 \t\t\t15 \t\t\t4\n59"}︡{"stdout":" \t60 \t\t50 \t\t\t60 \t\t\t1\n59 \t58 \t\t51 \t\t\t29 \t\t\t2\n59 \t58 \t\t52 \t\t\t58 \t\t\t1\n"}︡{"stdout":"59 \t60 \t\t53 \t\t\t20 \t\t\t3\n59"}︡{"stdout":" \t58 \t\t54 \t\t\t58 \t\t\t1\n59 \t58"}︡{"stdout":" \t\t55 \t\t\t29 \t\t\t2\n59 \t58 \t\t56 \t\t\t58 \t\t\t1\n59 \t118"}︡{"stdout":" \t\t57 \t\t\t118 \t\t\t1\n59 \t60 \t\t58 \t\t\t3 \t\t\t20\nNumber of Strong Pseudoprimes:  58\nNumber of Pseudoprimes:  58\nNumber of Lucas Group Pseudoprimes:  57\nNumber of Strong Lucas Group Pseudoprimes:  20\n23\n\n\n61\n61 \t60 \t\t1 \t\t\t6 \t\t\t10\n61"}︡{"stdout":" \t122 \t\t2 \t\t\t61 \t\t\t2\n61 \t60 \t\t3 \t\t\t30 \t\t\t2\n61"}︡{"stdout":" \t60 \t\t4 \t\t\t60 \t\t\t1\n61 \t62 \t\t5 \t\t\t62 \t\t\t1\n61"}︡{"stdout":" \t62 \t\t6 \t\t\t62 \t\t\t1\n61 \t60 \t\t7 \t\t\t15 \t\t\t4\n61"}︡{"stdout":" \t60 \t\t8 \t\t\t12 \t\t\t5\n61 \t60 \t\t9 \t\t\t20 \t\t\t3\n61"}︡{"stdout":" \t62 \t\t10 \t\t\t31 \t\t\t2\n61 \t60 \t\t11 \t\t\t15 \t\t\t4\n61 \t62"}︡{"stdout":" \t\t12 \t\t\t31 \t\t\t2\n61 \t62 \t\t13 \t\t\t31 \t\t\t2\n61"}︡{"stdout":" \t60 \t\t14 \t\t\t30 \t\t\t2\n61 \t62 \t\t15 \t\t\t62 \t\t\t1\n61 \t62 \t\t16 \t\t\t62 \t\t\t1\n61"}︡{"stdout":" \t60 \t\t17 \t\t\t5 \t\t\t12\n61 \t60 \t\t18 \t\t\t10 \t\t\t6\n61 \t60"}︡{"stdout":" \t\t19 \t\t\t60 \t\t\t1\n61 \t62 \t\t20 \t\t\t31 \t\t\t2\n61 \t62 \t\t21 \t\t\t62 \t\t\t1\n61"}︡{"stdout":" \t62 \t\t22 \t\t\t62 \t\t\t1\n61 \t62 \t\t23 \t\t\t31 \t\t\t2\n61 \t62 \t\t24 \t\t\t62 \t\t\t1\n61"}︡{"stdout":" \t62 \t\t25 \t\t\t31 \t\t\t2\n61 \t60 \t\t26 \t\t\t60 \t\t\t1\n61 \t62 \t\t27 \t\t\t62 \t\t\t1\n61"}︡{"stdout":" \t60 \t\t28 \t\t\t60 \t\t\t1\n61 \t62 \t\t29 \t\t\t62 \t\t\t1\n61"}︡{"stdout":" \t60 \t\t30 \t\t\t20 \t\t\t3\n61 \t60 \t\t31 \t\t\t20 \t\t\t3\n61"}︡{"stdout":" \t62 \t\t32 \t\t\t31 \t\t\t2\n61 \t60 \t\t33 \t\t\t60 \t\t\t1\n61"}︡{"stdout":" \t62 \t\t34 \t\t\t31 \t\t\t2\n61 \t60 \t\t35 \t\t\t60 \t\t\t1\n61"}︡{"stdout":" \t62 \t\t36 \t\t\t62 \t\t\t1\n61 \t62 \t\t37 \t\t\t31 \t\t\t2\n61"}︡{"stdout":" \t62 \t\t38 \t\t\t62 \t\t\t1\n61 \t62"}︡{"stdout":" \t\t39 \t\t\t31 \t\t\t2\n61 \t62 \t\t40 \t\t\t31 \t\t\t2\n61"}︡{"stdout":" \t62 \t\t41 \t\t\t62 \t\t\t1\n61 \t60 \t\t42 \t\t\t60 \t\t\t1\n61"}︡{"stdout":" \t60 \t\t43 \t\t\t5 \t\t\t12\n61 \t60 \t\t44 \t\t\t10 \t\t\t6\n61 \t62 \t\t45 \t\t\t31 \t\t\t2\n61"}︡{"stdout":" \t62 \t\t46 \t\t\t31 \t\t\t2\n61 \t60 \t\t47 \t\t\t15 \t\t\t4\n61"}︡{"stdout":" \t62 \t\t48 \t\t\t62 \t\t\t1\n61 \t62 \t\t49 \t\t\t62 \t\t\t1\n61"}︡{"stdout":" \t60 \t\t50 \t\t\t30 \t\t\t2\n61 \t62 \t\t51 \t\t\t62 \t\t\t1\n61 \t60 \t\t52 \t\t\t20 \t\t\t3\n61 \t60"}︡{"stdout":" \t\t53 \t\t\t12 \t\t\t5\n61 \t60 \t\t54 \t\t\t30 \t\t\t2\n61 \t62 \t\t55 \t\t\t31 \t\t\t2\n61"}︡{"stdout":" \t62 \t\t56 \t\t\t31 \t\t\t2\n61 \t60 \t\t57 \t\t\t60 \t\t\t1\n61 \t60 \t\t58 \t\t\t15 \t\t\t4\n61"}︡{"stdout":" \t122 \t\t59 \t\t\t122 \t\t\t1\n61 \t60 \t\t60 \t\t\t3 \t\t\t20\nNumber of Strong Pseudoprimes:  60\nNumber of Pseudoprimes:  60\nNumber of Lucas Group Pseudoprimes:  58\nNumber of Strong Lucas Group Pseudoprimes:  24\n24\n\n\n63\n63"}︡{"stdout":" \t108 \t\t1 \t\t\t6 \t\t\t18\n63 \t252 \t\t2 \t\t\t63 \t\t\t4\n63"}︡{"stdout":" \t96 \t\t3 \t\t\t24 \t\t\t4\n63 \t144 \t\t4 \t\t\t72 \t\t\t2\n63 \t252"}︡{"stdout":" \t\t5 \t\t\t126 \t\t\t2\n63 \t72 \t\t6 \t\t\t12 \t\t\t6\n63"}︡{"stdout":" \t144 \t\t7 \t\t\t36 \t\t\t4\n63 \t108 \t\t8 \t\t\t6 \t\t\t18\n63"}︡{"stdout":" \t168 \t\t9 \t\t\t28 \t\t\t6\n63 \t144 \t\t10 \t\t\t24 \t\t\t6\n63 \t144"}︡{"stdout":" \t\t11 \t\t\t72 \t\t\t2\n63 \t168 \t\t12 \t\t\t84 \t\t\t2\n63 \t108 \t\t13 \t\t\t18 \t\t\t6\n63"}︡{"stdout":" \t144 \t\t14 \t\t\t36 \t\t\t4\n63 \t72 \t\t15 \t\t\t12 \t\t\t6\n63 \t252 \t\t16 \t\t\t126 \t\t\t2\n63"}︡{"stdout":" \t144 \t\t17 \t\t\t24 \t\t\t6\n63 \t96 \t\t18 \t\t\t8 \t\t\t12\n63 \t252 \t\t19 \t\t\t42 \t\t\t6\n63"}︡{"stdout":" \t108 \t\t20 \t\t\t9 \t\t\t12\n63 \t96 \t\t21 \t\t\t12 \t\t\t8\n63 \t108 \t\t22 \t\t\t18 \t\t\t6\n63"}︡{"stdout":" \t252 \t\t23 \t\t\t63 \t\t\t4\n63 \t96 \t\t24 \t\t\t24 \t\t\t4\n63 \t144 \t\t25 \t\t\t72 \t\t\t2\n63"}︡{"stdout":" \t252 \t\t26 \t\t\t42 \t\t\t6\n63 \t72 \t\t27 \t\t\t12 \t\t\t6\n63 \t144 \t\t28 \t\t\t12 \t\t\t12\n63"}︡{"stdout":" \t108 \t\t29 \t\t\t18 \t\t\t6\n63 \t168 \t\t30 \t\t\t84 \t\t\t2\n63 \t144 \t\t31 \t\t\t72 \t\t\t2\n63"}︡{"stdout":" \t144 \t\t32 \t\t\t72 \t\t\t2\n63 \t168 \t\t33 \t\t\t84 \t\t\t2\n63 \t108 \t\t34 \t\t\t18 \t\t\t6\n63"}︡{"stdout":" \t144 \t\t35 \t\t\t12 \t\t\t12\n63 \t72 \t\t36 \t\t\t12 \t\t\t6\n63 \t252 \t\t37 \t\t\t42 \t\t\t6\n63"}︡{"stdout":" \t144 \t\t38 \t\t\t72 \t\t\t2\n63 \t96 \t\t39 \t\t\t24 \t\t\t4\n63"}︡{"stdout":" \t252 \t\t40 \t\t\t126 \t\t\t2\n63 \t108 \t\t41 \t\t\t9 \t\t\t12\n63"}︡{"stdout":" \t96 \t\t42 \t\t\t12 \t\t\t8\n63 \t108 \t\t43 \t\t\t18 \t\t\t6\n63 \t252 \t\t44 \t\t\t21 \t\t\t12\n63"}︡{"stdout":" \t96 \t\t45 \t\t\t8 \t\t\t12\n63 \t144 \t\t46 \t\t\t24 \t\t\t6\n63 \t252 \t\t47 \t\t\t126 \t\t\t2\n63"}︡{"stdout":" \t72 \t\t48 \t\t\t12 \t\t\t6\n63 \t144 \t\t49 \t\t\t36 \t\t\t4\n63 \t108 \t\t50 \t\t\t18 \t\t\t6\n63"}︡{"stdout":" \t168 \t\t51 \t\t\t84 \t\t\t2\n63 \t144 \t\t52 \t\t\t72 \t\t\t2\n63 \t144 \t\t53 \t\t\t24 \t\t\t6\n63"}︡{"stdout":" \t168 \t\t54 \t\t\t28 \t\t\t6\n63 \t108 \t\t55 \t\t\t6 \t\t\t18\n63"}︡{"stdout":" \t144 \t\t56 \t\t\t36 \t\t\t4\n63 \t72 \t\t57 \t\t\t12 \t\t\t6\n63"}︡{"stdout":" \t252 \t\t58 \t\t\t126 \t\t\t2\n63 \t144 \t\t59 \t\t\t72 \t\t\t2\n63"}︡{"stdout":" \t96 \t\t60 \t\t\t24 \t\t\t4\n63 \t252 \t\t61 \t\t\t126 \t\t\t2\n63"}︡{"stdout":" \t108 \t\t62 \t\t\t3 \t\t\t36\nNumber of Strong Pseudoprimes:  24\nNumber of Pseudoprimes:  26\nNumber of Lucas Group Pseudoprimes:  13\nNumber of Strong Lucas Group Pseudoprimes:  6\n0\n\n\n65\n65 \t72 \t\t1 \t\t\t6 \t\t\t12\n65"}︡{"stdout":" \t260 \t\t2 \t\t\t65 \t\t\t4\n65 \t140 \t\t3 \t\t\t70 \t\t\t2\n65 \t72 \t\t4 \t\t\t12 \t\t\t6\n65"}︡{"stdout":" \t56 \t\t5 \t\t\t28 \t\t\t2\n65 \t84 \t\t6 \t\t\t42 \t\t\t2\n65 \t140 \t\t7 \t\t\t35 \t\t\t4\n65"}︡{"stdout":" \t140 \t\t8 \t\t\t70 \t\t\t2\n65 \t72 \t\t9 \t\t\t12 \t\t\t6\n65"}︡{"stdout":" \t56 \t\t10 \t\t\t28 \t\t\t2\n65 \t156 \t\t11 \t\t\t78 \t\t\t2\n65 \t120 \t\t12 \t\t\t15 \t\t\t8\n65"}︡{"stdout":" \t120 \t\t13 \t\t\t20 \t\t\t6\n65 \t72 \t\t14 \t\t\t6 \t\t\t12\n65 \t104 \t\t15 \t\t\t52 \t\t\t2\n65"}︡{"stdout":" \t84 \t\t16 \t\t\t42 \t\t\t2\n65 \t120 \t\t17 \t\t\t60 \t\t\t2\n65 \t140 \t\t18 \t\t\t70 \t\t\t2\n65"}︡{"stdout":" \t84 \t\t19 \t\t\t42 \t\t\t2\n65 \t56 \t\t20 \t\t\t28 \t\t\t2\n65 \t84 \t\t21 \t\t\t42 \t\t\t2\n65"}︡{"stdout":" \t120 \t\t22 \t\t\t60 \t\t\t2\n65 \t140 \t\t23 \t\t\t70 \t\t\t2\n65"}︡{"stdout":" \t156 \t\t24 \t\t\t78 \t\t\t2\n65 \t48 \t\t25 \t\t\t12 \t\t\t4\n65"}︡{"stdout":" \t72 \t\t26 \t\t\t12 \t\t\t6\n65 \t120 \t\t27 \t\t\t30 \t\t\t4\n65"}︡{"stdout":" \t260 \t\t28 \t\t\t130 \t\t\t2\n65 \t84 \t\t29 \t\t\t42 \t\t\t2\n65"}︡{"stdout":" \t48 \t\t30 \t\t\t12 \t\t\t4\n65 \t84 \t\t31 \t\t\t42 \t\t\t2\n65 \t140 \t\t32 \t\t\t70 \t\t\t2\n65"}︡{"stdout":" \t140 \t\t33 \t\t\t70 \t\t\t2\n65 \t84 \t\t34 \t\t\t21 \t\t\t4\n65"}︡{"stdout":" \t48 \t\t35 \t\t\t12 \t\t\t4\n65 \t84 \t\t36 \t\t\t42 \t\t\t2\n65"}︡{"stdout":" \t260 \t\t37 \t\t\t130 \t\t\t2\n65 \t120 \t\t38 \t\t\t30 \t\t\t4\n65"}︡{"stdout":" \t72 \t\t39 \t\t\t12 \t\t\t6\n65"}︡{"stdout":" \t48 \t\t40 \t\t\t12 \t\t\t4\n65 \t156 \t\t41 \t\t\t78 \t\t\t2\n65"}︡{"stdout":" \t140 \t\t42 \t\t\t70 \t\t\t2\n65 \t120 \t\t43 \t\t\t60 \t\t\t2\n65"}︡{"stdout":" \t84 \t\t44 \t\t\t42 \t\t\t2\n65 \t56 \t\t45 \t\t\t28 \t\t\t2\n65"}︡{"stdout":" \t84 \t\t46 \t\t\t42 \t\t\t2\n65 \t140 \t\t47 \t\t\t35 \t\t\t4\n65"}︡{"stdout":" \t120 \t\t48 \t\t\t60 \t\t\t2\n65 \t84 \t\t49 \t\t\t21 \t\t\t4\n65"}︡{"stdout":" \t104 \t\t50 \t\t\t52 \t\t\t2\n65 \t72 \t\t51 \t\t\t6 \t\t\t12\n65"}︡{"stdout":" \t120 \t\t52 \t\t\t20 \t\t\t6\n65 \t120 \t\t53 \t\t\t30 \t\t\t4\n65"}︡{"stdout":" \t156 \t\t54 \t\t\t39 \t\t\t4\n65 \t56 \t\t55 \t\t\t28 \t\t\t2\n65 \t72 \t\t56 \t\t\t12 \t\t\t6\n65"}︡{"stdout":" \t140 \t\t57 \t\t\t70 \t\t\t2\n65 \t140 \t\t58 \t\t\t70 \t\t\t2\n65"}︡{"stdout":" \t84 \t\t59 \t\t\t21 \t\t\t4\n65 \t56 \t\t60 \t\t\t28 \t\t\t2\n65 \t72"}︡{"stdout":" \t\t61 \t\t\t12 \t\t\t6\n65 \t140 \t\t62 \t\t\t35 \t\t\t4\n65 \t260 \t\t63 \t\t\t130 \t\t\t2\n65"}︡{"stdout":" \t72 \t\t64 \t\t\t3 \t\t\t24\nNumber of Strong Pseudoprimes:  8\nNumber of Pseudoprimes:  14\nNumber of Lucas Group Pseudoprimes:  10\nNumber of Strong Lucas Group Pseudoprimes:  4\n0\n\n\n67\n67 \t66 \t\t1 \t\t\t6 \t\t\t11\n67"}︡{"stdout":" \t134 \t\t2 \t\t\t67 \t\t\t2\n67 \t68 \t\t3 \t\t\t68 \t\t\t1\n67"}︡{"stdout":" \t68 \t\t4 \t\t\t34 \t\t\t2\n67 \t66 \t\t5 \t\t\t66 \t\t\t1\n67"}︡{"stdout":" \t68 \t\t6 \t\t\t68 \t\t\t1\n67 \t68 \t\t7 \t\t\t34 \t\t\t2\n67"}︡{"stdout":" \t66 \t\t8 \t\t\t33 \t\t\t2\n67 \t66"}︡{"stdout":" \t\t9 \t\t\t66 \t\t\t1\n67 \t66 \t\t10 \t\t\t66 \t\t\t1\n67"}︡{"stdout":" \t68 \t\t11 \t\t\t68 \t\t\t1\n67 \t66 \t\t12 \t\t\t33 \t\t\t2\n67 \t68 \t\t13 \t\t\t17 \t\t\t4\n67"}︡{"stdout":" \t68 \t\t14 \t\t\t17 \t\t\t4\n67 \t68 \t\t15 \t\t\t17 \t\t\t4\n67 \t68 \t\t16 \t\t\t68 \t\t\t1\n67"}︡{"stdout":" \t66 \t\t17 \t\t\t11 \t\t\t6\n67 \t68 \t\t18 \t\t\t68 \t\t\t1\n67 \t66 \t\t19 \t\t\t11 \t\t\t6\n67"}︡{"stdout":" \t68 \t\t20 \t\t\t34 \t\t\t2\n67 \t66 \t\t21 \t\t\t33 \t\t\t2\n67 \t68 \t\t22 \t\t\t17 \t\t\t4\n67"}︡{"stdout":" \t66 \t\t23 \t\t\t33 \t\t\t2\n67 \t66 \t\t24 \t\t\t11 \t\t\t6\n67"}︡{"stdout":" \t68 \t\t25 \t\t\t68 \t\t\t1\n67 \t68 \t\t26 \t\t\t68 \t\t\t1\n67"}︡{"stdout":" \t66 \t\t27 \t\t\t33 \t\t\t2\n67 \t68 \t\t28 \t\t\t68 \t\t\t1\n67"}︡{"stdout":" \t66 \t\t29 \t\t\t22 \t\t\t3\n67 \t66 \t\t30 \t\t\t66 \t\t\t1\n67 \t66 \t\t31 \t\t\t33 \t\t\t2\n67"}︡{"stdout":" \t66 \t\t32 \t\t\t22 \t\t\t3\n67 \t68 \t\t33 \t\t\t17 \t\t\t4\n67"}︡{"stdout":" \t68 \t\t34 \t\t\t34 \t\t\t2\n67 \t66 \t\t35 \t\t\t11 \t\t\t6\n67"}︡{"stdout":" \t66 \t\t36 \t\t\t66 \t\t\t1\n67 \t66 \t\t37 \t\t\t33 \t\t\t2\n67"}︡{"stdout":" \t66 \t\t38 \t\t\t11 \t\t\t6\n67 \t68 \t\t39 \t\t\t68 \t\t\t1\n67"}︡{"stdout":" \t66 \t\t40 \t\t\t66 \t\t\t1\n67 \t68 \t\t41 \t\t\t68 \t\t\t1\n67 \t68 \t\t42 \t\t\t68"}︡{"stdout":" \t\t\t1\n67 \t66 \t\t43 \t\t\t22 \t\t\t3\n67"}︡{"done":true,"once":false,"stderr":"\nToo many output messages: 257 (at most 256 per cell -- type 'smc?' to learn how to raise this limit): attempting to terminate..."}︡









