"""
This file implements various functions related to Lucas Groups. There is functionality for finding the elements
of a Lucas Group given values for the parameters D and p, testing if an element generates the group, finding
the order of the Lucas Group, etc. 
"""

import random
from math import sqrt
from arith_lib import gcd
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
    return len(sequence) - 1
    for i in range(1, p**2):
        element = bin_op(generator, element, D, p)
        if element == (2,0):
            return i+1

#finds the order of x mod p
def order(x, p):
    order_x = 0
    for i in range(1, p):
        if x**i % p == 1:
            order_x = i
            break
    return order_x

#primality test
def is_prime(p):
	prime = True
	for i in range(2, int(sqrt(p)+1)):
		if p % i == 0:
			prime = False
			break
	return prime

#returns if P is a pseudoprime or not
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

#implements a new version of the weak primality test
def new_weak_primality_test(P, D, p):
    lucas_group = list(elements(D,p))
    generator = choice(lucas_group)
    element = generator
    for i in range(2, p - jacobi_symbol(D, p)+1):
        element = bin_op(generator, element, D, p)
    if element == (2,0):
        return True

#implements a new primality test
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











