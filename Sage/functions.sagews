"""
This file implements various functions related to Lucas Groups and Lucas Sequences. There is functionality for 
finding the elements of a Lucas Group given values for the parameters D and p, finding the order of a Lucas Sequence
given values for the parameters P, p, and D, and testing if an element is a generator of a Lucas Group. Then, 
functions that implement several existing pseudoprime/primality tests based on Lucas Sequences are implemented. 
Finally, functions that implement novel primality tests based on Lucas Groups are implemented.
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
            if (X**2 - D * Y**2) % p == 4 % p:
                solutions.append((X, Y))
    solutions = set(solutions)
    return solutions

#implements the binary operation for Lucas Groups
def bin_op(x, y, D, p):
    return ((x[0] * y[0] + D * x[1] * y[1]) * 2.inverse_mod(p) % p, (x[0] * y[1] + x[1] * y[0]) * 2.inverse_mod(p) % p)

#tests if an element is a generator of the Lucas Group
def gen_test(element, D, p):
    order_ele = 0
    new_element = element
    f = factor(p)
    max_order = 1
    for i in f:
        max_order *= 3 * i[0]**i[1] / 2
    #finds the order of the element
    for i in range(2, max_order):
        new_element = bin_op(new_element, element, D, p)
        if new_element == (2, 0):
            order_ele = i
            break
    #checks the prime case
    if p in Primes():
        if order_ele == p - 1 or order_ele == p + 1:
            return True
        else:
            return False
    #checks the prime power case
    elif p not in Primes() and is_prime_power(p):
        p0 = divisors(p)[1]
        if jacobi_symbol(D, p0) == 1:
            if order_ele == p * (p0 - 1) / p0:
                return True
            else:
                return False
        elif jacobi_symbol(D, p0) == -1:
            if order_ele == p * (p0 + 1) / p0:
                return True
            else:
                return False
        elif jacobi_symbol(D, p0) == 0:
            if order_ele == 2 * p:
                return True
            else:
                return False
    #checks the remaining cases
    else:
        new_order = 1
        for i in f:
            new_order = lcm(new_order, len(elements(D, i[0])))
        if order_ele == new_order:
            return True
        else:
            return False


#because the Lucas Sequence mod p forms a cyclic subgroup, we can compute its order by finding the order of the generator, (P, 1)
def lucas_sequence(P, p, D):
    generator = (P, 1)
    element = (P, 1)
    sequence = [(2, 0), (P, 1)]
    while sequence[-1] != (2, 0):
        sequence.append(((sequence[-1][0] * P - sequence[-2][0]) % p , (sequence[-1][1] * P - sequence[-2][1]) % p))
    return len(sequence) - 1

#finds the order of x mod p
def order(x, p):
    order_x = 0
    for i in range(1, p):
        if x**i % p == 1:
            order_x = i
            break
    return order_x

#implements a primality test
def is_prime(p):
    prime = True
    for i in range(2, int(sqrt(p) + 1)):
        if p % i == 0:
	    prime = False
	    break
    return prime

#implements a pseudoprime test
def probable_test(n, P):
    generator = (P, 1)
    element = (P, 1)
    for i in range(1, n - jacobi_symbol(P**2 - 4, n)):
        element = bin_op(generator, element, P**2 - 4, n)
    if element[1] == 0:
        return "Pseudoprime"
    else:
        return "Not Pseudoprime"

#implements the Strong Lucas Pseudoprime test
def strong_test(n, P):
    #these are computations associated with the primality test
    f = list(factor(p - jacobi_symbol(P**2 - 4 % n, p)))
    s = 0
    for j in f:
        if j[0] == 2:
            s = j[1]
            break
    q = (p - jacobi_symbol(D, p)) / 2**s
    generator = (P, 1)
    element = (P, 1)
    #generates the Lucas sequence
    lucas_sequence = [(2, 0), (P, 1)]
    for i in range(2, n - jacobi_symbol(P**2 - 4, n) + 1):
        element = bin_op(generator, element, P**2 - 4, n)
        lucas_sequence.append(element)
    if lucas_sequence[q][1] == 0:
        return "Strong Pseudoprime"
    else:
        for r in range(0, s):
            if lucas_sequence[q  *2**r][0] == 0:
                return "Strong Pseudoprime"
        return "Not Strong Pseudoprime"

#implements a new version of the weak primality test based on Lucas Groups
def new_weak_primality_test(P, D, p):
    lucas_group = list(elements(D, p))
    generator = choice(lucas_group)
    element = generator
    for i in range(2, p - jacobi_symbol(D, p) + 1):
        element = bin_op(generator, element, D, p)
    if element == (2, 0):
        return True

#implements a new primality test based on Lucas Groups
def new_primality_test(P, D, p):
    lucas_group = list(elements(D, p))
    generator = choice(lucas_group)
    lucas_group = [(2, 0), generator]
    element = generator
    #we perform analogous computations to the existing Strong Lucas Pseudoprime Test
    f = list(factor(p - jacobi_symbol(D, p)))
    s = 0
    for j in f:
        if j[0] == 2:
            s = j[1]
            break
    q = (p - jacobi_symbol(D, p)) / 2**s
    #however, here we instead look at elements of the associated Lucas Group, not Lucas Sequence
    for i in range(2, p - jacobi_symbol(D, p) + 1):
        element = bin_op(generator, element, D, p)
        lucas_group.append(element)
    if lucas_group[q][1] == 0:
        return True
    else:
        for r in range(0, s):
            if lucas_group[q * 2**r][0] == 0:
                return True
    return False











