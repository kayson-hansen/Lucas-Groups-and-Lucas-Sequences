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
