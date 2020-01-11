import random

#finds the elements of a Lucas Group
def elements(D,p):
    solutions = []
    for X in range(0, p):
        for Y in range(0, p):
            if (X^2 - D*Y^2)%p == 4%p:
                solutions.append((X,Y))
    return "Order of Lucas Group: %d" % (order(solutions))

#returns info about the Lucas Sequence assuming Q=1
def lucas_sequence(P, p):
    sequence = [(2 % p, 0), (P % p, 1)]
    index = 1
    end = False
    while True:
        sequence.append(((P*(sequence[index][0])-(sequence[index-1][0])) % p, (P*(sequence[index][0])-(sequence[index-1][0])) % p))
        for i in range(0, len(sequence)-1):
            if sequence[-1] == sequence[i]:
                sequence.pop()
                end = True
                break
        if end == True:
            break
        index += 1
    order_P = 0
    for i in range(1, p):
        if P^i % p == 1:
            order_P = i
            break
    answer = "Order of Lucas Sequence: %d, Order of P: %d" % (len(sequence), order_P)
    return answer

#find the elements of the sequence (x_n,y_n) mod p
def sequences(solutions,D,p):
    (X,Y) = random.choice(solutions)
    for i in solutions:
        if i[1] < Y and i[1] > 0:
            (X,Y) = i
    sequence = []
    for n in range(0, p):
        x_n = ((X/1.0+sqrt(D)*Y/1.0)^n+(X/1.0-sqrt(D)*Y/1.0)^n)/2.0
        y_n = ((X/1.0+sqrt(D)*Y/1.0)^n-(X/1.0-sqrt(D)*Y/1.0)^n)/(2.0*sqrt(D))
        if (x_n,y_n) not in sequence:
            sequence.append((x_n,y_n))
    return sequence

def order(group):
    return len(group)

for p in range(3, 30):
    for P in range(1, p):
        print("p: %d" % p, elements(P^2-4,p), lucas_sequence(P,p))









