-------------------------- MODULE TypeEquivalence --------------------------

EXTENDS FiniteSets, Integers, TLAPS, Functions
CONSTANT U, ACK

ASSUME AckUDef == ACK \notin U
ASSUME UNotEmpty == U # {}

\* The following is an axiom which is true but often not recognized by backend provers.

ASSUME FunctionExtensionality == \A f, g, S: DOMAIN f = S /\ DOMAIN g = S /\ \A x \in S: f[x] = g[x] => f = g

Ops == {<<"Find", i>>: i \in U} \cup {<<"Unite", i, j>>: i, j \in U}
Rets == U \cup ACK

L_U == {P \in SUBSET [r: U, X: SUBSET U]:
            /\ \A x \in P : x.X # {}                           
            /\ \A x1, x2 \in P : x1 # x2 => x1.X \cap x2.X = {}
            /\ \A i \in U: \E x \in P: i \in x.X
            /\ \A p \in P : p.r \in p.X}
            
delta(s1, op, s2, r) ==
               /\ s1 \in L_U /\ s2 \in L_U
               /\ op \in Ops /\ r \in Rets
               /\ \/ /\ op[1] = "Find"
                     /\ \E p \in s1 :
                          /\ op[2] \in p.X
                          /\ p.r = r
                     /\ s2 = s1
                  \/ /\ op[1] = "Unite"
                     /\ r = ACK
                     /\ \E p1, p2 \in s1 :
                          /\ op[2] \in p1.X
                          /\ op[3] \in p2.X
                          /\ s2 \in {
                                (s1 \ {p1, p2}) \cup {[r |-> p1.r, X |-> p1.X \cup p2.X]},
                                (s1 \ {p1, p2}) \cup {[r |-> p2.r, X |-> p1.X \cup p2.X]}
                             }

Idems == {A \in [U -> U]: \A i \in U: A[A[i]] = A[i]}

delta_prime(s1, op, s2, r) ==
               /\ s1 \in Idems /\ s2 \in Idems
               /\ op \in Ops /\ r \in Rets
               /\ \/ /\ op[1] = "Find"
                     /\ r = s1[op[2]]
                     /\ s2 = s1
                  \/ /\ op[1] = "Unite"
                     /\ r = ACK
                     /\ s2 \in {[i \in U |-> IF s1[i] = s1[op[2]]
                                                 THEN s1[op[3]]
                                                 ELSE s1[i]],
                                 [i \in U |-> IF s1[i] = s1[op[3]]
                                                 THEN s1[op[2]]
                                                 ELSE s1[i]]}

f(P) == [i \in U |-> LET p == CHOOSE q \in P : i \in q.X IN p.r]

LEMMA UniqueBlock == \A P \in L_U: \A i \in U: \A p, q \in P: i \in p.X /\ i \in q.X => p = q
    BY DEF L_U, f

LEMMA MapsToRep == \A P \in L_U: \A i \in U: \A p \in P: i \in p.X => f(P)[i] = p.r
    BY UniqueBlock DEF L_U, f
 
LEMMA RepsUnique == \A P \in L_U: (\A x, y \in P: x.r = y.r => x = y)
    BY DEF L_U 
    
LEMMA RepsIdem == \A P \in L_U: \A i \in U: f(P)[i] = i 
                                                => (\E p \in P: /\ p.r = i
                                                                /\ p.X = {k \in U: f(P)[k] = i})
    BY DEF L_U, f
    
LEMMA IdemSameRep == \A P \in L_U: \A x, y \in U: 
                                f(P)[x] = f(P)[y]
                                        => \E p \in P: /\ x \in p.X
                                                       /\ y \in p.X
                                                       /\ p.r = f(P)[x]
    BY DEF L_U, f

LEMMA PreimageIsSet == \A P \in L_U: \A p \in P: p.X = {i \in U: f(P)[i] = p.r}
    BY RepsIdem, IdemSameRep DEF L_U, f    


THEOREM FunctionWellDefined == \A P \in L_U: f(P) \in Idems
    BY DEF f, L_U, Idems

LEMMA PartitionReshaping == \A P \in L_U: \A p, q \in P: (P \ {p, q}) \cup {[r |-> p.r, X |-> p.X \cup q.X]} \in L_U
  <1> SUFFICES ASSUME NEW P \in L_U,
                      NEW p \in P, NEW q \in P
               PROVE  (P \ {p, q}) \cup {[r |-> p.r, X |-> p.X \cup q.X]} \in L_U
    OBVIOUS
  <1> DEFINE w == [r |-> p.r, X |-> p.X \cup q.X]
  <1>1. w \in [r: U, X: SUBSET U]
    BY DEF L_U
  <1>2. \A t \in (P \ {p, q}): /\ t.X # {} 
                               /\ t.r \in t.X 
                               /\ \A s \in (P \ {p, q}): s # t => s.X \cap t.X = {}
                               /\ w.X \cap t.X = {}
    BY DEF L_U 
  <1>3. w.X # {} /\ w.r \in w.X /\ \A s \in (P \ {p, q}): w.X \cap s.X = {} 
    BY DEF L_U
  <1>4. \A i \in U: i \in w.X \/ \E t \in (P \ {p, q}): i \in t.X
    BY DEF L_U
  <1> \A r \in (P \ {p, q}) \cup {w}: r.X # {}
    BY <1>2, <1>3
  <1> \A r, s \in (P \ {p, q}) \cup {w}: r # s => r.X \cap s.X = {}
    BY <1>2, <1>3
  <1> \A i \in U: \E r \in (P \ {p, q}) \cup {w}: i \in r.X
    BY <1>4
  <1> \A r \in (P \ {p, q}) \cup {w}: r.r \in r.X
    BY <1>2, <1>3
  <1> (P \ {p, q}) \cup {w} \in SUBSET [r: U, X: SUBSET U]
    BY <1>1 DEF L_U
  <1> QED
    BY DEF L_U
    


THEOREM FunctionInjective == \A P, Q \in L_U: f(P) = f(Q) => P = Q
  <1> SUFFICES ASSUME NEW P \in L_U, NEW Q \in L_U,
                      f(P) = f(Q)
               PROVE  P = Q
    OBVIOUS
  <1> DEFINE A == f(P)
  <1> DEFINE B == f(Q)
  <1> DEFINE Part(X) == {[r |-> j, X |-> {i \in U: X[i] = j}]: j \in {k \in U: X[k] = k}}
  <1>1. P = Part(A)
    <2> \A x \in P: x \in Part(A)
      <3> SUFFICES ASSUME NEW x \in P
                   PROVE  x \in Part(A)
        OBVIOUS
      <3>1. x.X = {i \in U: A[i] = x.r}
        BY RepsUnique DEF A, f, L_U
      <3>2. A[x.r] = x.r /\ x.r \in U
        BY DEF L_U, f
      <3> [r |-> x.r, X |-> x.X] \in Part(A)
        BY <3>1, <3>2 DEF Part
      <3> QED
        BY DEF L_U
    <2> \A x \in Part(A): x \in P
      <3> SUFFICES ASSUME NEW x \in Part(A)
                   PROVE  x \in P
        OBVIOUS
      <3> PICK j \in U: A[j] = j /\ x.r = j /\ x.X = {i \in U: A[i] = j}
        BY DEF Part
      <3> PICK p \in P: p.r = j /\ p.X = {i \in U: A[i] = j}
        BY RepsIdem
      <3> QED
        OBVIOUS
    <2> QED
        OBVIOUS
  <1>2. Q = Part(B)
    <2> \A x \in Q: x \in Part(B)
      <3> SUFFICES ASSUME NEW x \in Q
                   PROVE  x \in Part(B)
        OBVIOUS
      <3>1. x.X = {i \in U: B[i] = x.r}
        BY RepsUnique DEF B, f, L_U
      <3>2. B[x.r] = x.r /\ x.r \in U
        BY DEF L_U, f
      <3> [r |-> x.r, X |-> x.X] \in Part(B)
        BY <3>1, <3>2 DEF Part
      <3> QED
        BY DEF L_U
    <2> \A x \in Part(B): x \in Q
      <3> SUFFICES ASSUME NEW x \in Part(B)
                   PROVE  x \in Q
        OBVIOUS
      <3> PICK j \in U: B[j] = j /\ x.r = j /\ x.X = {i \in U: B[i] = j}
        BY DEF Part
      <3> PICK p \in Q: p.r = j /\ p.X = {i \in U: B[i] = j}
        BY RepsIdem
      <3> QED
        OBVIOUS
    <2> QED
        OBVIOUS
  <1> QED
    BY <1>1, <1>2
    
THEOREM FunctionSurjective == \A A \in Idems: \E P \in L_U: f(P) = A
  <1> SUFFICES ASSUME NEW A \in Idems
               PROVE  \E P \in L_U: f(P) = A
    OBVIOUS
  <1> DEFINE PreImage(x) == {i \in U: A[i] = x}  
  <1> DEFINE Reps == {i \in U: A[i] = i}
  <1> DEFINE Q == {[r |-> x, X |-> PreImage(x)]: x \in Reps}
  <1>1. \A q \in Q: q.r \in U /\ q.X \in SUBSET U
    BY DEF Q, PreImage
  <1> DEFINE Xs == {q.X: q \in Q}
  <1>2. \A x1, x2 \in Xs : x1 # x2 => x1 \cap x2 = {}
    BY DEF Xs, PreImage, Q
  <1>3. \A x \in Xs : x # {}
    BY DEF Xs, PreImage, Q
  <1>4. \A i \in U: \E x \in Xs: i \in x
    BY DEF Xs, PreImage, Q, Idems        
  <1>5. \A p \in Q : p.r \in p.X
    BY DEF Xs, PreImage, Idems
  <1>a. Q \in L_U
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF L_U
  <1>b. \A i \in U: f(Q)[i] = A[i]
    <2> USE <1>a
    <2> SUFFICES ASSUME NEW i \in U
                 PROVE  f(Q)[i] = A[i]
      OBVIOUS
    <2>1. CASE A[i] = i
        <3>1. A[i] \in Reps
            BY <2>1 DEF Reps
        <3>2. i \in PreImage(i)
            BY <2>1 DEF Reps, PreImage
        <3>3. \E q \in Q: q.r = i /\ i \in q.X
            BY <2>1, <3>2 DEF PreImage, Reps
        <3> QED
            BY <2>1, <3>3 DEF f
    <2>2. CASE A[i] # i
        <3> DEFINE x == A[i]
        <3>1. x \in Reps /\ i \in PreImage(x)
            BY <2>2 DEF Reps, PreImage, Idems
        <3>2. \E q \in Q: q.r = x /\ i \in q.X
            BY <3>1 DEF Reps, PreImage
        <3> QED
            BY <3>2 DEF f
    <2> QED
        BY <2>1, <2>2
  <1> QED
    BY FunctionWellDefined, <1>a, <1>b DEF Idems
    
THEOREM FunctionBijective == FunctionInjective /\ FunctionSurjective /\ FunctionWellDefined
    BY FunctionInjective, FunctionSurjective, FunctionWellDefined
    
    
THEOREM FunctionRespectsDelta == 
               \A s1, s2 \in L_U: \A o \in Ops: \A r \in Rets:
                    delta(s1, o, s2, r) <=> delta_prime(f(s1), o, f(s2), r)
  <1> SUFFICES ASSUME NEW s1 \in L_U, NEW s2 \in L_U,
                      NEW o \in Ops,
                      NEW r \in Rets
               PROVE  delta(s1, o, s2, r) <=> delta_prime(f(s1), o, f(s2), r)
    OBVIOUS
  <1>1. delta(s1, o, s2, r) => delta_prime(f(s1), o, f(s2), r)
    <2> SUFFICES ASSUME delta(s1, o, s2, r)
                 PROVE  delta_prime(f(s1), o, f(s2), r)
      OBVIOUS
    <2>1. CASE /\ o[2] \in U
               /\ o[1] = "Find"
               /\ \E p \in s1 :
                    /\ o[2] \in p.X
                    /\ p.r = r
               /\ s2 = s1
        <3> \E p \in s1: o[2] \in p.X /\ p.r = f(s1)[o[2]]
            BY <2>1 DEF f
        <3> /\ o[1] = "Find"
            /\ r = f(s1)[o[2]]
            /\ f(s2) = f(s1)
            BY <2>1 DEF f, delta_prime
        <3> QED
            BY <2>1, FunctionWellDefined DEF delta_prime             
    <2>2. CASE /\ o[2] \in U /\ o[3] \in U
               /\ o[1] = "Unite"
               /\ r = ACK
               /\ \E p1, p2 \in s1:
                    /\ o[2] \in p1.X
                    /\ o[3] \in p2.X
                    /\ s2 \in {(s1 \ {p1, p2}) \cup {[r |-> p1.r, X |-> p1.X \cup p2.X]},
                               (s1 \ {p1, p2}) \cup {[r |-> p2.r, X |-> p1.X \cup p2.X]}}
        <3> PICK p, q \in s1:
                /\ o[2] \in p.X
                /\ o[3] \in q.X
                /\ \/ s2 = (s1 \ {p, q}) \cup {[r |-> p.r, X |-> p.X \cup q.X]}
                   \/ s2 = (s1 \ {p, q}) \cup {[r |-> q.r, X |-> p.X \cup q.X]}
            BY <2>2
        <3>1. CASE s2 = (s1 \ {p, q}) \cup {[r |-> p.r, X |-> p.X \cup q.X]}
          <4> f(s2) = [i \in U |-> IF f(s1)[i] = f(s1)[o[3]]
                                               THEN f(s1)[o[2]]
                                               ELSE f(s1)[i]]
            <5> SUFFICES ASSUME NEW i \in U
                         PROVE f(s2)[i] = IF f(s1)[i] = f(s1)[o[3]]
                                               THEN f(s1)[o[2]]
                                               ELSE f(s1)[i]
                BY <2>2, FunctionWellDefined DEF Idems
            <5>1. CASE i \in p.X
                <6> \E d \in s2: i \in d.X /\ d.r = p.r
                    BY <3>1, <5>1
                <6> QED
                    BY MapsToRep, <5>1, <2>2 DEF f
            <5>2. CASE i \in q.X
                <6> \E d \in s2: i \in d.X /\ d.r = p.r
                    BY <3>1, <5>2
                <6> QED
                    BY MapsToRep, <5>2, <2>2 DEF f
            <5>3. CASE i \notin p.X /\ i \notin q.X
                <6> PICK d \in s1: i \in d.X /\ d # p /\ d # q
                    BY <3>1, <5>3 DEF L_U
                <6> f(s1)[i] # q.r
                    BY RepsUnique, UniqueBlock, <3>1, <2>2 DEF f, L_U
                <6> QED
                    BY UniqueBlock, <5>3, MapsToRep, <2>2 DEF f
            <5> QED
                BY <5>1, <5>2, <5>3
          <4> QED
            BY <2>2, FunctionWellDefined DEF delta_prime
        <3>2. CASE s2 = (s1 \ {p, q}) \cup {[r |-> q.r, X |-> p.X \cup q.X]}
          <4> f(s2) = [i \in U |-> IF f(s1)[i] = f(s1)[o[2]]
                                               THEN f(s1)[o[3]]
                                               ELSE f(s1)[i]]
            <5> SUFFICES ASSUME NEW i \in U
                         PROVE f(s2)[i] = IF f(s1)[i] = f(s1)[o[2]]
                                               THEN f(s1)[o[3]]
                                               ELSE f(s1)[i]
                BY <2>2, FunctionWellDefined DEF Idems
            <5>1. CASE i \in p.X
                <6> \E d \in s2: i \in d.X /\ d.r = q.r
                    BY <3>2, <5>1
                <6> QED
                    BY MapsToRep, <5>1, <2>2 DEF f
            <5>2. CASE i \in q.X
                <6> \E d \in s2: i \in d.X /\ d.r = q.r
                    BY <3>2, <5>2
                <6> QED
                    BY MapsToRep, <5>2, <2>2 DEF f
            <5>3. CASE i \notin p.X /\ i \notin q.X
                <6> PICK d \in s1: i \in d.X /\ d # p /\ d # q
                    BY <3>2, <5>3 DEF L_U
                <6> f(s1)[i] # p.r
                    BY RepsUnique, UniqueBlock, <3>2, <2>2 DEF f, L_U
                <6> QED
                    BY UniqueBlock, <5>3, MapsToRep, <2>2 DEF f
            <5> QED
                BY <5>1, <5>2, <5>3
          <4> QED
            BY <2>2, FunctionWellDefined DEF delta_prime
        <3> QED
            BY <3>1, <3>2, <2>2
    <2>3. QED
      BY <2>1, <2>2 DEF delta, Ops
  <1>2. ~delta(s1, o, s2, r) => ~delta_prime(f(s1), o, f(s2), r)
    <2> SUFFICES ASSUME ~delta(s1, o, s2, r)
                 PROVE  ~delta_prime(f(s1), o, f(s2), r)
      OBVIOUS
    <2>h. ~(\/ /\ o[1] = "Find"
               /\ \E p \in s1 : /\ o[2] \in p.X
                                /\ p.r = r
               /\ s2 = s1
            \/ /\ o[1] = "Unite"
               /\ r = ACK
               /\ \E p1, p2 \in s1 :
                   /\ o[2] \in p1.X
                   /\ o[3] \in p2.X
                   /\ s2 \in {(s1 \ {p1, p2}) \cup {[r |-> p1.r, X |-> p1.X \cup p2.X]},
                              (s1 \ {p1, p2}) \cup {[r |-> p2.r, X |-> p1.X \cup p2.X]}})
        BY DEF delta
    <2> o[1] = "Find" \/ o[1] = "Unite"
        BY DEF Ops
    <2>1. CASE o[1] = "Find"
        <3> \/ \A p \in s1: o[2] \notin p.X \/ p.r # r
            \/ s2 # s1
            BY <2>1, <2>h
        <3>1. CASE \A p \in s1: o[2] \notin p.X \/ p.r # r
            <4> PICK p \in s1: o[2] \in p.X
                BY <2>1 DEF L_U, Ops
            <4> QED
                BY MapsToRep, <2>1, <3>1 DEF delta_prime, Ops
        <3>2. CASE s2 # s1
            BY <2>1, <3>2, FunctionInjective DEF delta_prime
        <3> QED
            BY <3>1, <3>2
    <2>2. CASE o[1] = "Unite"
        <3>a. \/ r # ACK
              \/ \A p1, p2 \in s1:
                  \/ o[2] \notin p1.X
                  \/ o[3] \notin p2.X
                  \/ s2 \notin {(s1 \ {p1, p2}) \cup {[r |-> p1.r, X |-> p1.X \cup p2.X]},
                                (s1 \ {p1, p2}) \cup {[r |-> p2.r, X |-> p1.X \cup p2.X]}}
            BY <2>2, <2>h
         <3>1. CASE r # ACK
            BY <2>2, <3>1, <3>a DEF delta_prime
         <3>2. CASE \A p1, p2 \in s1:
                        \/ o[2] \notin p1.X
                        \/ o[3] \notin p2.X
                        \/ s2 \notin {(s1 \ {p1, p2}) \cup {[r |-> p1.r, X |-> p1.X \cup p2.X]},
                                      (s1 \ {p1, p2}) \cup {[r |-> p2.r, X |-> p1.X \cup p2.X]}}
            <4> PICK p1 \in s1: o[2] \in p1.X
                BY <2>2 DEF L_U, Ops
            <4> PICK p2 \in s1: o[3] \in p2.X
                BY <2>2 DEF L_U, Ops
            <4> DEFINE a1 == (s1 \ {p1, p2}) \cup {[r |-> p1.r, X |-> p1.X \cup p2.X]}
            <4> DEFINE a2 == (s1 \ {p1, p2}) \cup {[r |-> p2.r, X |-> p1.X \cup p2.X]}
            <4>h. s2 \notin {a1, a2}
                BY <3>2
            <4>k. f(s2) \notin {f(a1), f(a2)}
                BY PartitionReshaping, FunctionInjective, <4>h
            <4>l. a1 \in L_U /\ a2 \in L_U
                BY PartitionReshaping
            <4> DEFINE b1 == [i \in U |-> IF f(s1)[i] = f(s1)[o[3]] THEN f(s1)[o[2]] ELSE f(s1)[i]]
            <4> DEFINE b2 == [i \in U |-> IF f(s1)[i] = f(s1)[o[2]] THEN f(s1)[o[3]] ELSE f(s1)[i]] 
            <4> o[2] \in U /\ o[3] \in U
                BY <2>2 DEF Ops
            <4>a. f(a1) = b1
                <5> SUFFICES ASSUME NEW i \in U
                             PROVE f(a1)[i] = b1[i]
                    BY PartitionReshaping, FunctionWellDefined DEF Idems
                <5>1. CASE i \in p2.X
                    <6> \E d \in a1: i \in d.X /\ d.r = p1.r
                        BY <4>l, <5>1
                    <6> QED
                        BY MapsToRep, <4>l, <5>1 DEF f
                <5>2. CASE i \in p1.X
                    <6> \E d \in a1: i \in d.X /\ d.r = p1.r
                        BY <4>l, <5>2
                    <6> QED
                        BY MapsToRep, <4>l, <5>2 DEF f
                <5>3. CASE i \notin p1.X \cup p2.X
                    <6> \E d \in a1: i \in d.X /\ d # p1 /\ d # p2
                        BY <4>l, <5>3, RepsUnique DEF L_U
                    <6> QED
                        BY RepsUnique, UniqueBlock, MapsToRep, <4>l, <5>3 DEF f
                <5> QED
                    BY <5>1, <5>2, <5>3
            <4>b. f(a2) = b2
                <5> SUFFICES ASSUME NEW i \in U
                             PROVE f(a2)[i] = b2[i]
                    BY FunctionExtensionality, PartitionReshaping, FunctionWellDefined DEF Idems
                <5>1. CASE i \in p2.X
                    <6> \E d \in a2: i \in d.X /\ d.r = p2.r
                        BY <4>l, <5>1
                    <6> QED
                        BY MapsToRep, <4>l, <5>1 DEF f
                <5>2. CASE i \in p1.X
                    <6> \E d \in a2: i \in d.X /\ d.r = p2.r
                        BY <4>l, <5>2
                    <6> QED
                        BY MapsToRep, <4>l, <5>2 DEF f
                <5>3. CASE i \notin p1.X \cup p2.X
                    <6> \E d \in a2: i \in d.X /\ d # p1 /\ d # p2
                        BY <4>l, <5>3, RepsUnique DEF L_U
                    <6> QED
                        BY RepsUnique, UniqueBlock, MapsToRep, <4>l, <5>3 DEF f
                <5> QED
                    BY <5>1, <5>2, <5>3
            <4> QED
                BY <2>2, <4>k, <4>a, <4>b DEF delta_prime, Ops
        <3> QED
            BY <3>1, <3>2, <3>a
    <2> QED
        BY <2>1, <2>2
  <1> QED
    BY <1>1, <1>2

=============================================================================
\* Modification History
\* Last modified Tue Jun 03 05:52:59 EDT 2025 by karunram
\* Created Tue Jun 03 05:52:54 EDT 2025 by karunram
