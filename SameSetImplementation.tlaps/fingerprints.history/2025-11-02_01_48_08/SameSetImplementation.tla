----------------------- MODULE SameSetImplementation -----------------------

\* Shared Memory Object: Union-find object, represented as idempotent function
\* ALGORITHM:

\*     0:  CHOOSE i, j \in [1..n]: Find_p(i) \/ Unite_p(i, j) \/ SameSet(i, j)
    
\*         Find_p(c):
\*     F1:    u_F = F(c)
\*     F2:    Return u_F

\*         Unite_p(c, d):
\*     U1:    Unite(c, d)
\*     U2:    return ACK


\*         SameSet_p(c, d):
\*     S1:     u_S =  c; v_S = d; u_S = Find(u_S) 
\*     S2:     v_S = Find(v_S); if u = v then return True
\*     S3:     a_S = Find(u_S)
\*             if u = a_S then return False else goto S1

\* F is going to be the union-find object, represented as an element of Idems

EXTENDS FiniteSets, Integers
CONSTANT BOT, ACK, PROCESSES, N
VARIABLES pc, F, u_F, a_S, b_S, c, d, M
NodeSet ==          1..N
ASSUME NisNat ==    (N \in Nat) /\ (N > 0)
ASSUME AckBotDef == BOT \notin NodeSet /\ ACK \notin NodeSet /\ BOT # ACK
ASSUME ExistProc == PROCESSES # {}

Idems == {A \in [NodeSet -> NodeSet]: \A i \in NodeSet: A[A[i]] = A[i]}

UniteAbstract(x, y) ==  /\ F \in Idems /\ x \in NodeSet /\ y \in NodeSet
                        /\ \/ F' = [i \in NodeSet |-> IF F[i] = F[x] THEN F[y] ELSE F[i]]
                           \/ F' = [i \in NodeSet |-> IF F[i] = F[y] THEN F[x] ELSE F[i]]




=============================================================================
\* Modification History
\* Last modified Sun Nov 02 01:48:07 IST 2025 by karunram
\* Created Sun Nov 02 01:20:50 IST 2025 by karunram
