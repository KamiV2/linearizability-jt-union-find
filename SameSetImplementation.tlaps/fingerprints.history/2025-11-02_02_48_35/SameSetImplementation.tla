----------------------- MODULE SameSetImplementation -----------------------

\* Shared Memory Object: Union-find object, represented as idempotent function
\* ALGORITHM:

\*     0:  CHOOSE i, j \in [1..n]: Find_p(i) \/ Unite_p(i, j) \/ SameSet(i, j)
    
\*         Find_p(c):
\*     F1:    ret = F(c)
\*     FR:    Return ret

\*         Unite_p(c, d):
\*     U1:    ret = Unite(c, d)
\*     UR:    return ret


\*         SameSet_p(c, d):
\*     S1:     u = c; v = d; 
\*     S2:     u = Find(u) 
\*     S3:     v = Find(v); if u = v then ret = True; goto SR
\*     S4:     w = Find(u)
\*             if u = w then ret = False; goto SR else goto S2
\*     SR:     return ret

\* F is an idempotent function

EXTENDS FiniteSets, Integers
CONSTANT BOT, ACK, PROCESSES, N
VARIABLES pc, F, u, v, w, c, d, M, ret
NodeSet ==          1..N
ASSUME NisNat ==    (N \in Nat) /\ (N > 0)
ASSUME AckBotDef == BOT \notin NodeSet /\ ACK \notin NodeSet /\ BOT # ACK
ASSUME ExistProc == PROCESSES # {}

PCSet ==  {"0", "F1", "FR", "U1", "UR", "S1", "S2", "S3", "S4", "SR"}
OpSet ==  [PROCESSES -> {"F", "U", "S", BOT}]
ArgSet == [PROCESSES -> {BOT} \cup NodeSet \cup NodeSet \X NodeSet]
ReturnSet == [PROCESSES -> {ACK} \cup NodeSet \cup {TRUE, FALSE}]
UFAbsSet ==  {A \in [NodeSet -> NodeSet]: \A i \in NodeSet: A[A[i]] = A[i]}
StateSet == UFAbsSet

Configs == [sigma: StateSet, ret: ReturnSet, op: OpSet, arg: ArgSet]




UniteAbstract(x, y) ==  /\ F \in UFAbsSet /\ x \in NodeSet /\ y \in NodeSet
                        /\ \/ F' = [i \in NodeSet |-> IF F[i] = F[x] THEN F[y] ELSE F[i]]
                           \/ F' = [i \in NodeSet |-> IF F[i] = F[y] THEN F[x] ELSE F[i]]



F1(p) == /\ pc[p] = "F1"
         /\ pc' = [pc EXCEPT ![p] = "FR"]
         /\ ret' = [ret EXCEPT ![p] = F[c]]
         /\ M' = {t \in Configs: \E told \in M: /\ told.ret[p] = BOT 
                                                /\ t.sigma = told.sigma
                                                /\ t.ret = [told.ret EXCEPT ![p] = told.sigma[told.arg[p]]]
                                                /\ t.op = told.op
                                                /\ t.arg = told.arg}
         /\ UNCHANGED <<F, u, v, w, c, d>>
         
FR(p) == /\ pc[p] = "FR"
         /\ pc' = [pc EXCEPT ![p] = "0"]
         /\ M' = M \* TODO: FIX
         /\ UNCHANGED <<F, u, v, w, c, d, ret>>
         
U1(p) == /\ pc[p] = "U1"
         /\ pc' = [pc EXCEPT ![p] = "UR"]
         /\ UniteAbstract(c, d) 
         /\ ret' = [ret EXCEPT ![p] = ACK]
         /\ M' = M
         /\ UNCHANGED <<u, v, w, c, d>>

UR(p) == /\ pc[p] = "UR"
         /\ pc' = [pc EXCEPT ![p] = "0"]
         /\ M' = M
         /\ UNCHANGED <<F, u, v, w, c, d, ret>>

S1(p) == /\ pc[p] = "S1"
         /\ pc' = [pc EXCEPT ![p] = "S2"]
         /\ u' = [u EXCEPT ![p] = c]
         /\ v' = [v EXCEPT ![p] = d]
         /\ M' = M
         /\ UNCHANGED <<F, w, c, d, ret>>

S2(p) == /\ pc[p] = "S2"
         /\ pc' = [pc EXCEPT ![p] = "S3"]
         /\ u' = [u EXCEPT ![p] = F[u]]
         /\ M' = M
         /\ UNCHANGED <<F, v, w, c, d, ret>>
         
S3(p) == /\ pc[p] = "S3"
         /\ v' = [v EXCEPT ![p] = F[v]]
         /\ IF u = F[v]
                THEN    /\ ret' = [ret EXCEPT ![p] = TRUE]
                        /\ pc' = [pc EXCEPT ![p] = "SR"]
                ELSE    /\ ret' = ret
                        /\ pc' = [pc EXCEPT ![p] = "S4"]
         /\ M' = M
         /\ UNCHANGED <<F, v, w, c, d>>

S4(p) == /\ pc[p] = "S4"
         /\ w' = [w EXCEPT ![p] = F[u]]
         /\ IF u = F[u]
                THEN    /\ ret' = [ret EXCEPT ![p] = FALSE]
                        /\ pc' = [pc EXCEPT ![p] = "SR"]
                ELSE    /\ ret' = ret
                        /\ pc' = [pc EXCEPT ![p] = "S2"]
         /\ M' = M
         /\ UNCHANGED <<F, v, w, c, d>>

SR(p) == /\ pc[p] = "SR"
         /\ pc' = [pc EXCEPT ![p] = "0"]
         /\ M' = M
         /\ UNCHANGED <<F, u, v, w, c, d, ret>>

Decide(p) ==    /\ pc[p] = "0"
                /\  \/  /\ pc' = [pc EXCEPT ![p] = "F1"]
                        /\ \E i \in NodeSet:    
                                /\ c' = [c EXCEPT ![p] = i]
                                /\ M' = {t \in Configs: \E told \in M:  /\ told.ret[p] = BOT
                                                                        /\ told.op[p] = BOT
                                                                        /\ told.arg[p] = BOT
                                                                        /\ t.sigma = told.sigma
                                                                        /\ t.op = [told.op EXCEPT ![p] = "F"]
                                                                        /\ t.arg = [told.arg EXCEPT ![p] = i]
                                                                        /\ t.ret = told.ret}
                        /\ UNCHANGED <<F, u, v, w, c, d, ret>>
                    \/  /\ pc' = [pc EXCEPT ![p] = "U1"]
                        /\ \E i \in NodeSet: \E j \in NodeSet: 
                                /\ c' = [c EXCEPT ![p] = i]
                                /\ d' = [d EXCEPT ![p] = j]
                                /\ M' = {t \in Configs: \E told \in M:  /\ told.ret[p] = BOT
                                                                        /\ told.op[p] = BOT
                                                                        /\ told.arg[p] = BOT
                                                                        /\ t.sigma = told.sigma
                                                                        /\ t.op = [told.op EXCEPT ![p] = "U"]
                                                                        /\ t.arg = [told.arg EXCEPT ![p] = <<i, j>>]
                                                                        /\ t.ret = told.ret}
                        /\ UNCHANGED <<F, u, v, w, c, d, ret>>
                    \/  /\ pc' = [pc EXCEPT ![p] = "S1"]
                        /\ \E i \in NodeSet: \E j \in NodeSet: 
                                /\ c' = [c EXCEPT ![p] = i]
                                /\ d' = [d EXCEPT ![p] = j]
                                /\ M' = {t \in Configs: \E told \in M:  /\ told.ret[p] = BOT
                                                                        /\ told.op[p] = BOT
                                                                        /\ told.arg[p] = BOT
                                                                        /\ t.sigma = told.sigma
                                                                        /\ t.op = [told.op EXCEPT ![p] = "S"]
                                                                        /\ t.arg = [told.arg EXCEPT ![p] = <<i, j>>]
                                                                        /\ t.ret = told.ret}
                        /\ UNCHANGED <<F, u, v, w, c, d, ret>>

Step(p) ==  \/  F1(p)
            \/  FR(p)
            \/  U1(p)
            \/  UR(p)
            \/  S1(p)
            \/  S2(p)
            \/  S3(p)
            \/  S4(p)
            \/  SR(p)
            \/  Decide(p)


          

=============================================================================
\* Modification History
\* Last modified Sun Nov 02 02:48:34 IST 2025 by karunram
\* Created Sun Nov 02 01:20:50 IST 2025 by karunram
