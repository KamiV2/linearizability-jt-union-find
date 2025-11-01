------------------------- MODULE SameSetTypeSafety -------------------------

EXTENDS SameSetImplementation, TLAPS

\* Type Statements
Valid_pc ==     pc \in [PROCESSES -> PCSet]
Valid_F ==      F \in [NodeSet -> NodeSet]
Valid_u ==      u \in [PROCESSES -> NodeSet]
Valid_v ==      v \in [PROCESSES -> NodeSet]
Valid_w ==      w \in [PROCESSES -> NodeSet]
Valid_c ==      c \in [PROCESSES -> NodeSet]
Valid_d ==      d \in [PROCESSES -> NodeSet]
Valid_ret ==    ret \in [PROCESSES -> {ACK, TRUE, FALSE} \cup NodeSet]
Valid_M ==      M \in SUBSET Configs

TypeOK == /\ Valid_pc
          /\ Valid_F
          /\ Valid_u
          /\ Valid_v
          /\ Valid_w
          /\ Valid_c
          /\ Valid_d
          /\ Valid_ret
          /\ Valid_M
         
LEMMA InitTypeOK == Init => TypeOK 
    
LEMMA NextTypeOK == TypeOK /\ [Next]_varlist => TypeOK'
  
THEOREM TypeSafety == SameSetSpec => []TypeOK


=============================================================================
\* Modification History
\* Last modified Sun Nov 02 03:11:24 IST 2025 by karunram
\* Created Sun Nov 02 03:06:54 IST 2025 by karunram
