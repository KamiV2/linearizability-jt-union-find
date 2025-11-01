---------------------------- MODULE jtunionfind ----------------------------

\* Main module file. 
\* See Linearizability.tla for the proof of linearizability.
\* See StrongLinearizability.tla for the proof of strong linearizability.
\* See TypeEquivalence.tla for the proof that the idempotent representation 
\*     is equivalent to the natural labelled partition representation.


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
  <1> USE DEF Init, TypeOK
  <1> SUFFICES ASSUME Init
               PROVE  TypeOK
    OBVIOUS
  <1>1. Valid_pc
    BY DEF Valid_pc, PCSet
  <1>2. Valid_F
    BY DEF Valid_F, InitF
  <1>3. Valid_u
    BY DEF Valid_u
  <1>4. Valid_v
    BY DEF Valid_v
  <1>5. Valid_w
    BY DEF Valid_w
  <1>6. Valid_c
    BY DEF Valid_c
  <1>7. Valid_d
    OBVIOUS
  <1>8. Valid_ret
    OBVIOUS
  <1>9. Valid_M
    BY DEF Init, Valid_M, Configs, InitRet, InitOp, InitState, InitArg, StateSet, ReturnSet, OpSet, ArgSet
  <1>10. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF TypeOK
    
    
LEMMA NextTypeOK == TypeOK /\ [Next]_varlist => TypeOK'
  
THEOREM TypeSafety == SameSetSpec => []TypeOK



=============================================================================
\* Modification History
\* Last modified Sun Nov 02 03:27:52 IST 2025 by karunram
\* Created Fri Apr 04 00:28:14 EDT 2025 by karunram
