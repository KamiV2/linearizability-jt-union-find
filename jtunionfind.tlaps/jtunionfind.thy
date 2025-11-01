(* automatically generated -- do not edit manually *)
theory jtunionfind imports Constant Zenon begin
ML_command {* writeln ("*** TLAPS PARSED\n"); *}
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'11:
(* usable definition IsFiniteSet suppressed *)
(* usable definition Cardinality suppressed *)
fixes BOT
fixes ACK
fixes PROCESSES
fixes N
fixes pc pc'
fixes F F'
fixes u u'
fixes v v'
fixes w w'
fixes a_ca a_ca'
fixes d d'
fixes M M'
fixes ret ret'
(* usable definition NodeSet suppressed *)
(* usable definition varlist suppressed *)
(* usable definition PCSet suppressed *)
(* usable definition OpSet suppressed *)
(* usable definition ArgSet suppressed *)
(* usable definition ReturnSet suppressed *)
(* usable definition UFAbsSet suppressed *)
(* usable definition StateSet suppressed *)
(* usable definition Configs suppressed *)
(* usable definition InitState suppressed *)
(* usable definition InitF suppressed *)
(* usable definition InitRet suppressed *)
(* usable definition InitOp suppressed *)
(* usable definition InitArg suppressed *)
(* usable definition UFUniteShared suppressed *)
(* usable definition UFSUnite suppressed *)
(* usable definition F1 suppressed *)
(* usable definition FR suppressed *)
(* usable definition U1 suppressed *)
(* usable definition UR suppressed *)
(* usable definition S1 suppressed *)
(* usable definition S2 suppressed *)
(* usable definition S3 suppressed *)
(* usable definition S4 suppressed *)
(* usable definition SR suppressed *)
(* usable definition Decide suppressed *)
(* usable definition Step suppressed *)
(* usable definition Next suppressed *)
(* usable definition SameSetSpec suppressed *)
(* usable definition Valid_pc suppressed *)
(* usable definition Valid_F suppressed *)
(* usable definition Valid_u suppressed *)
(* usable definition Valid_v suppressed *)
(* usable definition Valid_w suppressed *)
(* usable definition Valid_c suppressed *)
(* usable definition Valid_d suppressed *)
(* usable definition Valid_ret suppressed *)
(* usable definition Valid_M suppressed *)
assumes v'58: "((((((pc) = ([ p \<in> (PROCESSES)  \<mapsto> (''0'')]))) & (((F) = (InitF))) & (((u) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> (NodeSet)))]))) & (((M) = ({(((''sigma'' :> (InitState)) @@ (''ret'' :> (InitRet)) @@ (''op'' :> (InitOp)) @@ (''arg'' :> (InitArg))))})))) \<Longrightarrow> ((a_Validunde_pca) & (a_Validunde_Fa) & (a_Validunde_ua) & (a_Validunde_va) & (a_Validunde_wa) & (a_Validunde_ca) & (a_Validunde_da) & (a_Validunde_reta) & (a_Validunde_Ma))))"
shows "((((((pc) = ([ p \<in> (PROCESSES)  \<mapsto> (''0'')]))) & (((F) = (InitF))) & (((u) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((v) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((w) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((a_ca) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((d) \<in> ([(PROCESSES) \<rightarrow> (NodeSet)]))) & (((ret) \<in> ([(PROCESSES) \<rightarrow> ((({(ACK), (TRUE), (FALSE)}) \<union> (NodeSet)))]))) & (((M) = ({(((''sigma'' :> (InitState)) @@ (''ret'' :> (InitRet)) @@ (''op'' :> (InitOp)) @@ (''arg'' :> (InitArg))))})))) \<Rightarrow> ((a_Validunde_pca) & (a_Validunde_Fa) & (a_Validunde_ua) & (a_Validunde_va) & (a_Validunde_wa) & (a_Validunde_ca) & (a_Validunde_da) & (a_Validunde_reta) & (a_Validunde_Ma))))"(is "PROP ?ob'11")
proof -
ML_command {* writeln "*** TLAPS ENTER 11"; *}
show "PROP ?ob'11"

(* BEGIN ZENON INPUT
;; file=jtunionfind.tlaps/tlapm_7f1662.znn; PATH='/usr/bin:/bin:/usr/sbin:/sbin:/usr/local/bin:/usr/local/lib/tlaps/bin'; zenon -p0 -x tla -oisar -max-time 1d "$file" >jtunionfind.tlaps/tlapm_7f1662.znn.out
;; obligation #11
$hyp "v'58" (=> (/\ (= pc (TLA.Fcn PROCESSES ((p) "0"))) (= F InitF)
(TLA.in u (TLA.FuncSet PROCESSES NodeSet)) (TLA.in v
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in w (TLA.FuncSet PROCESSES NodeSet))
(TLA.in a_ca (TLA.FuncSet PROCESSES NodeSet)) (TLA.in d
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in ret
(TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.) NodeSet))) (= M
(TLA.set (TLA.record "sigma" InitState "ret" InitRet "op" InitOp "arg" InitArg)))) (/\ a_Validunde_pca
a_Validunde_Fa a_Validunde_ua a_Validunde_va a_Validunde_wa a_Validunde_ca
a_Validunde_da a_Validunde_reta a_Validunde_Ma))
$goal (=> (/\ (= pc (TLA.Fcn PROCESSES ((p) "0"))) (= F InitF) (TLA.in u
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in v (TLA.FuncSet PROCESSES NodeSet))
(TLA.in w (TLA.FuncSet PROCESSES NodeSet)) (TLA.in a_ca
(TLA.FuncSet PROCESSES NodeSet)) (TLA.in d (TLA.FuncSet PROCESSES NodeSet))
(TLA.in ret (TLA.FuncSet PROCESSES (TLA.cup (TLA.set ACK T. F.) NodeSet)))
(= M
(TLA.set (TLA.record "sigma" InitState "ret" InitRet "op" InitOp "arg" InitArg))))
(/\ a_Validunde_pca a_Validunde_Fa a_Validunde_ua a_Validunde_va
a_Validunde_wa a_Validunde_ca a_Validunde_da a_Validunde_reta
a_Validunde_Ma))
END ZENON  INPUT *)
(* PROOF-FOUND *)
(* BEGIN-PROOF *)
proof (rule zenon_nnpp)
 have z_Ha:"(((pc=Fcn(PROCESSES, (\<lambda>p. ''0'')))&((F=InitF)&((u \\in FuncSet(PROCESSES, NodeSet))&((v \\in FuncSet(PROCESSES, NodeSet))&((w \\in FuncSet(PROCESSES, NodeSet))&((a_ca \\in FuncSet(PROCESSES, NodeSet))&((d \\in FuncSet(PROCESSES, NodeSet))&((ret \\in FuncSet(PROCESSES, ({ACK, TRUE, FALSE} \\cup NodeSet)))&(M={(''sigma'' :> (InitState) @@ ''ret'' :> (InitRet) @@ ''op'' :> (InitOp) @@ ''arg'' :> (InitArg))})))))))))=>(a_Validunde_pca&(a_Validunde_Fa&(a_Validunde_ua&(a_Validunde_va&(a_Validunde_wa&(a_Validunde_ca&(a_Validunde_da&(a_Validunde_reta&a_Validunde_Ma)))))))))" (is "?z_hc=>?z_hbz")
 using v'58 by blast
 assume z_Hb:"(~(?z_hc=>?z_hbz))"
 show FALSE
 by (rule notE [OF z_Hb z_Ha])
qed
(* END-PROOF *)
ML_command {* writeln "*** TLAPS EXIT 11"; *} qed
end
