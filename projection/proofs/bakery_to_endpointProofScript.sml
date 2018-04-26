open preamble endpointLangTheory bakery_to_endpointTheory
              endpointSemanticsTheory endpointPropsTheory
              semBakeryTheory;

val _ = new_theory "bakery_to_endpointProof";


val all_distinct_nub' = Q.store_thm("all_distinct_nub'",
  `∀l. ALL_DISTINCT (nub' l)`,
  rw [ALL_DISTINCT,nub'_def]
  \\ Induct_on `l`
  \\ rw [ALL_DISTINCT,nub'_def,FILTER_ALL_DISTINCT,MEM_FILTER]
);

val procsOf_all_distinct = Q.store_thm("procsOf_all_distinct",
  `∀c. ALL_DISTINCT (procsOf c)`,
  Induct_on `c` >> rw [procsOf_def,ALL_DISTINCT,all_distinct_nub']
);

val cn_ignore_com = Q.store_thm("cn_ignore_com",
  `∀p1 v1 p2 v2 s c' pl q.
    ¬MEM p1 pl ∧ ¬MEM p2 pl
    ⇒ compile_network s (Com p1 v1 p2 v2 c') pl q = compile_network s c' pl q`,
  Induct_on `pl`
  \\ rw [compile_network_def,project_def,projectS_def]
);

val cn_ignore_sel = Q.store_thm("cn_ignore_sel",
  `∀p1 b p2 s c' pl q.
    ¬MEM p1 pl ∧ ¬MEM p2 pl
    ⇒ compile_network s (Sel p1 b p2 c') pl q = compile_network s c' pl q`,
  Induct_on `pl`
  \\ rw [ compile_network_def,project_def,projectS_def
        , projectQ_def,FLOOKUP_UPDATE]
);

val cn_ignore_let = Q.store_thm("cn_ignore_let",
  `∀p s v f vl c pl q.
    ¬MEM p pl
    ⇒ compile_network s (Let v p f vl c) pl q = compile_network s c pl q`,
  Induct_on `pl`
  \\ rw [ compile_network_def,project_def,projectS_def
        , projectQ_def,FLOOKUP_UPDATE]
);

val cn_ignore_queue_update = Q.store_thm("cn_ignore_queue_update",
  `∀p s c pl q q'.
    ¬MEM p pl
    ⇒ compile_network s c pl (q |+ (p,q')) = compile_network s c pl q`,
  Induct_on `pl`
  \\ rw [ compile_network_def,project_def,projectS_def
        , projectQ_def,FLOOKUP_UPDATE]
);

val cn_ignore_state_update = Q.store_thm("cn_ignore_state_update",
  `∀p v d s c pl q.
    ¬MEM p pl
    ⇒ compile_network (s |+ ((v,p),d)) c pl q = compile_network s c pl q`,
  Induct_on `pl`
  \\ rw [ compile_network_def,project_def,projectS_def
        , projectQ_def,FLOOKUP_UPDATE]
);

val RTC_TRANS = save_thm ("RTC_TRANS",
  RTC_RULES |> CONV_RULE FORALL_AND_CONV |> CONJUNCTS |> el 2);


(* Move to endpointPropsTheory *)
val trans_dequeue_gen = Q.store_thm("trans_dequeue_gen",
  `∀d s s' v p1 p2 e q1 q2.
    s.queue = q1 ⧺ [(p1,d)] ⧺ q2
    ∧ p1 ≠ p2 ∧ EVERY (λ(p,_). p ≠ p1) q1
    ∧ s' = s with <|queue := q1 ⧺ q2; bindings := s.bindings |+ (v,d)|>
    ⇒ trans (NEndpoint p2 s (Receive p1 v e))
            LTau
            (NEndpoint p2 s' e)`,
  rw [] >> drule trans_dequeue >> rw []
);

val trans_enqueue_choice_gen = Q.store_thm("trans_enqueue_choice_gen",
  `∀s p1 p2 e s' b.
    p1 ≠ p2
    ∧ s' = s with queue := SNOC (p1,if b then [1w] else [0w]) s.queue
    ⇒ trans (NEndpoint p2 s e)
            (LExtChoice p1 b p2)
            (NEndpoint p2 s' e)`,
  rw []
  >- (drule trans_enqueue_choice_l >> rw [])
  >- (drule trans_enqueue_choice_r >> rw [])
);

val trans_let_gen = Q.store_thm("trans_let_gen",
  `∀s s' v p f vl e.
    EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl)
    ∧ s' = (s with bindings := s.bindings |+ (v,f(MAP (THE o FLOOKUP s.bindings) vl)))
    ⇒ trans (NEndpoint p s (Let v f vl e))
             LTau
             (NEndpoint p s' e)`,
  rw [endpointSemanticsTheory.trans_let]
);

val compile_network_preservation = Q.store_thm("compile_network_preservation"
  `∀s c α τ s' c'. trans (s,c) (α,τ) (s',c')
    ⇒ ∃q. reduction^* (compile_network s  c  (procsOf c) FEMPTY)
                      (compile_network s' c' (procsOf c) q)`,
  ho_match_mp_tac trans_pairind
  \\ rw [ compile_network_def
        , procsOf_def
        , procsOf_all_distinct
        , nub'_def
        , reduction_def
        , project_def
        , FILTER_FILTER
        , FOLDL
        , fupdate_projectS]
  (* Com *)
  >- (Q.EXISTS_TAC `FEMPTY`
     \\ IMP_RES_TAC lookup_projectS
     \\ rw [projectQ_def]
     \\ MAP_EVERY Q.ABBREV_TAC [ `l = FILTER (λy. p1 ≠ y ∧ p2 ≠ y) (nub' (procsOf c'))`
                               , `s'   = s |+ ((v2,p2),d)`
                               , `s1   = projectS p1 s`
                               , `s2   = projectS p2 s`
                               , `s2'  = projectS p2 s'`
                               , `cp1  = project p1 c'`
                               , `cp2  = project p2 c'`
                               , `ns   = compile_network s' c' l FEMPTY`
                               , `s1q  = <|bindings := s1; queue := []|>`
                               , `s2q  = <|bindings := s2; queue := []|>`
                               ]
     \\ `compile_network s (Com p1 v1 p2 v2 c') l FEMPTY = ns`
        by (rw [Abbr `l`, Abbr `ns`, Abbr `s'`, MEM_FILTER
               , cn_ignore_com, cn_ignore_state_update])
     \\ ASM_REWRITE_TAC []
     \\ pop_assum (K ALL_TAC)
     \\ ho_match_mp_tac RTC_TRANS
     \\ Q.EXISTS_TAC
        `NPar  (NEndpoint p1 s1q cp1)
        (NPar  (NEndpoint p2 (s2q with queue := SNOC (p1,d) s2q.queue)
                             (Receive p1 v2 cp2)) ns)`
     \\ rw [reduction_def]
     >- (ho_match_mp_tac trans_com_l
        \\ MAP_EVERY Q.EXISTS_TAC [`p1`,`p2`,`d`]
        \\ rw []
        >- (ho_match_mp_tac trans_send
           \\ rw [Abbr `s1q`])
        >- (ho_match_mp_tac trans_par_l
           \\ ho_match_mp_tac trans_enqueue
           \\ rw []))
     >- (ho_match_mp_tac RTC_SINGLE
        \\ rw [reduction_def]
        \\ ho_match_mp_tac trans_par_r
        \\ ho_match_mp_tac trans_par_l
        \\ ho_match_mp_tac trans_dequeue_gen
        \\ MAP_EVERY Q.EXISTS_TAC [`d`,`[]`,`[]`]
        \\ rw [Abbr `s2q`, Abbr `s2`,Abbr `s'`,Abbr `s2'`,projectS_fupdate]))
  (* Sel *)
  >- (Q.EXISTS_TAC `FEMPTY |+ (p2,[(p1,if b then [1w] else [0w])])`
      \\ fs [projectQ_def,FLOOKUP_UPDATE]
      \\ MAP_EVERY Q.ABBREV_TAC [ `l  = FILTER (λy. p1 ≠ y ∧ p2 ≠ y) (nub' (procsOf c'))`
                                , `s1   = projectS p1 s`
                                , `s2   = projectS p2 s`
                                , `cp1  = project p1 c'`
                                , `cp2  = project p2 c'`
                                , `ns   = compile_network s c' l FEMPTY`
                                ]
      \\ `compile_network s (Sel p1 b p2 c') l FEMPTY = ns`
         by (rw [Abbr `l`, Abbr `ns`, MEM_FILTER, cn_ignore_sel])
      \\ `compile_network s c' l
              (FEMPTY |+ (p2,[(p1,if b then [1w] else [0w])])) = ns`
          by (rw [Abbr `l`, Abbr `ns`, MEM_FILTER, cn_ignore_queue_update])
      \\ fs []
      \\ pop_assum (K ALL_TAC)
      \\ pop_assum (K ALL_TAC)
      \\ ho_match_mp_tac RTC_SINGLE
      \\ fs [reduction_def]
      \\ ho_match_mp_tac trans_com_choice_l
      \\ MAP_EVERY Q.EXISTS_TAC [`p1`,`p2`,`b`]
      \\ fs []
      \\ CONJ_TAC
      >- (ho_match_mp_tac trans_int_choice >> rw [])
      >- (ho_match_mp_tac trans_par_l
         \\ ho_match_mp_tac trans_enqueue_choice_gen
         \\ rw []))
  (* Let *)
  >- (Q.EXISTS_TAC `FEMPTY`
     \\ fs [projectQ_def,FLOOKUP_UPDATE]
     \\ MAP_EVERY Q.ABBREV_TAC [ `l  = FILTER (λy. p ≠ y) (nub' (procsOf c'))`
                               , `s' = s |+ ((v,p),f (MAP (THE ∘ FLOOKUP s) (MAP (λv. (v,p)) vl)))`
                               , `s1   = projectS p s`
                               , `s1'  = projectS p s'`
                               , `cp1  = project p c'`
                               , `cp2  = project p c'`
                               , `ns   = compile_network s' c' l FEMPTY`
                               , `sq  = <|bindings := s1; queue := []|>`
                               , `sq'  = <|bindings := s1'; queue := []|>`
                               ]
     \\`compile_network s (Let v p f vl c') l FEMPTY = ns`
     by (rw [ Abbr `l`, Abbr `ns`, Abbr `s'`, MEM_FILTER
            , cn_ignore_let , cn_ignore_state_update])
     \\ ASM_REWRITE_TAC []
     \\ pop_assum (K ALL_TAC)
     \\ ho_match_mp_tac RTC_SINGLE
     \\ rw [reduction_def]
     \\ ho_match_mp_tac trans_par_l
     \\ ho_match_mp_tac trans_let_gen
     \\ UNABBREV_ALL_TAC
     \\ rw []
     >- (Induct_on `vl` \\ rw [lookup_projectS'])
     >- (rw [projectS_fupdate] >> rpt AP_TERM_TAC
        \\ Induct_on `vl` >> rw [lookup_projectS']))
  \\ cheat
);

val _ = export_theory ()
