open HolKernel boolLib Parse bossLib;
open optionTheory
     relationTheory
     listTheory
     rich_listTheory;
open ffiTheory;
open payloadSemTheory
     payloadLangTheory
     payloadPropsTheory
     comms_ffi_modelTheory
     comms_ffi_consTheory;

val _ = new_theory "comms_ffi_props";

(* FUNDAMENTAL FFI STATE INVARIANTS/PROPERTIES *)
(* Process Number *)
Theorem strans_pres_pnum:
  ∀conf s1 L s2.
    strans conf s1 L s2 ⇒
      FST s1 = FST s2
Proof
  rw[Once strans_cases] >>
  simp[]
QED

(* Message Queue *)
Theorem strans_queue_pres:
  ∀conf P Q1 N1 D M Q2 N2.
    strans conf (P,Q1,N1) (ASend D M) (P,Q2,N2) ⇒
      ∀sp.
        isPREFIX (qlk Q1 sp) (qlk Q2 sp)
Proof
  Induct_on ‘strans’ >> rw[] >>
  metis_tac[IS_PREFIX_TRANS,qpush_prefix]
QED

(* Message Queue Irrelevance *)
(* -- Lemma about queue growth *)
Theorem active_trans_queue_expand:
  ∀conf c q1 n1 q2 n2.
    RTC (active_trans conf c) (q1,n1) (q2,n2) ⇒
    ∀sp.
      isPREFIX (qlk q1 sp) (qlk q2 sp)
Proof
  rw[] >>
  ‘∀s1 s2. RTC (active_trans conf c) s1 s2 ⇒
           (λ(q1,n1) (q2,n2).
              ∀sp.
                isPREFIX (qlk q1 sp) (qlk q2 sp)) s1 s2’
    suffices_by (rw[] >>
                 first_x_assum (qspecl_then [‘(q1,n1)’,‘(q2,n2)’] assume_tac) >>
                 rfs[]) >>
  ho_match_mp_tac RTC_INDUCT >>
  first_x_assum (K ALL_TAC) >>
  rw[]
  >- (PairCases_on ‘s1’ >> rw[])
  >- (rename [‘_ _ s1 s2’,‘_ s2 s3’] >>
      PairCases_on  ‘s1’ >> PairCases_on ‘s2’ >>
      PairCases_on ‘s3’ >>
      fs[active_trans_def,internal_trans_def,emit_trans_def] >>
      rw[] >>
      last_x_assum (K ALL_TAC) >>
      metis_tac[IS_PREFIX_TRANS,qpush_prefix])
QED

(* -- Helper lemmas about queue irrelevance *)
Definition qsame_def:
  qsame q1 q2 ⇔ ∀sp. qlk q1 sp = qlk q2 sp
End

(* -- -- Internal Transition *)
Theorem qsame_irrel_internal:
  ∀conf c q1 q1M N1 q2 N2.
    RTC (internal_trans conf c) (q1,N1) (q2,N2) ⇒
    qsame q1 q1M ⇒
    ∃q2M.
      RTC (internal_trans conf c) (q1M,N1) (q2M,N2) ∧
      qsame q2 q2M
Proof
  simp[qsame_def] >>
  rpt gen_tac >>
  ‘∀s1 s2.
    RTC (internal_trans conf c) s1 s2 ⇒
    (λ(q1,N1) (q2,N2).
      ∀q1M.
        (∀sp. qlk q1 sp = qlk q1M sp) ⇒
        ∃q2M.
          RTC (internal_trans conf c) (q1M,N1) (q2M,N2) ∧
          (∀sp. qlk q2 sp = qlk q2M sp)) s1 s2’
    suffices_by (rw[pairTheory.FORALL_PROD] >>
                 metis_tac[]) >>
  Induct_on ‘RTC’ >> rw[]
  >- (PairCases_on ‘s1’ >> rw[] >>
      qexists_tac ‘q1M’ >> metis_tac[RTC_REFL]) >>
  rename1 ‘internal_trans conf c s1 sI’ >>
  MAP_EVERY PairCases_on [‘s1’,‘sI’,‘s2’] >>
  fs[] >> rw[] >>
  ‘∃sI0M.
    internal_trans conf c (q1M,s11) (sI0M,sI1) ∧
    (∀sp. qlk sI0 sp = qlk sI0M sp)’
    suffices_by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SINGLE] >>
  metis_tac[internal_trans_def]
QED

(* -- -- Active Transition *)
Theorem qsame_irrel_active:
  ∀conf c q1 q1M N1 q2 N2.
    RTC (active_trans conf c) (q1,N1) (q2,N2) ⇒
    qsame q1 q1M ⇒
    ∃q2M.
      RTC (active_trans conf c) (q1M,N1) (q2M,N2) ∧
      qsame q2 q2M
Proof
  simp[qsame_def] >>
  rpt gen_tac >>
  ‘∀s1 s2.
    RTC (active_trans conf c) s1 s2 ⇒
    (λ(q1,N1) (q2,N2).
      ∀q1M.
        (∀sp. qlk q1 sp = qlk q1M sp) ⇒
        ∃q2M.
          RTC (active_trans conf c) (q1M,N1) (q2M,N2) ∧
          (∀sp. qlk q2 sp = qlk q2M sp)) s1 s2’
    suffices_by (rw[pairTheory.FORALL_PROD] >>
                 metis_tac[]) >>
  Induct_on ‘RTC’ >> rw[]
  >- (PairCases_on ‘s1’ >> rw[] >>
      qexists_tac ‘q1M’ >> metis_tac[RTC_REFL]) >>
  rename1 ‘active_trans conf c s1 sI’ >>
  MAP_EVERY PairCases_on [‘s1’,‘sI’,‘s2’] >>
  fs[] >> rw[] >>
  ‘∃sI0M.
    active_trans conf c (q1M,s11) (sI0M,sI1) ∧
    (∀sp. qlk sI0 sp = qlk sI0M sp)’
    suffices_by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SINGLE] >>
  last_x_assum assume_tac >>
  ntac 2 (last_x_assum (K ALL_TAC)) >>
  pop_assum (assume_tac o REWRITE_RULE [active_trans_def]) >>
  fs[emit_trans_def,internal_trans_def]
  >- metis_tac[active_trans_def,internal_trans_def] >>
  qexists_tac ‘qpush q1M sp d’ >>
  fs[active_trans_def,emit_trans_def] >> rw[] >>
  fs[qpush_def,qlk_def,fget_def] >>
  metis_tac[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* -- -- Input Transition *)
Theorem qsame_irrel_send:
  ∀conf c q1 q1M N1 rp d q2 N2.
    input_trans conf c (q1,N1) (rp,d) (q2,N2) ⇒
    qsame q1 q1M ⇒
    ∃q2M.
      input_trans conf c (q1M,N1) (rp,d) (q2M,N2) ∧
      qsame q2 q2M
Proof
  rw[qsame_def,input_trans_def]
QED

(* -- -- Receive Transition *)
Theorem qsame_irrel_receive:
  ∀conf c q1 q1M N1 rp d q2 N2.
    output_trans conf c (q1,N1) (sp,d) (q2,N2) ⇒
    qsame q1 q1M ⇒
    ∃q2M.
      output_trans conf c (q1M,N1) (sp,d) (q2M,N2) ∧
      qsame q2 q2M
Proof
  rw[qsame_def,output_trans_def] >>
  qexists_tac ‘q2’ >>
  rw[] >>
  last_x_assum(SUBST_ALL_TAC o GSYM) >>
  rw[finite_mapTheory.FLOOKUP_EXT,FUN_EQ_THM] >>
  rename1 ‘FLOOKUP _ x’ >>
  first_x_assum(qspec_then ‘x’ mp_tac) >>
  rw[qlk_def,fget_def,FLOOKUP_normalise_queues] >>
  rpt (BasicProvers.TOP_CASE_TAC >> fs[])
QED

(* Network Properties *)
(* -- Contained Nodes *)
Definition ffi_has_node_def:
  ffi_has_node nd (P,Q,N) =
    net_has_node N nd
End

Theorem strans_pres_nodes:
  ∀conf s0 l s1.
    strans conf s0 l s1 ⇒
      (∀nd. ffi_has_node nd s0 ⇔ ffi_has_node nd s1)
Proof
  Induct_on ‘strans’ >> rw[ffi_has_node_def] >>
  metis_tac[trans_pres_nodes]
QED

(* -- Wellformedness *)
Definition ffi_wf_def:
  ffi_wf (c,q,n) ⇔ net_wf n ∧ ¬net_has_node n c
End

Theorem strans_pres_wf:
  ∀conf s1 L s2.
    strans conf s1 L s2 ⇒
      (ffi_wf s1 ⇔ ffi_wf s2)
Proof
  Induct_on ‘strans’ >> rw[ffi_wf_def] >>
  metis_tac[trans_pres_nodes,trans_pres_wf]
QED

Theorem trans_pres_ffi_wf:
  ∀conf n L n' p q q' .
   trans conf n L n' ∧
   ffi_wf (p,q,n) ⇒
   ffi_wf (p,q',n')
Proof
  rw [ffi_wf_def]
  \\ metis_tac[trans_pres_nodes,trans_pres_wf]
QED

Theorem reduction_pres_ffi_wf:
  ∀conf n n' p q q'.
   RTC (reduction conf) n n' ∧
   ffi_wf (p,q,n) ⇒
   ffi_wf (p,q',n')
Proof
  rpt strip_tac
  \\ pop_assum mp_tac
  \\ map_every qid_spec_tac [‘q'’,‘q’,‘p’]
  \\ pop_assum mp_tac
  \\ map_every qid_spec_tac [‘n'’,‘n’]
  \\ Induct_on ‘RTC’ \\  rw[reduction_def]
  >- fs [ffi_wf_def]
  \\ metis_tac [trans_pres_ffi_wf]
QED

Theorem internal_trans_pres_wf:
  ∀conf c q1 N1 q2 N2.
    RTC (internal_trans conf c) (q1,N1) (q2,N2) ⇒
    ffi_wf (c,q1,N1) ⇒
    ffi_wf (c,q2,N2)
Proof
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac ‘RTC _ S1 S2’ >>
  MAP_EVERY qid_spec_tac [‘S1’,‘S2’] >>
  Induct_on ‘RTC’ >> rw[] >>
  rename1 ‘ffi_wf (c,SK) ⇒ ffi_wf (c,SU)’ >>
  ‘ffi_wf (c,SK)’
    suffices_by rw[] >>
  rename1 ‘internal_trans conf c SB SK’ >>
  MAP_EVERY PairCases_on [‘SB’,‘SK’] >>
  fs[internal_trans_def,ffi_wf_def] >>
  metis_tac[trans_pres_nodes,trans_pres_wf]
QED

Theorem emit_trans_pres_wf:
  ∀conf c q1 N1 q2 N2.
    RTC (emit_trans conf c) (q1,N1) (q2,N2) ⇒
    ffi_wf (c,q1,N1) ⇒
    ffi_wf (c,q2,N2)
Proof
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac ‘RTC _ S1 S2’ >>
  MAP_EVERY qid_spec_tac [‘S1’,‘S2’] >>
  Induct_on ‘RTC’ >> rw[] >>
  rename1 ‘ffi_wf (c,SK) ⇒ ffi_wf (c,SU)’ >>
  ‘ffi_wf (c,SK)’
    suffices_by rw[] >>
  rename1 ‘emit_trans conf c SB SK’ >>
  MAP_EVERY PairCases_on [‘SB’,‘SK’] >>
  fs[emit_trans_def,ffi_wf_def] >>
  metis_tac[trans_pres_nodes,trans_pres_wf]
QED

Theorem active_trans_pres_wf:
  ∀conf c q1 N1 q2 N2.
    RTC (active_trans conf c) (q1,N1) (q2,N2) ⇒
    ffi_wf (c,q1,N1) ⇒
    ffi_wf (c,q2,N2)
Proof
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac ‘RTC _ S1 S2’ >>
  MAP_EVERY qid_spec_tac [‘S1’,‘S2’] >>
  Induct_on ‘RTC’ >> rw[] >>
  rename1 ‘ffi_wf (c,SK) ⇒ ffi_wf (c,SU)’ >>
  ‘ffi_wf (c,SK)’
    suffices_by rw[] >>
  rename1 ‘active_trans conf c SB SK’ >>
  MAP_EVERY PairCases_on [‘SB’,‘SK’] >>
  fs[active_trans_def,internal_trans_def,
     emit_trans_def,ffi_wf_def] >>
  metis_tac[trans_pres_nodes,trans_pres_wf]
QED

Theorem input_trans_pres_wf:
  ∀conf c q1 N1 rp d q2 N2.
    input_trans conf c (q1,N1) (rp,d) (q2,N2) ⇒
    ffi_wf (c,q1,N1) ⇒
    ffi_wf (c,q2,N2)
Proof
  rw[input_trans_def,ffi_wf_def] >>
  metis_tac[trans_pres_nodes,trans_pres_wf]
QED

Theorem output_trans_pres_wf:
  ∀conf c q1 N1 sp d q2 N2.
    output_trans conf c (q1,N1) (sp,d) (q2,N2) ⇒
    ffi_wf (c,q1,N1) ⇒
    ffi_wf (c,q2,N2)
Proof
  rw[output_trans_def,ffi_wf_def] >>
  metis_tac[trans_pres_nodes,trans_pres_wf]
QED


(* FFI STATE COMMUNICATION PROPERTIES *)
(* Send Validity Checks *)
(* -- Destination *)
Definition valid_send_dest_def:
  valid_send_dest (dest:word8 list) ffiSt = ((FST ffiSt ≠ MAP (CHR o w2n) dest) ∧ (ffi_has_node (MAP (CHR o w2n) dest) ffiSt))
End
(* -- Call Format *)
Definition valid_send_call_format_def:
  valid_send_call_format conf dest s c bytes =
    ((s = "send") ∧ (c = dest) ∧ (LENGTH bytes = SUC conf.payload_size))
End
(* -- Event Format *)
Definition valid_send_event_format_def:
  valid_send_event_format conf dest event =
    case event of
      IO_event n d c =>
         (valid_send_call_format conf dest n d (MAP FST c) ∧
          (MAP FST c = MAP SND c))
End

(* Receive Validity Checks *)
(* -- Destination *)
Definition valid_receive_src_def:
  valid_receive_src (src:word8 list) ffiSt = ((FST ffiSt ≠ (MAP (CHR o w2n) src)) ∧ (ffi_has_node (MAP (CHR o w2n) src) ffiSt))
End
(* -- Call Format *)
Definition valid_receive_call_format_def:
  valid_receive_call_format conf src s c bytes =
    ((s = "receive") ∧ (c = src) ∧ (LENGTH bytes = SUC conf.payload_size))
End
(* -- Event Format *)
Definition valid_receive_event_format_def:
  valid_receive_event_format conf src event =
    case event of
      IO_event n d c =>
         (valid_receive_call_format conf src n d (MAP FST c))
End

(* Send Properties *)
(* -- Sufficient Sending Conditions *)
Theorem strans_send_cond:
  ∀S1 dest conf.
    valid_send_dest dest S1 ⇒
    (∀bytes. ∃S2.
      strans conf S1 (ASend (MAP (CHR o w2n) dest) bytes) S2)
Proof
  rw[] >> Cases_on ‘S1’ >> qmatch_goalsub_rename_tac ‘(P,R)’ >>
  Cases_on ‘R’  >> qmatch_goalsub_rename_tac ‘(P,Q1,N1)’ >>
  ‘∃N2. trans conf N1 (LReceive P bytes (MAP (CHR ∘ w2n) dest)) N2’
    suffices_by metis_tac[strans_rules] >>
  fs[valid_send_dest_def,ffi_has_node_def] >>
  metis_tac[trans_receive_cond]
QED
(* -- Necessary Sending Conditions *)
Theorem strans_dest_check:
  ∀S1 dest conf.
    (∃bytes S2.
      strans conf S1 (ASend (MAP (CHR ∘ w2n) dest) bytes) S2) ⇒
    valid_send_dest dest S1
Proof
  Induct_on ‘strans’ >>
  rw[valid_send_dest_def,ffi_has_node_def] >>
  metis_tac[trans_pres_nodes,trans_receive_cond]
QED


(* COMPLEX FFI STATE INVARIANTS *)
(* Basic FFI State Invariant Definition *)
Definition ffi_accepts_rel_def:
  ffi_accepts_rel stpred pred oracle =
  ∀st s conf bytes.
    stpred st.ffi_state ∧ st.oracle = oracle ∧ pred s conf bytes ⇒
    ∃ffi. st.oracle s st.ffi_state conf bytes = Oracle_return ffi bytes ∧
          stpred ffi
End

(* Basic FFI Send Invariant *)
Theorem send_invariant:
  ∀ conf l.
    ffi_accepts_rel (valid_send_dest l) (valid_send_call_format conf l) (comms_ffi_oracle conf)
Proof
  rw[valid_send_dest_def,ffi_accepts_rel_def,valid_send_call_format_def,
     comms_ffi_oracle_def,ffi_send_def] >>
  DEEP_INTRO_TAC some_intro >>
  qmatch_goalsub_abbrev_tac ‘strans _ s _’ >>
  first_x_assum (K ALL_TAC) >>
  qpat_x_assum ‘_ = comms_ffi_oracle conf’ (K ALL_TAC) >>
  rw[]
  >- (rename1 ‘strans _ s _ s2’ >>
      Cases_on ‘s’ >> Cases_on ‘s2’ >>
      metis_tac[strans_pres_pnum])
  >- (rename1 ‘strans _ s _ s2’ >>
      Cases_on ‘s’ >> Cases_on ‘s2’ >>
      metis_tac[strans_pres_nodes])
  >- metis_tac[valid_send_dest_def,strans_send_cond]
QED

val _ = export_theory ();
