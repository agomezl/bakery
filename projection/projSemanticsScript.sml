open preamble projLangTheory

val _ = new_theory "projSemantics";

val _ = Datatype `
 label = LSend    proc (datum option) slabel proc
       | LReceive proc proc (datum option) slabel proc
       | LTau
`


val (trans_rules,trans_ind,trans_cases) = Hol_reln `

  (* Internal Choice + Send  or Send (if t = C)*)
  (∀s v d p1 p2 e t.
    FLOOKUP s.bindings v = SOME d
    ∧ p1 ≠ p2
    ⇒ trans (NEndpoint p1 s (Send p2 (SOME v) t e)) (LSend p1 (SOME d) t p2) (NEndpoint p1 s e))

  (* Internal Choice *)
∧ (∀s p1 p2 e t.
    t ≠ C
    ∧ p1 ≠ p2
    ⇒ trans (NEndpoint p1 s (Send p2 NONE t e)) (LSend p1 NONE t p2) (NEndpoint p1 s e))

  (* Enqueue-Send-Choice-L *)
∧ (∀s d p pl pr e.
    p ≠ pl ∧ p ≠ pr ∧ pl ≠ pr
    ⇒ trans (NEndpoint p s e)
             (LReceive pl pr (SOME d) L p)
             (NEndpoint p (s with queue := SNOC (pl,d) s.queue) e))

  (* Enqueue-Send-Choice-R *)
∧ (∀s d p pl pr e.
    p ≠ pl ∧ p ≠ pr ∧ pl ≠ pr
    ⇒ trans (NEndpoint p s e)
             (LReceive pl pr (SOME d) R p)
             (NEndpoint p (s with queue := SNOC (pr,d) s.queue) e))

  (* Enqueue-Send *)
∧ (∀s d p1 p2 e.
    p1 ≠ p2
    ⇒ trans (NEndpoint p2 s e)
             (LReceive p1 p1 (SOME d) C p2)
             (NEndpoint p2 (s with queue := SNOC (p1,d) s.queue) e))

  (* Enqueue-Choice-L *)
∧ (∀s p pl pr e.
    p ≠ pl ∧ p ≠ pr
    ⇒ trans (NEndpoint p s e)
             (LReceive pl pr NONE L p)
             (NEndpoint p (s with queue := SNOC (pl,[1w]) s.queue) e))

  (* Enqueue-Choice-R *)
∧ (∀s p pl pr e.
    p ≠ pl ∧ p ≠ pr
    ⇒ trans (NEndpoint p s e)
             (LReceive pl pr NONE R p)
             (NEndpoint p2 (s with queue := SNOC (pr,[0w]) s.queue) e))

  (* Com-L(L) *)
∧ (∀n1 n2 p pl pr d n1' n2'.
    p ≠ pl ∧ p ≠ pr
    ∧ trans n1 (LSend    pl    d L p) n1'
    ∧ trans n2 (LReceive pl pr d L p) n2'
    ⇒ trans (NPar n1 n2) LTau (NPar n1' n2'))

  (* Com-L(R) *)
∧ (∀n1 n2 p pl pr d n1' n2'.
    p ≠ pl ∧ p ≠ pr
    ∧ trans n1 (LSend       pr d R p) n1'
    ∧ trans n2 (LReceive pl pr d R p) n2'
    ⇒ trans (NPar n1 n2) LTau (NPar n1' n2'))

  (* Com-L(C) *)
∧ (∀n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans n1 (LSend       p1 (SOME d) C p2) n1'
    ∧ trans n2 (LReceive p1 p1 (SOME d) C p2) n2'
    ⇒ trans (NPar n1 n2) LTau (NPar n1' n2'))

  (* Com-R(L) *)
∧ (∀n1 n2 p pl pr d n1' n2'.
    p ≠ pl ∧ p ≠ pr
    ∧ trans n1 (LReceive pl pr d L p) n1'
    ∧ trans n2 (LSend    pl    d L p) n2'
    ⇒ trans (NPar n1 n2) LTau (NPar n1' n2'))

  (* Com-R(R) *)
∧ (∀n1 n2 p pl pr d n1' n2'.
    p ≠ pl ∧ p ≠ pr
    ∧ trans n1 (LReceive pl pr d R p) n1'
    ∧ trans n2 (LSend       pr d R p) n2'
    ⇒ trans (NPar n1 n2) LTau (NPar n1' n2'))

  (* Com-R(C) *)
∧ (∀n1 n2 p1 p2 d n1' n2'.
    p1 ≠ p2
    ∧ trans n1 (LReceive p1 p1 (SOME d) C p2) n1'
    ∧ trans n2 (LSend       p1 (SOME d) C p2) n2'
    ⇒ trans (NPar n1 n2) LTau (NPar n1' n2'))

  (* Dequeue-L *)
∧ (∀s v p pl pr e1 e2 q1 q2.
    s.queue = q1 ++ [(pl,d)] ++ q2
    ∧ p ≠ pl ∧ p ≠ pr ∧ pl ≠ pr
    ∧ EVERY (λ(p,_). p ≠ pr ∧ p ≠ pl) q1
    ⇒ trans (NEndpoint p2 s (Receive pl pr (SOME v) e1 e2))
             LTau
             (NEndpoint p2 (s with <|queue := q1 ++ q2;
                                     bindings := s.bindings |+ (v,d)|>) e1))

  (* Dequeue-R *)
∧ (∀s v p pl pr e1 e2 q1 q2.
    s.queue = q1 ++ [(pr,d)] ++ q2
    ∧ p ≠ pl ∧ p ≠ pr ∧ pl ≠ pr
    ∧ EVERY (λ(p,_). p ≠ pr ∧ p ≠ pl) q1
    ⇒ trans (NEndpoint p2 s (Receive pl pr (SOME v) e1 e2))
             LTau
             (NEndpoint p2 (s with <|queue := q1 ++ q2;
                                     bindings := s.bindings |+ (v,d)|>) e2))

  (* ExtChoice-L *)
∧ (∀s p pl pr e1 e2 q1 q2.
    s.queue = q1 ++ [(pl,[1w])] ++ q2
    ∧ p ≠ pl ∧ p ≠ pr
    ∧ EVERY (λ(p,_). p ≠ pl) q1
    ⇒ trans (NEndpoint p s (Receive pl pr NONE e1 e2))
             LTau
             (NEndpoint p (s with queue := q1 ++ q2) e1))

  (* ExtChoice-R *)
∧ (∀s p pl pr e1 e2 q1 q2.
    s.queue = q1 ++ [(pr,[0w])] ++ q2
    ∧ p ≠ pl ∧ p ≠ pr
    ∧ EVERY (λ(p,_). p ≠ pr) q1
    ⇒ trans (NEndpoint p s (Receive pl pr NONE e1 e2))
             LTau
             (NEndpoint p (s with queue := q1 ++ q2) e2))

  (* If-L *)
∧ (∀s v p e1 e2.
    FLOOKUP s.bindings v = SOME [1w]
    ⇒ trans (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e1))

  (* If-R *)
∧ (∀s v p e1 e2 w.
    FLOOKUP s.bindings v = SOME w ∧ w ≠ [1w]
    ⇒ trans (NEndpoint p s (IfThen v e1 e2))
             LTau
             (NEndpoint p s e2))

  (* Let *)
∧ (∀s v p f vl e.
    EVERY IS_SOME (MAP (FLOOKUP s.bindings) vl)
    ⇒ trans (NEndpoint p s (Let v f vl e))
             LTau
             (NEndpoint p (s with bindings := s.bindings |+ (v,f(MAP (THE o FLOOKUP s.bindings) vl))) e))

  (* Par-L *)
∧ (∀n1 n1' n2 alpha.
    trans n1 alpha n1'
    ⇒ trans (NPar n1 n2)
             alpha
             (NPar n1' n2))

  (* Par-R *)
∧ (∀n1 n2 n2' alpha.
    trans n2 alpha n2'
    ⇒ trans (NPar n1 n2)
             alpha
             (NPar n1 n2'))
`

val _ = zip ["trans_int_choice_send","trans_int_choice",
             "enqueue_send_choice_l","enqueue_send_choice_r",
             "enqueue_send","enqueue_choice_l","enqueue_choice_r",
             "trans_com_l_l","trans_com_l_r","trans_com_l_c",
             "trans_com_r_l","trans_com_r_r","trans_com_r_c",
             "trans_dequeue_l","trans_dequeue_r",
             "trans_ext_choice_l","trans_ext_choice_r",
              "trans_if_true","trans_if_false",
              "trans_let",
              "trans_par_l","trans_par_r"]
            (CONJUNCTS trans_rules) |> map save_thm;

val reduction_def = Define `
  reduction p q = trans p LTau q`

val _ = export_theory ()
