open preamble payloadLangTheory astTheory;


val _ = new_theory "payload_to_cakeml";


(* HELPER FUNCTIONS *)
(* Config interaction
    These functions interact with config and return useful
    CakeML expressions *)
(* -- Given name of let function, produce reference to it in module *)
Definition getLetID_def:
  getLetID conf letStr =
    Long conf.letModule (Short letStr)
End
(* -- Return maximum data in message as CakeML literal *)
Definition payload_size_def:
  payload_size conf =
    Lit(IntLit(&conf.payload_size))
End
(* -- Return required communication buffer size as CakeML literal *)
Definition buffer_size_def:
  buffer_size conf =
    Lit(IntLit(&(conf.payload_size + 1)))
End

(* Payload Helper *)
(* -- Returns the list of HOL functions used in Let statements
        in Payload endpoint code *)
Definition letfuns_def:
  (letfuns payloadLang$Nil = []) ∧
  (letfuns (Send p v n e) = letfuns e) ∧
  (letfuns (Receive p v l e) = letfuns e) ∧
  (letfuns (IfThen v e1 e2) = letfuns e1 ++ letfuns e2) ∧
  (letfuns (Let v f vl e) = f::letfuns e) ∧
  (letfuns (Letrec dn args e1) = letfuns e1) ∧
  (letfuns (Fix s e) = letfuns e) ∧
  (letfuns (FCall s v) = []) ∧
  (letfuns (Call s) = [])
End

(* CakeML Helpers
    These functions help convert HOL expressions to CakeML *)
(* -- Returns a CakeML singleton list with just the Word8 literal of
      byte 0x01. Used as part of testing representations of booleans
      in compiled code. *)
Definition w1ckV_def:
  w1ckV conf =
    Con (SOME conf.cons) [Lit (Word8 1w);Con (SOME conf.nil) []]
End
(* -- Converts datum (word8 list) to CakeML list of Word8 literals *)
Definition convDatum_def:
  (convDatum conf []      = Con (SOME conf.nil) []) ∧
  (convDatum conf (x::xs) = Con (SOME conf.cons) [Lit (Word8 x);
                                                  convDatum conf xs])
End
(* -- Converts datum list ((word8 list) list) to CakeML list of
        lists of Word8 literals *)
Definition convDatumList_def:
  (convDatumList conf []      = Con (SOME conf.nil) []) ∧
  (convDatumList conf (x::xs) = Con (SOME conf.cons) [convDatum conf x;
                                                      convDatumList conf xs])
End

(* -- Converts exp list (HOL list of CakeML AST) to CakeML list of AST *)
Definition convList_def:
  (convList conf []    = Con (SOME conf.nil) []) ∧
  (convList conf (x::xs) = Con (SOME conf.cons) [x; convList conf xs])
End

(* COMMUNICATION PRIMITIVES *)
(* Sending *)
(* -- CakeML deep embedding of pad from payloadSemantics *)
Definition padv_def:
  padv conf =
    Fun "x"
    (Let (SOME "y")
          (App Aw8alloc [buffer_size conf;Lit(Word8 0w)])
          (If (App Equality [App Opapp [Var conf.length;Var(Short "x")];payload_size conf])
           (Let NONE (App Aw8update [Var(Short "y");Lit(IntLit 0);Lit(Word8 7w)])
             (Let
               (SOME "z")
               (App Opapp [Var conf.fromList;
                           App Opapp [App Opapp [Var conf.take; Var(Short"x")];
                                      payload_size conf]])
               (Let NONE
                 (App CopyAw8Aw8 [Var(Short "z"); Lit(IntLit 0); payload_size conf;
                                  Var(Short "y"); Lit(IntLit 1)])
                 (Var(Short "y"))
               )
             )
           )
           (If (App (Opb Lt) [App Opapp [Var conf.length;Var(Short "x")];payload_size conf])
            (Let NONE (App Aw8update [Var(Short "y");Lit(IntLit 0);Lit(Word8 6w)])
              (Let (SOME "z") (App Opapp [Var conf.fromList;Var(Short"x")])
                (Let NONE
                  (App Aw8update
                       [Var(Short "y");
                        App (Opn Minus)
                            [payload_size conf;
                             App Aw8length [Var(Short "z")]];
                        Lit(Word8 1w)
                       ]
                  )
                  (Let NONE
                    (App CopyAw8Aw8
                         [Var (Short "z");
                          Lit(IntLit 0);
                          App Aw8length [Var(Short "z")];
                          Var(Short "y");
                          App (Opn Plus)
                              [Lit(IntLit 1);
                               App (Opn Minus)
                                   [payload_size conf;App Aw8length [Var(Short "z")]]
                              ]
                         ]
                    )
                    (Var (Short "y"))
                  )
                )
              )
            )
            (Let NONE (App Aw8update [Var(Short "y");Lit(IntLit 0);Lit(Word8 2w)])
             (Let
               (SOME "z")
               (App Opapp [Var conf.fromList;
                          App Opapp [App Opapp [Var conf.take; Var(Short"x")];
                                     payload_size conf]])
               (Let NONE
                 (App CopyAw8Aw8 [Var(Short "z"); Lit(IntLit 0); payload_size conf;
                                  Var(Short "y"); Lit(IntLit 1)])
                 (Var (Short "y"))
               )
             )
            )
           )
          )
    )
End

(* -- Encoding of the payloadLang Send instruction as a CakeML recursive
      function definition. Has a one-to-one correspondence between #(send) FFI
      calls and LSend labels. *)
Definition sendloop_def:
  sendloop conf dest =
   [("sendloop","x",
     Let (SOME "y")
       (App Opapp [padv conf;Var(Short "x")])
       (Let NONE
         (App (FFI "send") [Lit(StrLit dest); Var (Short "y")])
         (If
           (App (Opb Leq) [App Opapp [Var conf.length; Var(Short "x")];
                           payload_size conf]
           )
           (Con NONE [])
           (Let (SOME "x") (App Opapp [App Opapp [Var conf.drop;
                                                  Var (Short "x")];
                                       payload_size conf])
                (App Opapp [Var(Short "sendloop"); Var(Short "x")])
           )
         )
       )
    )]
End

(* Receiving *)
(* -- CakeML deep embedding of final from payloadSemantics *)
Definition finalv_def:
  finalv x =
   Log Or
       (App Equality [Lit (Word8 7w); App Aw8sub [Var(Short x); Lit(IntLit 0)]])
       (App Equality [Lit (Word8 6w); App Aw8sub [Var(Short x); Lit(IntLit 0)]])
End
(* -- CakeML deep embedding of intermediate \/ final.
      Both from payloadSemantics *)
Definition validv_def:
  validv x =
   Log Or
       (App Equality [Lit (Word8 2w); App Aw8sub [Var(Short x); Lit(IntLit 0)]])
       (finalv x)
End

(* -- CakeML recursive function definition to find the first occurence of 1 in a W8array.
      x is assumed to be in scope and point to the relevant array. *)
Definition find_one_def:
  find_one =
    [("find_one","n",
      If (App (Opb Leq) [App Aw8length [Var (Short "x")]; Var(Short "n")])
         (App Aw8length [Var (Short "x")])
         (If (App Equality [Lit (Word8 1w); App Aw8sub [Var(Short "x"); Var(Short "n")]])
             (Var (Short "n"))
             (App Opapp [Var(Short "find_one"); App (Opn Plus) [Var(Short "n"); Lit(IntLit 1)]])
          )
    )]
End

(* -- CakeML deep embedding of the unpad function. *)
(* fun unpadv x =
     if validv x then
       let val l = Aw8.length x
           val n = if Aw8.sub(x,0) = 0x7w orelse
                      Aw8.sub(x,0) = 0x2w
                   then
                      1
                   else
                     let
                       fun find_one i = ...
                     in
                       1 + find_one 1
       in
           if n = 1 + Aw8.length x then []
           else
             let fun backseg A i = if i <= n then A
                                   else backseg (Aw8.sub(x,i) :: A) (i - 1)
             in
                 backseg [] (l - 1)
             end
       end
     else []
*)

Definition backseg_code_def:
  backseg_code conf =
  If (App (Opb Leq) [Var (Short"i"); Var (Short "n")])
     (Var (Short "A"))
     (App Opapp [
         App Opapp [
             Var (Short "backseg");
             Con (SOME conf.cons) [
                 App Aw8sub [Var (Short "x");
                             Var (Short "i")];
                 Var (Short "A")
               ];
           ];
         App (Opn Minus) [Var (Short "i"); Lit (IntLit 1)]
       ])
End

Definition unpadv_def:
  unpadv conf =
   Fun "x"
   (If (validv "x")
    (Let (SOME "l") (App Aw8length [Var (Short "x")])
    (Let (SOME "n")
     (If (Log Or
             (App Equality [Lit (Word8 7w); App Aw8sub [Var(Short "x");
                                                        Lit(IntLit 0)]])
             (App Equality [Lit (Word8 2w); App Aw8sub [Var(Short "x");
                                                        Lit(IntLit 0)]]))
        (Lit(IntLit 0))
        (Letrec find_one (App Opapp [Var(Short "find_one"); Lit(IntLit 1)])))
     (If (App Equality [Var (Short "n"); Var (Short "l")])
      (Con (SOME conf.nil) [])
      (Letrec [("backseg", "A", Fun "i" (backseg_code conf))]
       (App Opapp [App Opapp [Var (Short "backseg"); Con (SOME conf.nil) []];
                  App (Opn Minus) [Var (Short "l"); Lit (IntLit 1)]])))))
   (Con (SOME conf.nil) []))
End

Definition zerobuf_code_def:
  zerobuf_code =
  If (App (Opb Lt) [Var (Short "i"); Lit (IntLit 0)])
     (Con NONE [])
     (Let NONE
      (App Aw8update [Var (Short "buff"); Var (Short "i"); Lit (Word8 0w)])
      (App Opapp [Var (Short "zerobuf");
                  App (Opn Minus) [Var (Short "i"); Lit (IntLit 1)]]))
End

(* -- Encoding of the payloadLang Receive instruction as a CakeML recursive
      function definition. *)
Definition receiveloop_def:
  receiveloop conf src =
    [("receiveloop","A",
      Let NONE (App (FFI "receive") [Lit(StrLit src); Var(Short "buff")])
        (Let (SOME "n") (App Opapp [unpadv conf;Var(Short "buff")])
          (If (finalv "buff")
            (App Opapp [Var conf.concat;
                        App Opapp [Var conf.reverse;
                                   Con (SOME conf.cons) [Var (Short "n");
                                                         Var (Short "A")]]])
            (Let NONE (Letrec [("zerobuf", "i", zerobuf_code)]
                       (App Opapp [Var (Short "zerobuf");
                                   App (Opn Minus) [
                                       App Aw8length[Var (Short "buff")];
                                       Lit (IntLit 1)]]))
             (App Opapp [
                 Var(Short "receiveloop");
                 Con(SOME conf.cons) [Var(Short "n"); Var (Short "A")]])
            )
          )
        )
     )]
End

(* COMPILATION *)
(* Adds a 'P' character to the front of names. Used to avoid Payload variables
   colliding with constant names used in emitted code *)
Definition ps2cs_def:
  ps2cs ps =
    #"P"::ps
End
(* Similarly, add an F to the front of function names *)
Definition ps2cs2_def:
  ps2cs2 ps =
    #"F"::ps
End
(* compile_endpoint conf vs e

   (Static parts of) the compilation of endoint e to CakeML.

   In particular, does not compile the functions used in let expressions.
   Instead, assumes that the i:th element of vs is a CakeML expression
   whose value refines the i:th element of letfuns(e).
   It is expected that these will be obtained by translating the letfuns.

   The compilation depends on some functions from the CakeML basis library,
   mostly for routine list operations. In order to avoid this directory
   having to depend on basis, we assume that, eg., conf.append is the name
   of a function that refines APPEND.
 *)
Definition compile_endpoint_def:
    (compile_endpoint conf vs payloadLang$Nil = Con NONE []) ∧
    (compile_endpoint conf vs (Send p v n e) =
      let vv = Var(Short (ps2cs v)) in
           (Let NONE
             (Letrec
                (sendloop conf p)
                (App Opapp [Var(Short "sendloop");
                            App Opapp [App Opapp [Var conf.drop; vv];
                            Lit(IntLit(&n))]
                ])
             )
             (compile_endpoint conf vs e)
           )
    ) ∧
    (compile_endpoint conf vs (Receive p v l e) =
      Let (SOME (ps2cs v))
          (Let (SOME "buff") (App Aw8alloc [Lit(IntLit(&(conf.payload_size + 1)));
                                            Lit(Word8 0w)])
               (Letrec
                  (receiveloop conf p)
                  (App Opapp [Var (Short "receiveloop");
                              convDatumList conf (REVERSE l)]))
          )
          (compile_endpoint conf vs e)
     ) ∧
    (compile_endpoint conf vs (IfThen v e1 e2) =
     let vn = LENGTH(letfuns e1) in
       If (App Equality [Var(Short (ps2cs v)); w1ckV conf])
          (compile_endpoint conf (TAKE vn vs) e1)
          (compile_endpoint conf (DROP vn vs) e2)) ∧
    (compile_endpoint conf (hv::vs) (payloadLang$Let v f vl e) =
     ast$Let (SOME (ps2cs v))
         (App Opapp [((ast$Var o (getLetID conf)) hv);
                     convList conf (MAP (Var o Short o ps2cs) vl)])
         (compile_endpoint conf vs e)) ∧
    (compile_endpoint conf vs (payloadLang$Letrec dn args e1) =
       ast$Letrec
         [(ps2cs2 dn,"",
           Mat (Var(Short ""))
               [(Pcon NONE (MAP (Pvar o ps2cs) args),
                 compile_endpoint conf vs e1)]
          )
         ]
         (App Opapp [Var(Short(ps2cs2 dn)); Con NONE (MAP (Var o Short o ps2cs) args)])
    ) ∧
    (compile_endpoint conf vs (payloadLang$FCall dn args) =
     App Opapp [Var(Short(ps2cs2 dn)); Con NONE (MAP (Var o Short o ps2cs) args) ]
    ) ∧
    (*** The following cases should never happen: payload_closure ***
     *** should run before  payload_to_cakeml and compile away    ***
     *** fixpoint ops.                                            ***)
    (compile_endpoint conf vs (payloadLang$Call dn) =
     Con NONE []
    ) ∧
    (compile_endpoint conf vs (payloadLang$Fix dn e1) =
     Con NONE []
    )
End

val _ = export_theory ();
