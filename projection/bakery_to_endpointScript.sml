open preamble semBakeryTheory endpointLangTheory

val _ = new_theory "bakery_to_endpoint";

val split_sel_def = Define `
   (split_sel proc (Sel p1 b p2 c) =
    if proc = p2 then
      SOME(b,c)
    else
      split_sel proc c)
/\ (split_sel proc _ = NONE)`

val project_def = Define `
   (project proc Nil = Nil)
/\ (project proc (Com p1 v1 p2 v2 c) =
    if proc = p1 /\ proc = p2 then
      Let v2 HD [v1] (project proc c) (*TODO: does it make sense to compile self-communication to let? *)
    else if proc = p1 then
      Send p2 v1 (project proc c)
    else if proc = p2 then
      Receive p1 v2 (project proc c)
    else
      project proc c)
/\ (project proc (Let v p1 f vs c) =
    if proc = p1 then
      Let v f vs (project proc c)
    else
      project proc c)
/\ (project proc (IfThen v p1 c1 c2) =
    if proc = p1 then
      IfThen v (project proc c1) (project proc c2)
    else
      case (split_sel proc c1,split_sel proc c2) of
        | (SOME(T,c1'),SOME(F,c2')) =>
            ExtChoice p1 (project proc c1) (project proc c2)
        | (NONE,NONE) => project proc c1
        | _ => Nil (* shouldn't happen *)
   )
/\ (project proc (Sel p1 b p2 c) =
    if proc = p1 then
      IntChoice b p2 (project proc c)
    else
      project proc c)`

(* Project a global state `(proc,var) |-> val` into a single process
   state `var |-> val`
*)
val projectS_def = Define`
  projectS p s =
    let state_of_p = FILTER (λx. SND (FST x) = p) (fmap_to_alist s);
        v_to_vl    = MAP (λx. (FST (FST x), SND x)) state_of_p;
    in alist_to_fmap v_to_vl
`;

(*Crates a network of projections from a choreography *)
val compile_network_def = Define`
  compile_network s c []      = NNil
∧ compile_network s c (p::lp) =
       let mkState = (λp. <| bindings := (projectS p s); queue := [] |>);
           mkEP    = (λp. project p c);
           mkNEP   = (λp. NEndpoint p (mkState p) (mkEP p))
       in NPar (mkNEP p) (compile_network s c lp)`
;

val _ = export_theory ()
