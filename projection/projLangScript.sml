open preamble astBakeryTheory (* todo: shouldn't have to depend on astBakery *)

val _ = new_theory "projLang";

val _ = Datatype`
  slabel = L (* true    *)
         | R (* false   *)
         | C (* neither *)
`

val _ = Datatype`
projep = Nil
         | Send proc (varN option) slabel projep
         | Receive proc proc (varN option) projep projep
         (* | Send p v e => Send p v C e                         *)
         (* | Receive p v e => Receive p p v e e                 *)
         (* | IntChoice b p e => Send p v (if b then L else R) e *)
         (* | ExtChoice p e1 e2 => Receive p p v e1 e2           *)
         | IfThen varN projep projep
         | Let varN (datum list -> datum) (varN list) projep`

val _ = Datatype `state = <| bindings : varN |-> datum; queue : (proc # datum) list  |>`;

val _ = Datatype`
network = NNil
        | NPar network network
        | NEndpoint proc state projep
`

val _ = export_theory ()


(* If p@a *)
(* then *)
(*   a -> b [T] *)
(*   a -> c [T] *)

(*   b -> d [T] *)

(*   b -> c *)
(*   b -> d *)
(* else *)
(*   a -> c [F] *)
(*   a -> b [F] *)

(*   b -> d [F] *)

(*   c -> b *)
(*   c -> d *)



(* a *)
(* -- *)
(* if p then *)
(*    Send b L p  *)
(* else *)
(*    Send c R p *)

(* b *)
(* -- *)
(*   (*      L R |     L-case              | |      R-case    | *) *)
(*   Receive a c (Send c x C (Send d y L e)) (Receive c c v e' e') *)


(* c *)
(* -- *)
(*   (*      L R |     L-case      | |      R-case             | *) *)
(*   Receive b a (Receive b b v e e) (Send b x C (Send d y R e)) *)


(* d *)
(* -- *)
(* Receive b c x e1 e2 *)
