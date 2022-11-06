open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)
 (* cherche si -l existe dans clause*)
 let rec simp_aux2 l clause = match clause with
  | []->[]
  | x::[]-> if (x = ((-1) * l)) then [] else x::[]
  | x::list -> if (x = ((-1) * l)) then (simp_aux2 l list) else x::(simp_aux2 l list);;
 
 
(* cherche si l existe dans clause*)
let rec simp_aux1 l clause = match clause with
  | []->[]
  | x::[]-> if x=l then [] else x::[]
  | x::list -> if x=l then [] else simp_aux1 l list;;
 
(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)

(*cette fonction de simplifier utilise de fonction auxiliair simp_aux1 qui prends 
     une clause et n léttiral l et test si le le littéral l existe dans clause alors 
     en supprime cette clause sinon on ne fait rien et pour la 2eme fonction auxiliaire 
     simp_aux2 elle cherche si -il existe alors on supprime -l et on garde le reste de la clause *)
let rec simplifie l clauses = match clauses with
  | []->[]
  | a::[]-> if (simp_aux1 l a) = [] then [] else (simp_aux2 l a)::[]
  | x::list -> if (simp_aux1 l x) = [] then (simplifie l list) else (simp_aux2 l x)::(simplifie l list);;


(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche;;



(* solveur dpll récursif *)

    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let rec unitaire clauses = match clauses with  
  (* ici dans le 1er cas on retourne 0 pour qu'on puisse verifier 
     simplement si on a reussi à trouver un littéral unitaire ou 
     non en executant la fonction solveur_dpll_rec 
     et pour ne pas lever une exeption dans la fonction solveur_dpll_rec *)       
  |[] -> 0(* failwith "Not_found" *)
  |x :: reste ->  if List.length x = 1 then List.hd x else unitaire reste ;;
  


(* merge_list : 'a list  -> 'a list -> 'a list
    ajoute à une liste "l" tous les éléments d'une autre liste "li" 
    qui n'y figure pas sans répétition  *)
let rec merge_list l li = match li with 
|[]-> l
|x::li-> if List.mem x l then merge_list l li else merge_list (x::l) li ;;


(* transformer : 'a list list -> 'a list
    transforme une liste de liste "clauses " a une liste "l" qui contient tout les éléments 
    des sous-listes de clauses sans répétition *)
let rec transformer l clauses = match clauses with 
 |[]-> l
 |x::clauses -> transformer (merge_list l x) clauses;;


(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses = 
  (* "l" est une liste qui contient tous les littéraux de clauses sans répétion *)
  let l = transformer [] clauses in
  (* pur fait appel à une fonction local pur_intere, comme on a la liste "l" 
     qui contient tous les littéraux de clauses il suffit de verifier pour chaque élément "x" de la liste "l" :
      - si la liste "l" ne contient "-x" alors retourner x  (i.e x est pur)  
      - sinon verifier l'élément suivant *)
  let rec pur_interne list = match list with
  (* ici dans le 1er cas on retourne 0 pour qu'on puisse verifier 
     simplement si on a reussi à trouver un littéral pur ou non en executant la fonction solveur_dpll_rec 
     et pour ne pas lever une exeption dans la fonction solveur_dpll_rec *)  
  |[] -> 0 (*failwith "pas de litteral pur"*)
  |x::r -> if List.mem (-x) l then pur_interne r else x
in pur_interne l;;

 
  
 


let rec solveur_dpll_rec clauses interpretation =  
  (* on verifier si la formule ne contient pas la clause vide *)
  if mem [] clauses then None 
  else
   begin
     let u = unitaire clauses in
     (* on verifie si la formule contient un  littéral unitaire. 
        la fonction unitaire retourne "0" si la formule ne contient 
        pas un littéral unitaire *)
     if (u!=0) then solveur_dpll_rec (simplifie u clauses) (u::interpretation)
     else
     begin
       let p = pur clauses in
       (* on verifie si la formule contient un  littéral pur.
          la fonction pur retourne "0" si la formule ne contient 
          pas un littéral pur *)
       if(p!=0) then solveur_dpll_rec (simplifie p clauses) (p::interpretation)
       else solveur_split clauses interpretation
     end  
   end;;
  
 (* pour tester avec les test donnés ci-dessus il suffit d'executer 
    les lignes ci-dessous en les enlevant du commentaire *) 

(*print_string("\nTest de : exemple_7_2 = [[1;-1;-3];[-2;3];[-2]] \n\n");;
print_modele(solveur_dpll_rec exemple_7_2 []);;
print_string("\n-*-*-*-*-*-*-*-*-*-*-*-*-*-**-*-*-*-**-*-**-*-*-\n ");;
print_string("Test de : exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]\n\n");;
print_modele(solveur_dpll_rec exemple_7_8 []);;
print_string("\n*-*-*-*-*-*-*-*-*-*-*-*-*-**-*-*-*-**-*-**-*-*-\n ");;
print_string("Test de : systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]\n\n");;
print_modele(solveur_dpll_rec systeme []);;
print_string("\n*-*-*-*-*-*-*-*-*-*-*-*-*-**-*-*-*-**-*-**-*-*-\n ");;
print_string("Test de : coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]\n\n");;
print_modele(solveur_dpll_rec coloriage []);;*)


let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
