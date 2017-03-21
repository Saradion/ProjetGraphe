open Dag;;

(********** Definitions de fonctions utilitaires **********)

(* Renvoie true si la liste l contient l'element a *)
let contains l a =
    List.exists (fun e -> a == e) l;;

(* Renvoie true si la liste l1 contient la liste l2 *)
let subset l1 l2 =
    List.for_all (contains l1) l2;;

(* Renvoie les "sources" du DAG g, c'est a dire les noeuds de g n'ayant aucun predecesseur *)
let sources g =
    fold_vertex (fun v l -> match (pred g v) with
    | [] -> l@[v]
    | _ -> l) g [] ;;

(* Renvoie la liste l1 privee des elements de l2 *)
let rec remove l e =
    match l with
    | [] -> []
    | h::t -> if (h == e) then t else (remove t e);;
(**********************************************************)



(************** Fonction de tri topologique ***************)
let tri_topologique g =
    (* On definit une fonction auxiliaire récursive qui va parcourir y *)
    let rec tri_aux g1 y z =
        (match y with
        | []   -> z
        | h::t -> 
            let z = z@[h] in
            let y = t in
            (* fonction prenant 2 liste y et z, un noeud v et un graphe et ajoutant a y *)
            (* l'ensemble des sucesseurs de v dont tous les predecesseurs sont dans z   *)
            let add_to_y g v y z = List.fold_left (fun l e -> if (subset z (pred g e)) then l@[e] else l) y (succ g v) in 
            let y = add_to_y g1 h y z in
            tri_aux g1 y z)
        in
           let y0 = sources g in
           let z0 = [] in
           tri_aux g y0 z0;;
(**********************************************************)




(************** Algorithme d'ordonnancement ***************)
type trace = (Dag.t list) list

(* Calcul d'étape : on prend la liste des étapes non terminées,
 * on regarde la première. Si on a suffisamment de ressources, on met le cout
 * courant de la tâche à 0, puis *)
let rec step r_available g l =
    match l with
    | []   -> []
    | h::t -> 
        if (r_available > (currcostv h)) then
            begin
            let r = r_available -. (currcostv h) in
            decreasev h (currcostv h);
            Format.printf "%f " r;
            h::(step r g t)
            end
        else 
            begin
            decreasev h r_available;
            [h]
            end;;

let ordonnanceur_multi r g =
    let rec ord_aux r g l =
    match l with
    | [] -> []
    | _  -> let s = (step r g l) in
            let l = (List.fold_left (fun l1 e1 -> if (computedv e1) then (remove l1 e1) else l1) l s) in
            s::(ord_aux r g l) in
    ord_aux r g (tri_topologique g);;
(**********************************************************)
