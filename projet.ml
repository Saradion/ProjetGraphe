open Dag.Dag;;

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

let print_trace t =
    let print_list l =
        begin
            Format.printf "[";
            List.iter (fun e -> Format.printf "%s " (namev e)) l;
            Format.printf "]";
        end
    in
        begin
            Format.printf "[";
            List.iter print_list t;
            Format.printf "]";
        end;;
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
type trace = (V.t list) list

let rec step r g =
    if is_empty g then
        []
    else if r = 0 then
        []
    else
        let y = sources g in
        match y with
        | []   -> failwith "Not a DAG!"
        | h::t -> match computedv h with
            | true -> (remove_vertex g h; step r g)
            | false -> (decreasev h 1.; h::(step (r-1) g));;

let ordonnanceur_multi r g =
    let rec aux r g =
        if is_empty g then
            []
        else
           let s = step r g in
           s::(aux r g) in
    aux r g;;


let decrease v res_type alpha =
    if (typeressv v) = res_type then
        decreasev v 1.
    else
        decreasev v (1./.alpha);;

let rec step_bis alpha r1 r2 g =
    if is_empty g then
        []
    else if r1 = 0 && r2 = 0 then
        []
    else
        let y = sources g in
        match y with
        | []   -> failwith "Not a DAG!"
        | h::t -> match computedv h with
            | true -> (remove_vertex g h; step_bis alpha r1 r2 g)
            | false -> 
                if r1 = 0 then
                    (decrease h 2 alpha; h::(step_bis alpha r1 (r2-1) g))
                else
                    (decrease h 1 alpha; h::(step_bis alpha (r1-1) r2 g));;

let ordonnanceur_heterogene alpha r1 r2 g =
    let rec aux alpha r1 r2 g =
        if is_empty g then
            []
        else
           let s = step_bis alpha r1 r2 g in
           s::(aux alpha r1 r2 g) in
    aux alpha r1 r2 g;;

let rec step_ter alpha r1 r2 g =
    if is_empty g then
        []
    else if r1 = 0 && r2 = 0 then
        []
    else
        let y = sources g in
        match y with
        | []   -> failwith "Not a DAG!"
        | h::t -> match computedv h with
            | true -> (remove_vertex g h; step_ter alpha r1 r2 g)
            | false -> let res_type = typeressv h in
                if (res_type = 1 && r1 != 0) || (res_type = 2 && r2 = 0) then
                    (decrease h 1 alpha; h::(step_ter alpha (r1-1) r2 g))
                else
                    (decrease h 2 alpha; h::(step_ter alpha r1 (r2-1) g));;

let ordonnanceur_heterogene_quick alpha r1 r2 g =
    let rec aux alpha r1 r2 g =
        if is_empty g then
            []
        else
           let s = step_ter alpha r1 r2 g in
           s::(aux alpha r1 r2 g) in
    aux alpha r1 r2 g;;

