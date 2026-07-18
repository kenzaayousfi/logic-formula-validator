(** Le module Formule contient les types et définitions de base permettant la
    manipulation des formules de la logique propositionnelle. *)

(** Type des formules de la logique propositionnelle, avec des string comme
    atomes. *)
type formule =
  | Bot
  | Top
  | Atome of string
  | Imp of (formule * formule)
  | Ou of (formule * formule)
  | Et of (formule * formule)
  | Non of formule


(* ----------------- Exercice 1 : Hauteur ----------------- *)

(** Calcule la hauteur de l'arbre syntaxique d'une formule. *)
let rec hauteur = function
  | Bot | Top | Atome _ -> 0
  | Non f -> 1 + hauteur f
  | Et (f, g)
  | Ou (f, g)
  | Imp (f, g) ->
      1 + max (hauteur f) (hauteur g)


(* ----------------- Exercice 2 : Représentation en chaîne de caractères ----------------- *)

(** Conversion d'une formule en chaîne de caractères. *)
let rec string_of_formule : formule -> string = function
  | Atome s -> s
  | Et (f,g)-> String.concat "" ["(";string_of_formule f; "∧"; string_of_formule g;")"]
  | Bot-> "⊥"
  | Top -> "⊤"
  | Ou (f,g)-> String.concat "" ["(";string_of_formule f; "∨"; string_of_formule g; ")"]
  | Imp(f,g)-> String.concat "" ["(";string_of_formule f; "⇒"; string_of_formule g; ")"]
  | Non (f)-> String.concat "" ["("; "¬"; string_of_formule f;")"]


(* ----------------- Exercice 3 : Conversion depuis une liste ----------------- *)

(** Transforme une liste de formules [[f1; f2; ... ; fl]] en la formule
    [f1 ∧ f2 ∧ ... ∧ fl] en considérant les éléments suivants : Si un des [fi]
    vaut [Bot], renvoie [Bot]. Si un des [fi] vaut [Top], il n'apparait pas dans
    le résultat. Si tous les [fi] valent [Top], renvoie [Top]. *)
let rec conj_of_list (f : formule list) : formule =
  match f with
  | [] -> Top                         
  | Bot :: _ -> Bot                   
  | Top :: q -> conj_of_list q        
  | x :: [] -> x                      
  | x :: q -> Et(x, conj_of_list q)  

(** Transforme une liste de formules [[f1; f2; ... ; fl]] en la formule
    [f1 ∨ f2 ∨ ... ∨ fl] en considérant les éléments suivants : Si un des [fi]
    vaut [Top], renvoie [Top]. Si un des [fi] vaut [Bot], il n'apparait pas dans
    le résultat. Si tous les [fi] valent [Bot], renvoie [Bot]. *)
let rec disj_of_list = function
  | [] -> Bot
  | Top :: _ -> Top
  | Bot :: q -> disj_of_list q
  | f :: [] -> f
  | f :: q -> Ou(f, disj_of_list q)


(** --- Exercice 4 : Fonctions d'évaluation ------- *)

(** Type des interprétations. *)
type interpretation = string -> bool

(** Évalue une formule en fonction d'une interprétation. *)
let rec eval (i: interpretation) (f : formule) : bool = match f with
  | Bot -> false
  | Top -> true
  | Atome s -> i s 
  | Non(f) -> not (eval i f)
  | Ou(f,g)-> eval i f || eval i g
  | Et(f,g) -> eval i f && eval i g
  | Imp(f,g) -> not (eval i f) || eval i g 


(** --- Exercice 5 : Tests de satisfaisabilité ------- *)

(** Transforme une liste de string en une interprétation. *)
let interpretation_of_list (l: string list) : interpretation =
  function s -> List.mem s l 

(** Calcule la liste de toutes les sous-listes d'une liste donnée. *)
let all_sublists (lst : 'a list) : 'a list list =
  List.fold_right (fun x acc -> acc @ List.map (fun sublist -> x :: sublist) acc) lst [[]]

(** Calcule toutes les interprétations pour une liste d'atomes donnée. *)
let all_interpretations (ats : string list) : interpretation list =
  let sublists = all_sublists ats in
    List.map interpretation_of_list sublists

(** Calcule la liste (triée et sans doublon) des atomes d'une formule.*)
let atomes (f : formule) : string list =
  let rec collect acc = function
    | Bot | Top -> acc
    | Atome s -> s :: acc
    | Non g -> collect acc g
    | Et (f1, f2)
    | Ou (f1, f2)
    | Imp (f1, f2) -> collect (collect acc f1) f2
  in
  List.sort_uniq compare (collect [] f)

(** Détermine si une formule est satisfaisable. *)
let est_satisfaisable (f : formule) : bool =
  let ats = atomes f in
    let interps = all_interpretations ats in
      List.exists (fun i -> eval i f) interps

(** Renvoie un témoin de la satisfaisabilité d'une formule, s'il en existe. *)
let ex_sat (f : formule) : interpretation option =
  let ats = atomes f in
    let interps = all_interpretations ats in
      let rec aux = function
        | [] -> None
        | i :: q -> if eval i f then Some i else aux q
      in
        aux interps

(** Détermine si une formule est une tautologie. *)
let est_tautologie (f : formule) : bool =
  let ats = atomes f in
    let interps = all_interpretations ats in
      List.for_all (fun i -> eval i f) interps

(** Détermine si une formule est une contradiction. *)
let est_contradiction (f : formule) : bool = not (est_satisfaisable f)

(** Détermine si une formule est contingente. *)
let est_contingente (f : formule) : bool = est_satisfaisable f && not (est_tautologie f)

  
(** ----------------- Exercice 8 : Tables de vérité ----------------- *)

type ligne = string list * bool
(** Type d'une ligne d'une table de vérité. *)

type table = ligne list
(** Type d'une table de vérité. *)

(** Calcule la table de vérité associée à une formule. *)
let table_of_formule (f : formule) : table =
  let ats = atomes f in
    let sublists = all_sublists ats in
      List.map
        (fun vrais ->
          let i = interpretation_of_list vrais in
            (vrais, eval i f)) sublists
