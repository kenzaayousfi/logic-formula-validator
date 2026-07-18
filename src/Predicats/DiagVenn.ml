open Formule_Syllogisme
(* open Formule_Log_Prop *)

module Predicate_set = Set.Make (String)
(** Module des ensembles de prédicats représentés par des chaines de caractères *)

(** Type des remplissages possibles d'un diagramme de Venn *)
type fill = Vide | NonVide

module Diag = Map.Make (Predicate_set)
(** Module des Maps dont les clés sont des ensembles de chaines de caractères *)

type diagramme = fill Diag.t
(** Type des diagrammes de Venn *)

let string_of_fill = function
  | Vide -> "Vide"
  | NonVide -> "NonVide"

(** string_of_diag d : conversion d'un diagramme d en une chaine de caractères *)
let string_of_diag (d : diagramme) : string =
  let zone_to_string z =
    let elems = Predicate_set.elements z in
      if elems = [] then "∅" else String.concat "," elems
        in
          let items =
            Diag.bindings d
            |> List.map (fun (zone, fill) ->
                  Printf.sprintf "[%s ↦ %s]" (zone_to_string zone) (string_of_fill fill))
          in
          "{ " ^ String.concat "; " items ^ " }"

(* -------------------------------------------------------------------------- *)
(* Extraction des prédicats : on ne manipule pas 'formule' en interface,
   seulement formule_syllogisme. *)
let rec predicates_of_prop_formule (f : Proposition.Formule.formule) : string list =
  match f with
  | Atome p -> [ p ]
  | Top | Bot -> []
  | Non g -> predicates_of_prop_formule g
  | Et (g1, g2) | Ou (g1, g2) | Imp (g1, g2) -> predicates_of_prop_formule g1 @ predicates_of_prop_formule g2

(* Les quantificateurs ne créent pas de nouveaux prédicats.*)
let predicates_of_formule_syll : formule_syllogisme -> string list = function
  | PourTout g | IlExiste g -> predicates_of_prop_formule g

(* -------------------------------------------------------------------------- *)
(* Satisfaction d'une zone *)

(* eval φ sur une zone : true si la zone satisfait φ *)
let rec zone_satisfies (zone : Predicate_set.t) (f : Proposition.Formule.formule) : bool =
  match f with
  | Atome p -> Predicate_set.mem p zone
  | Top -> true
  | Bot -> false
  | Non g -> not (zone_satisfies zone g)
  | Et (g1, g2) -> zone_satisfies zone g1 && zone_satisfies zone g2
  | Ou (g1, g2) -> zone_satisfies zone g1 || zone_satisfies zone g2
  | Imp (g1, g2) -> (not (zone_satisfies zone g1)) || zone_satisfies zone g2

(* -------------------------------------------------------------------------- *)
(* Génération des zones de toutes les parties d’une liste *)
let all_subsets (lst : 'a list) : 'a list list =
  let rec aux acc = function
    | [] -> acc
    | x :: xs ->
        let with_x = List.map (fun s -> x :: s) acc in
        aux (acc @ with_x) xs
  in
    aux [ [] ] lst

(* -------------------------------------------------------------------------- *)
(* Construction des diagrammes pour une formule de syllogisme *)

(** diag_from_formule alpha f : construit la liste des diagrammes de Venn associés
    à la formule f sur les prédicats issus de f ou de alpha.
    IMPORTANT : diagrammes PARTIELS : une zone indéfinie = absente de la map. *)
let diag_from_formule (alpha : string list) (f : formule_syllogisme) : diagramme list =
  let preds = List.sort_uniq compare (alpha @ predicates_of_formule_syll f) in

  let zones =
    all_subsets preds
    |> List.map (fun lst ->
           List.fold_left (fun s p -> Predicate_set.add p s) Predicate_set.empty lst)
  in
    match f with
    | PourTout phi ->
        let diag = 
          List.fold_left (fun d zone -> if zone_satisfies zone phi then d else Diag.add zone Vide d) Diag.empty zones 
        in 
          [ diag ]
    | IlExiste phi ->
        let compatibles = List.filter (fun z -> zone_satisfies z phi) zones 
        in
          List.map (fun chosen_zone -> Diag.add chosen_zone NonVide Diag.empty) compatibles


(** conj_diag d1 d2 : Calcule la combinaison/conjonction de deux diagrammes,
    renvoyant None si incompatibilité *)
let conj_diag (d1 : diagramme) (d2 : diagramme) : diagramme option =
  Diag.fold
    (fun cle valeur res ->
      match res with
      | None -> None
      | Some diagrame -> (
          match Diag.find_opt cle d1 with
          | None -> Some (Diag.add cle valeur diagrame)
          | Some v when v = valeur -> res
          | _ -> None))
    d2 (Some d1)


(** est_compatible_diag_diag dp dc : teste si le diagramme dp d'une prémisse est
    compatible avec le diagramme dc d'une conclusion *)

let est_compatible_diag_diag (d : diagramme) (d' : diagramme) : bool =
  Diag.for_all
    (fun zone v' ->
      match Diag.find_opt zone d with
      | None -> true
      | Some v -> v = v')
    d'

(** est_compatible_diag_list dp dcs : teste si un diagramme dp d'une prémisse
    est compatible avec un des diagrammes de la liste dcs, diagrammes issus
    d'une conclusion *)
let est_compatible_diag_list (dp : diagramme) (dcs : diagramme list) : bool =
  List.exists (fun d -> est_compatible_diag_diag dp d) dcs

(** est_compatible_list_list dps dcs : teste si chacun des diagrammes de dps,
    diagrammes issus de prémisses, est compatible avec au moins un des
    diagrammes de dcs, diagrammes issus d'une conclusion *)
let est_compatible_list_list (dps : diagramme list) (dcs : diagramme list) : bool =
  List.for_all (fun dp -> est_compatible_diag_list dp dcs) dps

(** construit les diagrammes globaux des prémisses 
    et équivalente à une conjonction logique *)
let rec combiner_listes (l : diagramme list list) : diagramme list =
  match l with
  | [] -> [ Diag.empty ]
  | ds :: q ->
      let rest = combiner_listes q in
        List.concat
          (List.map
            (fun d -> List.filter_map (fun r -> conj_diag d r) rest)
            ds)

(** est_compatible_premisses_conc ps c : teste si une liste de prémisses ps est
    compatible avec une conclusion c *)
let est_compatible_premisses_conc (ps : formule_syllogisme list) (c : formule_syllogisme) : bool =
  let preds =
    List.sort_uniq compare
      (List.concat (List.map predicates_of_formule_syll ps) @ predicates_of_formule_syll c)
  in
    let diag_premisses_lists = List.map (fun p -> diag_from_formule preds p) ps 
    in
      let diag_premisses = combiner_listes diag_premisses_lists 
      in
        let diag_conclusion = diag_from_formule preds c 
        in
          est_compatible_list_list diag_premisses diag_conclusion


(** temoin_incompatibilite_premisses_conc_opt ps c : renvoie un diagramme de la
    combinaison des prémisses ps incompatible avec la conclusion c s'il existe,
    None sinon *)
let temoin_incompatibilite_premisses_conc_opt (ps : formule_syllogisme list) (c : formule_syllogisme) : diagramme option =
  let preds =
    List.sort_uniq compare
      (List.concat (List.map predicates_of_formule_syll ps) @ predicates_of_formule_syll c)
  in
    let diag_premisses_lists = List.map (fun p -> diag_from_formule preds p) ps 
    in
      let diag_conclusion = diag_from_formule preds c 
      in
        let combinaisons = combiner_listes diag_premisses_lists 
        in
          List.find_opt (fun dp -> not (est_compatible_diag_list dp diag_conclusion)) combinaisons


(** temoins_incompatibilite_premisses_conc ps c : renvoie les diagrammes de la
    combinaison des prémisses ps incompatibles avec la conclusion c *)
let temoins_incompatibilite_premisses_conc (ps : formule_syllogisme list) (c : formule_syllogisme) : diagramme list =
  let preds =
    List.sort_uniq compare
      (List.concat (List.map predicates_of_formule_syll ps) @ predicates_of_formule_syll c)
  in
    let diag_premisses_lists = List.map (fun p -> diag_from_formule preds p) ps 
    in
      let diag_conclusion = diag_from_formule preds c 
      in
        let combinaisons = combiner_listes diag_premisses_lists 
        in
          List.filter (fun dp -> not (est_compatible_diag_list dp diag_conclusion)) combinaisons


(* ***** Ajouts pour le projet ***** *)

(** negate_diag d renvoie la négation du diagramme d*)
let negate_diag (d : diagramme) : diagramme list =
  Diag.fold
    (fun zone f acc ->
      let inverse =
        match f with
        | Vide -> NonVide
        | NonVide -> Vide
      in
      Diag.add zone inverse Diag.empty :: acc)
    d
    []

(** conj_diag_list ds1 ds2 renvoie la conjonction de deux listes de diagrammes
    ds1 et ds2 *)
let conj_diag_list (ds1 : diagramme list) (ds2 : diagramme list) : diagramme list =
  List.concat
    (List.map
       (fun d1 -> List.filter_map (fun d2 -> conj_diag d1 d2) ds2)
       ds1)

(** negate_diag_list ds renvoie la négation de la liste de diagrammes ds *)
let negate_diag_list (ds : diagramme list) : diagramme list =
  match ds with
  | [] -> []
  | _ ->
      List.fold_left
        (fun acc d -> conj_diag_list acc (negate_diag d))
        [Diag.empty]
        ds

(** disj_of_diag_list ds1 ds2 renvoie la disjonction de deux listes de
    diagrammes ds1 et ds2 *)
let disj_of_diag_list (ds1 : diagramme list) (ds2 : diagramme list) : diagramme list = ds1 @ ds2

(** diags_of_bool_comb alpha b renvoie la liste des diagrammes associés à la
    combinaison booléenne b de formules pour syllogismes, sur les prédicats
    issus de b ou de alpha *)
let rec diags_of_bool_comb (alpha : string list) (b : boolCombSyllogismes) : diagramme list =
  match b with
  | Vrai -> [ Diag.empty ]
  | Faux -> []
  | Base f -> diag_from_formule alpha f
  | Et (b1, b2) -> conj_diag_list (diags_of_bool_comb alpha b1) (diags_of_bool_comb alpha b2)
  | Ou (b1, b2) -> disj_of_diag_list (diags_of_bool_comb alpha b1) (diags_of_bool_comb alpha b2)
  | Non b1 ->
    let ds = diags_of_bool_comb alpha b1 in
      if ds = [] then
        [Diag.empty]      
      else
        negate_diag_list ds

(** renvoie la liste des prédicats apparaissant dans
    une combinaison booléenne b de formules pour syllogismes.
    La liste contient tous les prédicats présents dans les formules de base de b.
    Les constantes Vrai et Faux ne contiennent aucun prédicat. *) 
let rec predicates_of_bool_comb (b : boolCombSyllogismes) : string list =
  match b with
  | Vrai | Faux -> []
  | Base f -> predicates_of_formule_syll f
  | Et (b1, b2)
  | Ou (b1, b2) -> predicates_of_bool_comb b1 @ predicates_of_bool_comb b2
  | Non b1 -> predicates_of_bool_comb b1