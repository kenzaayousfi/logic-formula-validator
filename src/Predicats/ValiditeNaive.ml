open DiagVenn
open Formule_Syllogisme

(** complete_diags d ats renvoie la liste des extensions complètes de d en
    considérant les atomes de la liste ats pour considérer les zones à
    compléter. Par exemple, un diagramme défini par une contrainte vide sur une
    zone A pourrait être complété en considérant les zones définies par une
    liste d'atomes [A; B; C]. *)
let complete_diags (d : diagramme) (ats : string list) : diagramme list =
  (* toutes les zones possibles *)
  let zones =
    let rec all_subsets = function
      | [] -> [[]]
      | x :: xs ->
          let subs = all_subsets xs in
            subs @ List.map (fun s -> x :: s) subs
    in
      all_subsets ats
      |> List.map Predicate_set.of_list
  in
    (* zones non définies *)
    let undef_zones =
      List.filter (fun z -> not (Diag.mem z d)) zones
    in
      (* générer toutes les extensions *)
      let rec extend diag = function
        | [] -> [diag]
        | z :: zs ->
            let with_vide = extend (Diag.add z Vide diag) zs in
              let with_nonvide = extend (Diag.add z NonVide diag) zs in
                with_vide @ with_nonvide
      in
        extend d undef_zones


(** is_contradiction d1 d2 teste si les diagrammes d1 et d2 sont en
    contradiction, c'est-à-dire s'il existe une zone non-vide de d1 qui est vide
    dans d2 ou inversement *)
let is_contradiction (d1 : diagramme) (d2 : diagramme) : bool =
  Diag.exists
    (fun z v1 ->
      match Diag.find_opt z d2 with
      | Some v2 -> v1 <> v2
      | None -> false)
    d1
  ||
  Diag.exists
    (fun z v2 ->
      match Diag.find_opt z d1 with
      | Some v1 -> v1 <> v2
      | None -> false)
    d2


(** est_valid_premiss_conc b1 b2 teste si pour deux combinaisons booléennes de
    formules pour syllogismes b1 et b2, b1 valide b2*)
let est_valid_premiss_conc (b1 : boolCombSyllogismes)
    (b2 : boolCombSyllogismes) : bool =
  let alpha =
    List.sort_uniq compare
      (predicates_of_bool_comb b1 @ predicates_of_bool_comb b2)
    in
    let dps = diags_of_bool_comb alpha b1 in
      let dcs = diags_of_bool_comb alpha b2 in
        (* Validité par vacuité : aucune prémisse possible *)
        if dps = [] then true
        else
          not (
            List.exists
              (fun dp ->
                let compls = complete_diags dp alpha in
                  List.exists
                    (fun dc ->
                      List.for_all (fun d2 -> is_contradiction dc d2) dcs)
                    compls)
              dps
          )


(** temoins_invalidite_premisses_conc b1 b2 renvoie les diagrammes de la
    combinaison des prémisses b1 invalidant la conclusion b2 *)
let temoins_invalidite_premisses_conc (b1 : boolCombSyllogismes)
    (b2 : boolCombSyllogismes) : diagramme list =
  let alpha =
    List.sort_uniq compare
      (predicates_of_bool_comb b1 @ predicates_of_bool_comb b2)
  in
    let dps = diags_of_bool_comb alpha b1 in
      let dcs = diags_of_bool_comb alpha b2 in
        (* Aucun témoin si les prémisses sont impossibles *)
        if dps = [] then []
        else
          List.concat
            (List.map
              (fun dp ->
                let compls = complete_diags dp alpha in
                  List.filter
                    (fun dc -> List.for_all (fun d2 -> is_contradiction dc d2) dcs)
                    compls)
              dps)

