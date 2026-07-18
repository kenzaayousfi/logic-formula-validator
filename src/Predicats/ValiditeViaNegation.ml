open DiagVenn
open Formule_Syllogisme

(** est_valid_premiss_conc b1 b2 teste si pour deux combinaisons booléennes de
    formules pour syllogismes b1 et b2, b1 valide b2, en utilisant la méthode de
    la conjonction avec les diagrammes inverses de la conclusion *)
let est_valid_premiss_conc' (b1 : boolCombSyllogismes) (b2 : boolCombSyllogismes) : bool =
  let alpha =
    List.sort_uniq compare
      (predicates_of_bool_comb b1 @ predicates_of_bool_comb b2)
  in
    let diags_b1 = diags_of_bool_comb alpha b1 in
      let diags_not_b2 = diags_of_bool_comb alpha (Non b2) in
        (* Validité par vacuité *)
        if diags_b1 = [] then true
        else conj_diag_list diags_b1 diags_not_b2 = []

(** temoins_invalidite_premisses_conc' b1 b2 renvoie les diagrammes de la
    conjonction des diagrammes de b1 avec la négation de b2, qui contredisent
    chaque diagramme de b2 *)
let temoins_invalidite_premisses_conc' (b1 : boolCombSyllogismes) (b2 : boolCombSyllogismes) : diagramme list =
  let alpha =
    List.sort_uniq compare
      (predicates_of_bool_comb b1 @ predicates_of_bool_comb b2)
  in
    let diags_b1 = diags_of_bool_comb alpha b1 in
      let diags_not_b2 = diags_of_bool_comb alpha (Non b2) in
        if diags_b1 = [] then []
        else conj_diag_list diags_b1 diags_not_b2

