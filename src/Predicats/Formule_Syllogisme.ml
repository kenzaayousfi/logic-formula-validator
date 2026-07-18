open Proposition.Formule

(** Type des formules utilisées pour les syllogismes *)
type formule_syllogisme = PourTout of formule | IlExiste of formule

(** string_of_formule_log_prop_var s f : conversion d'une formule f en chaîne de
    caractères, en les représentant comme des prédicats unaires appliqués sur
    des occurrences de la variable s. *)
let rec string_of_formule_log_prop_var (s : string) (f : formule) : string =
  match f with
  | Atome p -> p ^ "(" ^ s ^ ")"
  | Top -> "⊤"
  | Bot -> "⊥"
  | Non g -> "¬" ^ string_of_formule_log_prop_var s g
  | Et (f1, f2) -> "(" ^ string_of_formule_log_prop_var s f1 ^ " ∧ " ^ string_of_formule_log_prop_var s f2 ^ ")"
  | Ou (f1, f2) -> "(" ^ string_of_formule_log_prop_var s f1 ^ " ∨ " ^ string_of_formule_log_prop_var s f2 ^ ")"
  | Imp (f1, f2) -> "(" ^ string_of_formule_log_prop_var s f1 ^ " → " ^ string_of_formule_log_prop_var s f2 ^ ")"

(** string_of_formule_syllogisme f : conversion d'une formule f en chaîne de
    caractères, en considérant des prédicats unaires appliqués sur des
    occurrences de la variable s. *)
let string_of_formule_syllogisme ( f : formule_syllogisme) : string =
  let variable = "x" in
    match f with
    | PourTout p -> "∀" ^ variable ^ " " ^ string_of_formule_log_prop_var variable p
    | IlExiste p -> "∃" ^ variable ^ " " ^ string_of_formule_log_prop_var variable p
      
(** Type des combinaisons booléennes pour les syllogismes *)
type boolCombSyllogismes =
  | Vrai
  | Faux
  | Base of formule_syllogisme
  | Et of boolCombSyllogismes * boolCombSyllogismes
  | Ou of boolCombSyllogismes * boolCombSyllogismes
  | Non of boolCombSyllogismes
