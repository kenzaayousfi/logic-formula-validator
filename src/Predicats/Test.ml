open DiagVenn
open Proposition.Formule
open Formule_Syllogisme
open ValiditeNaive
open ValiditeViaNegation

(* ====================================================== *)
(* Génération aléatoire de formules propositionnelles     *)
(* ====================================================== *)

let rec string_of_bool_comb = function
  | Vrai -> "True"
  | Faux -> "False"
  | Base f -> string_of_formule_syllogisme f
  | Et (b1, b2) ->
      "(" ^ string_of_bool_comb b1 ^ " ∧ " ^ string_of_bool_comb b2 ^ ")"
  | Ou (b1, b2) ->
      "(" ^ string_of_bool_comb b1 ^ " ∨ " ^ string_of_bool_comb b2 ^ ")"
  | Non b ->
      "¬(" ^ string_of_bool_comb b ^ ")"
      
let atoms = [ "A"; "B"; "C" ]

let random_atom () =
  Atome (List.nth atoms (Random.int (List.length atoms)))

let rec random_prop depth =
  if depth = 0 then
    random_atom ()
  else
    match Random.int 6 with
    | 0 -> random_atom ()
    | 1 -> Non (random_prop (depth - 1))
    | 2 -> Et (random_prop (depth - 1), random_prop (depth - 1))
    | 3 -> Ou (random_prop (depth - 1), random_prop (depth - 1))
    | 4 -> Imp (random_prop (depth - 1), random_prop (depth - 1))
    | _ -> if Random.bool () then Top else Bot

(* ====================================================== *)
(* Génération aléatoire de syllogismes                    *)
(* ====================================================== *)

let random_syllogisme depth =
  if Random.bool () then
    PourTout (random_prop depth)
  else
    IlExiste (random_prop depth)

(* ====================================================== *)
(* Outils d'affichage                                     *)
(* ====================================================== *)

let print_diagramme (d : diagramme) =
  Diag.iter
    (fun zone fill ->
      let zone_str =
        if Predicate_set.is_empty zone then "{}"
        else
          "{" ^ String.concat ", " (Predicate_set.elements zone) ^ "}"
      in
      Printf.printf "%s -> %s\n" zone_str (string_of_fill fill)
    )
    d

(* ====================================================== *)
(* Test complet (fonctionnel)                             *)
(* ====================================================== *)

let string_of_bool_logic b =
  if b then "⊤" else "⊥"

let test_complet (prem : boolCombSyllogismes) (conc : boolCombSyllogismes) : int =
  print_endline "==============================================";
  print_endline ("Prémisses  : " ^ string_of_bool_comb prem);
  print_endline ("Conclusion : " ^ string_of_bool_comb conc);

  let alpha =
    List.sort_uniq compare
      (predicates_of_bool_comb prem @ predicates_of_bool_comb conc)
  in
  print_endline ("Alphabet   : [" ^ String.concat ", " alpha ^ "]");

  let res_naif = est_valid_premiss_conc prem conc in
  let res_neg  = est_valid_premiss_conc' prem conc in

  print_endline ("Résultat Naïf     : " ^ string_of_bool_logic res_naif);
  print_endline ("Résultat Négation : " ^ string_of_bool_logic res_neg);

  let incoherent = res_naif <> res_neg in
  if incoherent then
    print_endline ">> COHÉRENCE : NON"
  else
    print_endline ">> COHÉRENCE : OK";

  if (not incoherent) && (not res_naif) then begin
    print_endline "Témoins (Contre-exemples) :";
    let witnesses = temoins_invalidite_premisses_conc prem conc in
    List.iteri
      (fun i d ->
        Printf.printf "  - Témoin %d\n" (i + 1);
        print_diagramme d
      )
      witnesses
  end;

  print_endline "";
  if incoherent then 1 else 0

(* ====================================================== *)
(* Tests aléatoires 100 % fonctionnels                    *)
(* ====================================================== *)

let random_test depth =
  let prem = Base (random_syllogisme depth) in
  let conc = Base (random_syllogisme depth) in
  test_complet prem conc

let rec random_tests n depth =
  if n = 0 then 0
  else
    let errors = random_test depth in
    errors + random_tests (n - 1) depth

let run_random_tests n depth =
  Random.self_init ();
  let total_errors = random_tests n depth in
  print_endline "--------------------------------------------";
  Printf.printf
    "FIN DES TESTS. Total d'erreurs d'incohérence : %d\n"
    total_errors
