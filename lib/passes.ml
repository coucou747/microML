type ('acc, 'from, 'target, 'prev, 'final ) t = {
    init : 'acc;
    process :  'acc -> 'from -> 'acc * 'target;
    final : 'acc -> 'prev -> 'final;
  }

let nofinal = fun _ a -> a

(* le saut de ligne final est ajouté par handle_option, hors de la boîte *)
let print_pass pp = {init = (); final = nofinal; process = fun () value -> Format.printf "%a" pp value; (), value;}

let no_pass = {init = (); final = nofinal; process = fun () value -> (), value}

let handle_option name access pass =
  if access name then
    { init = pass.init; final = pass.final;
      process = fun acc v ->
                (* une seule boîte, ouverte après le nom de la passe et refermée après
                   l'élément : l'indentation suit le nom sans toucher à la marge *)
                Format.printf "%s@[<v>" name;
                let out = pass.process acc v in
                Format.printf "@]@\n@?";
                out}
  else no_pass

let handle_exception msg = Format.eprintf "%s@\n@\n" msg

let may_die : ('acc, 'from, 'target, 'prev, 'final ) t ->
              ('acc option, 'from, 'target option, 'prev, 'final option) t = fun pass ->
  {init = Some pass.init;
   final = (fun acc prev -> Option.map (fun acc -> pass.final acc prev) acc);
   process = fun acc from ->
             match acc with
             | Some acc ->
                begin try
                    let acc, next = pass.process acc from in
                    Some acc, Some next
                  with Failure msg -> handle_exception msg; None, None
                end
             | _ -> None, None}

let final_pass f = {init = (); process = (fun () itm -> (), itm); final = (fun () out -> f out; out)}

let combine : ('acc, 'from, 'mid, 'prev, 'mid2 ) t -> ('acc2, 'mid, 'target, 'mid2, 'final ) t -> ('acc1 * 'acc2, 'from, 'target, 'prev, 'final ) t = fun a b ->
  { init = a.init, b.init;
    final = (fun (acca, accb) prev ->
      let mid = a.final acca prev in
      b.final accb mid
    );
    process = fun (acca, accb) from ->
             let acca, mid = a.process acca from in
             let accb, target = b.process accb mid in
             (acca, accb), target
  }

let combine_may_die :
    ('acca option, 'from, 'mid option, 'prev, 'after_mid option) t ->
    ('accb option, 'mid, 'target option, 'after_mid, 'final option) t ->
    ( ('acca * 'accb option) option, 'from, 'target option, 'prev, 'final option) t = fun a b ->
  { init = Option.map (fun inita -> inita, b.init) a.init;
    final = (fun acc v ->
      Option.bind acc (fun (acca, accb_opt) ->
          let mid_opt = a.final (Some acca) v in
          Option.bind mid_opt (fun mid -> b.final accb_opt mid))
    );
    process = (fun acc v ->
      match acc with
      | None -> None, None
      | Some (acca, accb_opt) ->
         let acca_opt, mid_opt = a.process (Some acca) v in
         match mid_opt with
         | Some mid -> let accb, result = b.process accb_opt mid in
                       (Option.map (fun acca -> acca, accb) acca_opt), result
         | None -> None, None
    );
  }

let (|>~) list passe =
  let acc, li = List.fold_left_map passe.process passe.init list in
  passe.final acc li
let (++>) = combine
let (++?>) a b = combine_may_die a b
