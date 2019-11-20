(*************
  Statistic
**************)

let initial_time = (Unix.times ()).Unix.tms_utime

let record_time = true

type stat =
  {
    mutable recorded: bool;
    mutable time : float;
    mutable call : int;
    mutable time_last_restarted : float;
    name : string;
  }

let current_recording = ref []

let record_tail =
  if record_time
  then
    (fun ref_t f_cont f_next ->
      ref_t.recorded <- true;
      let t0 = (Unix.times ()).Unix.tms_utime in

      (* We stop the current recording *)
      begin match !current_recording with
        | [] -> ()
        | ref_t'::_ -> ref_t'.time <- ref_t'.time +. t0 -. ref_t'.time_last_restarted
      end;

      (* We add the new recording time *)
      ref_t.time_last_restarted <- t0;
      ref_t.call <- ref_t.call + 1;
      current_recording := ref_t::!current_recording;

      f_cont (fun () ->
        (* We stop the clock *)
        let t1 = (Unix.times ()).Unix.tms_utime in
        ref_t.time <- ref_t.time +. t1 -. ref_t.time_last_restarted;
        begin match !current_recording with
          | _::((ref_t'::_) as q) ->
              ref_t'.time_last_restarted <- t1;
              current_recording := q
          | _::q -> current_recording := q
          | _ -> Config.internal_error "[statistic.ml >> record_time] There should be at least one recorder."
        end;
        f_next ()
      )
    )
  else (fun _ f_cont f_next -> f_cont f_next)

(******* The function recorded ******)

let recorder_list = ref []

let create name =
  let r = { name = name; time = 0.; call = 0; recorded = false; time_last_restarted = 0. } in
  recorder_list := r :: ! recorder_list;
  r

let reset =
  if record_time
  then
    (fun () ->
      List.iter (fun r -> r.time <- 0.; r.call <- 0; r.recorded <- false; r.time_last_restarted <- 0. ) !recorder_list;
      current_recording := []
    )
  else (fun _ -> ())

let time_sat = create "Sat"
let time_non_deducible_term = create "Non Deducible Term"
let time_sat_disequation = create "Sat Disequation"
let time_split_data_constructor = create "Split Data Constructor"
let time_normalisation_deduction_consequence = create "Normalisation Deduction Consequence"
let time_rewrite = create "Rewrite"
let time_equality_constructor = create "Equality_constructor"
let time_other = create "Other"

let display_statistic () =
  Display.display_list (fun r ->
    Printf.sprintf "%s: %fs (%d calls)" r.name r.time r.call
  ) ", " !recorder_list
