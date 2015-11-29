open Unix

(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
let now () = Unix.times(), Unix.gettimeofday()

let last_time = ref (now ())

let start_timer() = last_time := now (); !last_time

let interval (cpu_time0,clock_time0) (cpu_time1,clock_time1) = 
  {tms_utime  = cpu_time1.tms_utime -. cpu_time0.tms_utime;
   tms_stime  = cpu_time1.tms_stime -. cpu_time0.tms_stime;
   tms_cutime = cpu_time1.tms_cutime -. cpu_time0.tms_cutime;
   tms_cstime = cpu_time1.tms_cstime -. cpu_time0.tms_cstime
  },
  clock_time1 -. clock_time0
  
let last_interval() =
  let time_now = now() in
  let prev = !last_time in 
  let result = interval prev time_now
  in
  last_time := time_now;
  result

let show_interval s (cpu_interval, clock_interval) =
  let cpu_interval = cpu_interval.Unix.tms_utime +. cpu_interval.Unix.tms_stime in
  let message = 
    Printf.sprintf "\n%s CPU %f clock %f ratio %f%%" 
                   s cpu_interval clock_interval 
                   ((cpu_interval /. clock_interval) *. 100.0)
  in
  print_newline (print_string message)