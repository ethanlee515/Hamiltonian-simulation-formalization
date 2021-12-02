let rec read_file_aux chan =
    try
        let c = input_char chan in
            c :: (read_file_aux chan)
    with End_of_file -> [];;

let rec write_to_file chan lst =
    match lst with
    | head :: tail ->
            output_char chan head;
            write_to_file chan tail
    | [] -> ()

let compile in_filename out_filename dt =
    let in_file = open_in in_filename in
    let in_program_body = read_file_aux in_file in
    let compilation_result = Compile_coq.compile in_program_body in
    let out_file = open_out out_filename in
    write_to_file out_file compilation_result;;

match Array.length Sys.argv with
| 4 -> compile Sys.argv.(1) Sys.argv.(2) Sys.argv.(3)
| _ -> Printf.printf "usage: ./compile program.ham program.qasm 1000\n"
;;
