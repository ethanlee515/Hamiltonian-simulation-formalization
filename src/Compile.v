Require Import String Extraction ExtrOcamlString.

Open Scope string_scope.

Definition compile (program : string) :=
    (* TODO *)
    "compile(" ++ program ++ ")".

Extraction "../extracted/compile_coq.ml" compile.
