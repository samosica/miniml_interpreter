(lang dune 3.0)

(name miniml_interpreter)

(generate_opam_files true)

(authors "samosica <samosic4@gmail.com>")

(documentation https://url/to/documentation)

(package
 (name miniml_interpreter)
 (synopsis "An interpreter of a subset of OCaml")
 (depends ocaml dune menhir))

(using menhir 2.0)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
