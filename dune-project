(lang dune 3.21)
(using rocq 0.11)

(name rocq-jwa)
(version 0.1.0)
(generate_opam_files true)
(opam_file_location inside_opam_directory)
(formatting (enabled_for dune))

(source (github jwa-software/rocq-jwa))
(license MIT)
(authors "Junzhe Wang")
(maintainers "Junzhe Wang <jwa.software@foobox.com>")

(package
 (name rocq-jwa)
 (synopsis "A layered Rocq library of data structures, structures, relations and tactics")
 (description
  "rocq-jwa is a general-purpose Rocq library organised in layers, each a separate theory under the logical root jwa: Core, Tactics, Structures, Relations, Data, Logic, Algebra and Programming. Clients import a layer with From jwa Require Import <Layer>.All.")
 (depends
  (rocq-core (>= 9.2)))
 (tags (rocq "logpath:jwa")))
