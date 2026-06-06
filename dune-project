(lang dune 3.23)

(using menhir 3.0)

(name mtt)

(generate_opam_files true)

(source
 (github bksaiki/mtt))

(authors "Brett Saiki <bksaiki@gmail.com>")

(maintainers "Brett Saiki <bksaiki@gmail.com>")

(license LICENSE)

; (documentation https://url/to/documentation)

(package
 (name mtt)
 (synopsis "A dependent type theory implementation in OCaml")
 (description "A dependent type theory implementation in OCaml")
 (depends
  ocaml
  (menhir :build)
  (ppx_expect :with-test))
 (tags
  ("type theory")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
