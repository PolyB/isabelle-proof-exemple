(*  Titre:      Import_C.thy
    Auteur:     Adrien Stalain

    Fait dans le cadre d'un stage à Orange Labs
*)

theory Import_C
  imports "AutoCorres.AutoCorres"
begin

external_file "../src/all.c_pp"
install_C_file "../src/all.c_pp"
autocorres[heap_abs_syntax]  "../src/all.c_pp"

end