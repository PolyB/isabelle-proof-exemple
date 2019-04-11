theory Listp
  imports "Import_C"
begin

section \<open>list\<close>

subsection \<open>list definition\<close>

text \<open>Le @{type list_C} est un type importé du C (struct list) qui représente une liste chainée,
  sa définition est:

  @{text "struct list { struct list *next; data_ptr data; };"}
\<close>

type_synonym list_nodes = "list_C ptr list"


primrec list :: "list_nodes \<Rightarrow> list_C ptr \<Rightarrow> lifted_globals \<Rightarrow> bool"  where
list_is_empty:  "list [] p s = (p = NULL)" |
list_is_cons:  "list (x#xs) p s = ( p = x
                              \<and> is_valid_list_C s p
                              \<and> p \<noteq> NULL
                              \<and> list xs s[p]\<rightarrow>next s
                              )"

text \<open>La propritétée @{term "list x p s"} est vraie quand @{term p} est une liste valide contenant
  les nodes @{term x} dans l'état global @{term s}\<close>
text \<open>Une liste bien définie est soit vide, et dans ce cas là @{term p} est @{const NULL},
  soit une liste commençant par @{term x} et avec comme reste @{term xs} et dans ce cas là
  @{term "p = x"}, p est valide dans l'état de heap @{term s} (@{term "is_valid_list_C s p"})
  @{term p} n'est pas @{term NULL}, et @{term xs} est une liste valide qui commence par
  @{term "s[p]\<rightarrow>next"}\<close>


definition a_list :: "list_C ptr \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "a_list p s \<equiv> (\<exists>xs. list xs p s)"

text \<open>La propriétée @{term "a_list p s"} est valide si @{term p}
  est une liste valide dans l'état @{term s}\<close>

subsection \<open>list properties\<close>

lemma list_is_empty_r : "list a NULL s \<Longrightarrow> [] = a"
  by (cases a,auto)

text \<open>Une liste valide qui commence par @{const NULL} ne peux que être vide\<close>

lemma list_is_cons_r : "p \<noteq> NULL \<Longrightarrow> list x p s = (\<exists>ys. (x = p#ys) \<and> (is_valid_list_C s p)
                                                      \<and> (p \<noteq> NULL) \<and> (list ys s[p]\<rightarrow>next s))"
  by(cases x, auto)

text \<open>Une liste valide qui n'est pas @{const NULL}, contient au moins un élément\<close>

lemma list_not_2_same : "list (x#y#z) p s \<Longrightarrow> x \<noteq> y"
  apply(clarsimp)
  apply(induction z)
   apply(clarsimp)+
  done

lemma list_append_Ex: "list (xs @ ys) p s \<Longrightarrow> (\<exists>q. list ys q s)"
  by (induct xs arbitrary: p,auto)

lemma list_unique:  "\<lbrakk> list xs p s ; list ys p s \<rbrakk> \<Longrightarrow> xs = ys"
  apply (induction xs arbitrary: p ys)
   apply(auto simp: list_is_empty_r list_is_cons_r)
  done

lemma list_distinct : "list x p s \<Longrightarrow> distinct x"
    apply (induct x arbitrary: p)
   apply simp
  apply (clarsimp dest!: split_list)
  apply (frule list_append_Ex)
  apply (auto dest: list_unique)
  done

lemma list_head_not_in_cons : "list (x#xs) x s \<Longrightarrow> x \<notin> set xs"
  apply(frule list_distinct)
  apply(simp add: distinct_def list_distinct)
  done

lemma the_list_unique : "list xs p s \<Longrightarrow> (THE ys. list ys p s) = xs"
  by (simp add: list_unique the_equality)

lemma list_next_in_list : "\<lbrakk> list xs p s ; a \<in> set xs ; s[a]\<rightarrow>next \<noteq> NULL \<rbrakk>\<Longrightarrow>(s[a]\<rightarrow>next) \<in> set xs"
  apply(induction xs arbitrary:p a)
   apply(clarsimp)
  apply(auto simp:list_is_cons_r)
  done

lemma list_has_end_not_null : "list (xs @ [x]) p s \<Longrightarrow> p \<noteq> NULL"
  apply(induction xs)
   apply(auto)
  done

lemma list_no_next_is_last : "\<lbrakk> list (xs @ [x]) p s ; w \<in> set (xs @ [x]) ; s[w]\<rightarrow>next = NULL \<rbrakk>\<Longrightarrow> w = x"
  apply(induction xs arbitrary:p)
   apply(clarsimp)+
  apply(auto)
  apply(rule ccontr)
  apply(frule list_has_end_not_null)
  apply(simp)
  done

lemma list_last_next_is_null : "list (xs @ [x]) p s \<Longrightarrow> s[x]\<rightarrow>next = NULL"
  apply(induction xs arbitrary:p)
   apply(clarsimp)+
  done

lemma list_content_is_valid : "\<lbrakk> list xs p s ; w \<in> set xs \<rbrakk> \<Longrightarrow> is_valid_list_C s w \<and> w \<noteq> NULL
                                                             \<and> (\<exists>ys. list ys s[w]\<rightarrow>next s)"
  apply(induction xs arbitrary:p)
   apply(clarsimp)+
  apply(auto)
  done

lemma first_element_in_list : "\<lbrakk> list xs p s ; p \<noteq> NULL \<rbrakk> \<Longrightarrow> p \<in> set xs"
  by (auto simp:list_is_cons_r)

section \<open>listp\<close>

subsection \<open>listp definition\<close>

definition listp :: "list_nodes \<Rightarrow> list_C ptr ptr \<Rightarrow> lifted_globals \<Rightarrow> bool" where
  "listp n pt s \<equiv> (ptr_coerce pt \<notin> set n \<and> is_valid_list_C'ptr s pt \<and> list n s[pt] s)"

text \<open>La propriétée @{term "listp x p s"} indique que @{term p} est une liste valide contenant
  les nodes @{term x} dans l'état global @{term s}\<close>

subsection \<open>listp properties\<close>

lemma listp_unique: "\<lbrakk> listp xs p s ; listp ys p s \<rbrakk> \<Longrightarrow> xs = ys"
  by (auto simp:listp_def list_unique)

subsubsection \<open>state update\<close>

lemma list_st_update_ignore [simp] : "q \<notin> set xs \<Longrightarrow> list xs p (s[q\<rightarrow>next := \<omega>]) = list xs p s"
  apply(induct xs arbitrary:p)
   apply(clarsimp)
  apply(clarsimp simp:fun_upd_def)
  done

lemma list_st_add [simp] : "\<lbrakk> is_valid_list_C s x ; x \<noteq> NULL; x \<notin> set xs \<rbrakk> 
                                                  \<Longrightarrow> list (x#xs) x s[x\<rightarrow>next := p] = list xs p s"
  by (auto simp:fun_upd_def)


lemma list_st_upd_any_base_ptr [simp] : "ptr_coerce (l :: list_C ptr ptr) \<notin> set xs 
                                                            \<Longrightarrow> list xs p s[l := \<omega>] = list xs p s"
  apply(induct xs arbitrary:p)
   apply(clarsimp)+
  done

section \<open>hoare helpers\<close>

subsection \<open>nondet monad\<close>

lemma grab_asm_NF : "(G \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!) \<Longrightarrow> \<lbrace>\<lambda>s. G \<and> P s\<rbrace> f \<lbrace>Q\<rbrace>!"
  by (simp add: triple_judgement_def validNF_is_triple)

lemma hoare_conjINF:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> R r s\<rbrace>!"
  by (simp add:hoare_conjI validNF_def)

lemma hoare_conjINFR:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!; \<lbrace>P\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> R r s\<rbrace>!"
  by (simp add:hoare_conjI validNF_def)

lemma hoare_transf_predNF: "\<lbrakk> (G' \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>! ) ; (G \<Longrightarrow> G') \<rbrakk> \<Longrightarrow> \<lbrace> \<lambda>s. G \<and> P s \<rbrace> f \<lbrace> Q \<rbrace>!"
  by (simp add: grab_asm_NF)
  

subsection \<open>option monad\<close>

lemma ovalidNF_is_validNF : "ovalidNF P f P' \<Longrightarrow> \<lbrace> P \<rbrace> gets_the f \<lbrace> P'\<rbrace>!"
  apply(unfold ovalidNF_def)
  apply(wp)
  apply(auto)
  done

lemma ovalid_is_valid : "ovalid P f P' \<Longrightarrow> \<lbrace> P \<rbrace> gets_the f \<lbrace> P'\<rbrace>"
  apply(unfold ovalid_def)
  apply(wp)
  apply(auto)
  done

lemma ovalid_herit_NF : "\<lbrakk> ovalid P f Q ; ovalidNF P f Q' \<rbrakk> \<Longrightarrow> ovalidNF P f Q"
  by (simp add: ovalidNF_def ovalid_def)

lemma ovalidNF_comb3p [wp_comb]:
  "\<lbrakk> ovalidNF P f Q; ovalidNF P f Q' \<rbrakk> \<Longrightarrow> ovalidNF (\<lambda>s. P s) f (\<lambda>r s. Q r s \<and> Q' r s)"
  by (rule OptionMonadWP.ovalidNF_wp_comb1)

lemma ovalidNF_comb3pr [wp_comb]:
  "\<lbrakk> ovalidNF P f Q; ovalid P f Q' \<rbrakk> \<Longrightarrow> ovalidNF (\<lambda>s. P s) f (\<lambda>r s. Q r s \<and> Q' r s)"
  by (simp add: ovalidNF_def ovalid_def)

lemma ovalid_grab_asm2: "(P' \<Longrightarrow> ovalid (\<lambda>s. P s \<and> R s) f Q) \<Longrightarrow> ovalid (\<lambda>s. P s \<and> P' \<and> R s) f Q"
  by (smt ovalid_assume_pre ovalid_pre_imp)
  
lemma ovalid_drop_post: "\<lbrakk> R ; ovalid P f Q \<rbrakk> \<Longrightarrow> ovalid P f (\<lambda>r s. R \<and> Q r s)"
  by auto

lemma ovalidNF_drop_post: "\<lbrakk> R ; ovalidNF P f Q \<rbrakk> \<Longrightarrow> ovalidNF P f (\<lambda>r s. R \<and> Q r s)"
  by auto

section \<open>isabelle lists helpers\<close>

lemma list_non_empty_has_init : "x \<noteq> [] \<Longrightarrow> \<exists>w. w @ [last x] = x"
  using append_butlast_last_id by auto

section \<open>state helpers\<close>

lemma next_upd_diff : "x \<noteq>w \<Longrightarrow> s[x\<rightarrow>next := a][w\<rightarrow>next := b] \<equiv> s[w\<rightarrow>next := b][x\<rightarrow>next := a]"
  by (smt all.update_list_next_def fun_upd_def fun_upd_twist
          lifted_globals.surjective lifted_globals.update_convs(4))
  
lemma listptrptr_upd_not_mod : "ptr_coerce (k :: list_C ptr ptr) \<noteq> (x :: list_C ptr)
                                                                          \<Longrightarrow> s[k := \<omega>][x] = s[x]"
  by simp

section \<open>program proof\<close>
subsection \<open>list\_empty\<close>
subsubsection \<open>correct\<close>

lemma list_empty_correct : "\<lbrace> \<lambda> s. is_valid_list_C'ptr s l \<rbrace> all.list_empty' l \<lbrace> \<lambda>_. listp [] l \<rbrace>!"
  apply(auto simp:all.list_empty'_def)
  apply(wp)
  apply(clarsimp simp:listp_def fun_upd_def)
  done

subsubsection \<open>pure\<close>

lemma list_empty_pure : " (\<forall>s. P s \<longrightarrow> P s[l := NULL]) \<Longrightarrow> \<lbrace> P \<rbrace> all.list_empty' l \<lbrace> \<lambda>_. P \<rbrace>"
  apply(unfold all.list_empty'_def)
  apply(wp)
  apply(clarsimp)
  done

subsection \<open>list\_insert\_front\<close>

subsubsection \<open>correct\<close>

lemma list_insert_front_correct : "\<lbrakk> x \<notin> set xs ; x \<noteq> NULL ; x \<noteq> ptr_coerce l \<rbrakk>
  \<Longrightarrow> \<lbrace>\<lambda>s. listp xs l s \<and> is_valid_list_C s x  \<rbrace> all.list_insert_front' l x \<lbrace>\<lambda>r. listp (x#xs) l \<rbrace>!"
  apply(clarsimp simp:all.list_insert_front'_def)
  apply(wp)
  apply(clarsimp)
  apply(unfold listp_def)
  apply(auto simp:listp_def fun_upd_def)
  done

subsubsection \<open>pure\<close>

lemma  list_insert_front_pure : "(\<forall>s. P s \<longrightarrow>  P s[x\<rightarrow>next := s[l]][l := x]) 
                                                     \<Longrightarrow> \<lbrace> P \<rbrace> all.list_insert_front' l x \<lbrace>\<lambda>_. P \<rbrace>"
  apply(clarsimp simp:all.list_insert_front'_def)
  apply(wp)
  apply(clarsimp)
  done

subsection \<open>list\_singleton\<close>

subsubsection \<open>correct\<close>

lemma list_singleton_correct : "\<lbrakk> x \<noteq> NULL ; x \<noteq> ptr_coerce l \<rbrakk> \<Longrightarrow> 
                                              \<lbrace> \<lambda>s. is_valid_list_C s x \<and> is_valid_list_C'ptr s l  \<rbrace>
                                              all.list_singleton' l x
                                              \<lbrace> \<lambda> r. listp [x] l \<rbrace>!"
  apply(clarsimp simp:all.list_singleton'_def)
  apply(wp)
  apply(clarsimp)
  apply(unfold listp_def)
  apply(intro conjI)
    apply(simp)
   apply(simp)
  apply(unfold list_is_cons)
  apply(intro conjI)
     apply(simp add:fun_upd_same)+
  done

subsubsection \<open>pure\<close>

lemma list_singleton_pure : "(\<forall>s. P s \<longrightarrow> P s[l := x][x\<rightarrow>next := NULL]) \<Longrightarrow> \<lbrace> P \<rbrace> all.list_singleton' l x \<lbrace> \<lambda>_. P \<rbrace>"
  apply(unfold all.list_singleton'_def)
  apply(wp)
  apply(clarsimp)
  done

subsection \<open>list\_insert\_after\<close>

subsubsection \<open>correct\<close>

lemma list_insert_inside : "\<lbrakk> n \<notin> set(x1 @ w # x2) ; n \<noteq> NULL ; is_valid_list_C s n 
                            ; list (x1 @ [w] @ x2) p s\<rbrakk> 
                            \<Longrightarrow> list (x1 @ w # n # x2) p s[w\<rightarrow>next := n][n\<rightarrow>next := s[w]\<rightarrow>next]"
  apply(subgoal_tac "w \<notin> set (x1 @ x2)")

   apply (induction x1 arbitrary:p)
    apply(clarsimp)
  apply(intro conjI)
       apply(simp add:fun_upd_def)+
  apply(intro conjI)+
  apply(clarsimp)+

   apply(frule list_distinct)
    apply (simp)
  done

lemma list_insert_after_correct : "\<lbrakk> x \<noteq> w ; x \<notin> set xa ; x \<notin> set xb ; x \<noteq> NULL \<rbrakk> 
                                          \<Longrightarrow> \<lbrace> \<lambda>s. list (xa @ [w] @ xb) p s \<and> is_valid_list_C s x \<rbrace>
                                              all.list_insert_after' w x
                                              \<lbrace> \<lambda>r s. list (xa @ [w,x] @ xb) p s \<rbrace>!"
  apply (clarsimp simp: all.list_insert_after'_def)
  apply(wp)
  apply(intro conjI)
  apply(subst next_upd_diff)
   apply(simp)
  apply(subst list_insert_inside)
       apply(clarsimp)+
  apply(simp add: list_content_is_valid)
  done


lemma list_insert_after_correct_p : "\<lbrakk> ptr_coerce p \<noteq> x ;  x \<notin> set (xa @ [w] @ xb) ; x \<noteq> NULL \<rbrakk> \<Longrightarrow> \<lbrace> \<lambda>s. listp (xa @ [w] @ xb) p s \<and> is_valid_list_C s x \<rbrace> all.list_insert_after' w x \<lbrace> \<lambda>r s. listp (xa @ [w,x] @ xb) p s \<rbrace>!"
 apply (clarsimp simp: all.list_insert_after'_def listp_def)
  apply(wp)
  apply(intro conjI,clarsimp+)
  apply(subst next_upd_diff,simp)
  apply(subst list_insert_inside)
        apply(clarsimp)+
   apply(simp add:list_content_is_valid[where w=w],simp)
  done

subsubsection \<open>pure\<close>

lemma list_insert_after_pure : "(\<forall>s \<omega>. P s \<longrightarrow> P s[x\<rightarrow>next := \<omega>][w\<rightarrow>next := x]) \<Longrightarrow> \<lbrace> P \<rbrace> all.list_insert_after' w x \<lbrace> \<lambda>r. P \<rbrace>"
  apply(clarsimp simp:all.list_insert_after'_def)
  apply(wp)
  apply(clarsimp)
  done

subsubsection \<open>specialisations\<close>

lemma list_insert_after_last : "\<lbrakk> (\<exists>a. a @ w # [] = xs) ; x \<notin> set xs ; x \<noteq> NULL ; (ptr_coerce p) \<noteq> x \<rbrakk> \<Longrightarrow> \<lbrace> \<lambda>s. listp xs p s \<and> is_valid_list_C s x \<rbrace> all.list_insert_after' w x \<lbrace>\<lambda> r. listp (xs @ [x]) p \<rbrace>!"
  apply(clarsimp)
  apply(frule list_insert_after_correct_p[where xb="[]", where w=w, where x=x],simp)
  apply(clarsimp)+
  done

lemma list_insert_after_the_last : "\<lbrakk> x \<notin> set xs ; x \<noteq> NULL ; (ptr_coerce p) \<noteq> x ; xs \<noteq> [] \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. listp xs p s \<and> is_valid_list_C s x \<rbrace> all.list_insert_after' (last xs) x \<lbrace> \<lambda>_. listp (xs @ [x]) p\<rbrace>!"
  apply(rule list_insert_after_last)
  apply(rule list_non_empty_has_init)
  apply(clarsimp)+
  done

lemma list_insert_after_the_last_pre : "\<lbrakk> x \<notin> set xs ; x \<noteq> NULL ; (ptr_coerce p) \<noteq> x ; xs \<noteq> [] ; w = last xs \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. listp xs p s \<and> is_valid_list_C s x \<rbrace> all.list_insert_after' w x \<lbrace> \<lambda>_. listp (xs @ [x]) p\<rbrace>!"
  apply(simp)
  apply(rule list_insert_after_the_last)
     apply(clarsimp)+
  done


subsection \<open>list\_find\_last\_node\<close>

subsubsection \<open>list\_find\_last\_node\_inner\_loop\_content\<close>

definition list_find_last_node_inner_loop_content :: "list_C ptr \<Rightarrow> lifted_globals \<Rightarrow> list_C ptr option" where
  "list_find_last_node_inner_loop_content p \<equiv> DO oguard (\<lambda>s. is_valid_list_C s p);
         p <- ogets (\<lambda>s. s[p]\<rightarrow>next);
         oguard (\<lambda>s. is_valid_list_C s p);
         oreturn p
      OD"

lemma list_find_last_node_inner_loop_content_correct : " \<lbrakk> a \<in> set (xs @ [x]) ; a \<noteq> NULL \<rbrakk> \<Longrightarrow> ovalidNF (\<lambda>s. list (xs @ [x]) pb s \<and> a_list a s \<and> s[a]\<rightarrow>next \<noteq> NULL)
          (list_find_last_node_inner_loop_content a) (\<lambda>a b. a \<in> set (xs @ [x]) \<and> a \<noteq> NULL \<and> list (xs @ [x]) pb b \<and> a_list a b)"
    apply(unfold list_find_last_node_inner_loop_content_def)
    apply(wp del:list_def set_append)
  apply(clarsimp simp del:set_append)
  apply(frule list_content_is_valid[where xs="(xs @ [x])", where p=pb, where w=a])
     apply(clarsimp)
    apply(rule)
     apply(clarsimp)
  apply(clarsimp simp del:set_append)
  apply(rule)
   apply(clarsimp simp:list_is_cons_r)
  apply(rule)
  apply(simp add: list_next_in_list del:set_append)
  apply(auto simp:a_list_def list_is_cons_r)
  done

lemma list_find_last_node_inner_loop_content_pure : "ovalid P (list_find_last_node_inner_loop_content a) (\<lambda>_. P)"
  apply(unfold list_find_last_node_inner_loop_content_def)
  apply(wp)
  apply(auto)
  done

subsubsection \<open>list\_find\_last\_node\_inner\_loop\<close>

definition list_find_last_node_inner_loop :: "list_C ptr \<Rightarrow> lifted_globals \<Rightarrow> list_C ptr option" where
 "list_find_last_node_inner_loop p \<equiv> owhile (\<lambda>p s. s[p]\<rightarrow>next \<noteq> NULL) (\<lambda>p. DO oguard (\<lambda>s. is_valid_list_C s p);
         p <- ogets (\<lambda>s. s[p]\<rightarrow>next);
         oguard (\<lambda>s. is_valid_list_C s p);
         oreturn p
      OD) p"

lemma list_find_last_node_inner_loop_content_mesure : " \<lbrakk> a \<in> set (xs @ [x]) ; a \<noteq> NULL \<rbrakk> \<Longrightarrow> ovalid
            (\<lambda>s. list (xs @ [x]) pb s \<and> a_list a s \<and> s[a]\<rightarrow>next \<noteq> NULL \<and> length (THE xs. list xs a s) = m)
            (list_find_last_node_inner_loop_content a)
            (\<lambda>r s. length (THE xs. list xs r s) < m)"
  apply(unfold list_find_last_node_inner_loop_content_def)
  apply(wp)
  apply(unfold a_list_def)
  apply(clarsimp)
  apply(frule_tac p=a in the_list_unique)
  apply(simp)
  apply(case_tac xsa)
  apply(clarsimp)
  apply (metis length_Cons lessI list_is_cons the_list_unique)
  done

lemma list_find_last_node_inner_loop_correct : "ovalidNF (list (xs @ [x]) pb) (list_find_last_node_inner_loop pb) (\<lambda>r _. r = x)"
  apply(unfold list_find_last_node_inner_loop_def)
  apply(subst list_find_last_node_inner_loop_content_def[symmetric])
  apply(subst owhile_add_inv [where I = "\<lambda>p s. p \<in> set (xs @ [x]) \<and> p \<noteq> NULL \<and> list (xs @ [x]) pb s \<and> a_list p s", where M = "\<lambda>p s. length (THE xs. list xs p s)"])
  apply(wp)
    apply(simp del:set_append)
     apply(rule ovalidNF_grab_asm)+
     apply(simp add: list_find_last_node_inner_loop_content_correct del:set_append)
    apply(simp del:set_append)
    apply(rule ovalid_grab_asm)+
  apply(simp)
    apply(simp add: list_find_last_node_inner_loop_content_mesure)
   apply(simp del:set_append)
  apply(clarsimp simp add: list_no_next_is_last)
  apply(frule list_has_end_not_null)
  apply(auto)
  apply(frule first_element_in_list)
    apply(simp)
   apply(clarsimp)
  apply(unfold a_list_def)
  apply(auto)
  done

lemma list_find_last_node_inner_loop_pure : "ovalid P (list_find_last_node_inner_loop p) (\<lambda>r. P)"
  apply(unfold list_find_last_node_inner_loop_def)
  apply(subst list_find_last_node_inner_loop_content_def[symmetric])
  apply(subst owhile_add_inv [where I="\<lambda>p. P"])
  apply(wp add:list_find_last_node_inner_loop_content_pure)
   apply(auto)
  done

subsubsection \<open>correct\<close>

lemma list_find_last_node_correct : "ovalidNF (listp (xs @ [x]) p ) (all.list_find_last_node' p) (\<lambda>r _. r = x) "
  apply(unfold all.list_find_last_node'_def)
  apply(subst list_find_last_node_inner_loop_def[symmetric])
  apply(wp)
     apply(rule list_find_last_node_inner_loop_correct[of xs x])
    apply(wp)
   apply(wp)
  apply(wp)
  apply(clarsimp simp:listp_def)
  apply(frule list_has_end_not_null)
  apply(intro conjI)
   apply(simp)
  apply(clarsimp simp:list_is_cons_r)
  done

lemma list_find_last_node_correct2 : "xs = ys @ [w] \<Longrightarrow> ovalidNF (listp xs p ) (all.list_find_last_node' p) (\<lambda>r _. r = w) "
  by(auto simp:list_find_last_node_correct)

subsubsection \<open>pure\<close>

lemma  list_find_last_node_pure : "ovalid P (all.list_find_last_node' p) (\<lambda>r. P)"
    apply(unfold all.list_find_last_node'_def)
  apply(subst list_find_last_node_inner_loop_def[symmetric])
  apply(wp add:list_find_last_node_inner_loop_pure)
  apply(auto)
  done

subsubsection \<open>specialisations\<close>

lemma list_find_last_node_correct_ND : "xs \<noteq> [] \<Longrightarrow> \<lbrace> listp xs l \<rbrace> gets_the (all.list_find_last_node' l) \<lbrace>\<lambda>xa s. xa = last xs\<rbrace>!"
  apply(subst ovalidNF_is_validNF)
    apply(frule list_non_empty_has_init)
    apply(clarsimp)
    apply(rule_tac xs=xs and ys=w and w="last xs" and p=l in list_find_last_node_correct2)
   apply(clarsimp)
  apply(simp)
  done

lemma list_find_last_node_pure_ND : "\<lbrace> P \<rbrace> gets_the (all.list_find_last_node' l) \<lbrace> \<lambda>_. P \<rbrace>"
  apply(subst ovalid_is_valid)
  apply(rule list_find_last_node_pure)
  apply(simp)
  done

subsection \<open>list\_insert\_back\<close>

subsubsection \<open>correct\<close>

lemma list_insert_back_correct : "(x \<notin> set xs \<and> x \<noteq> NULL \<and> x \<noteq> (ptr_coerce l)) \<Longrightarrow> \<lbrace>\<lambda>s. listp xs l s \<and> is_valid_list_C s x \<rbrace> all.list_insert_back' l x \<lbrace> \<lambda> _. listp (xs @ [x]) l \<rbrace>!"
  apply(cases "xs = []")
 (* empty *)
   apply(clarsimp simp:all.list_insert_back'_def)
   apply(wp)
      apply(rule list_singleton_correct)
       apply(simp)
  apply(simp)
     apply(rule validNF_false_pre )
    apply(wp)
   apply(clarsimp simp:listp_def)
(* cons *)
  apply(clarsimp simp:all.list_insert_back'_def)
  apply(wp)
  apply(rule validNF_false_pre )
    apply(wp)
     apply(rule hoare_transf_predNF[OF list_insert_after_the_last_pre])
  apply(simp)+
    apply(rule validNF_post_comb_conj_L)
     apply(rule list_find_last_node_correct_ND)
     apply(simp)
    apply(rule list_find_last_node_pure_ND)
   apply(wp)
  using list_is_empty_r listp_def apply fastforce
  done
end