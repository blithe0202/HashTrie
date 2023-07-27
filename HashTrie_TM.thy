theory HashTrie_TM
imports
  HashTrie
  Trie
  Time_Monad
begin
fun lookup_hashtrie_tm :: "('a, 'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> 'v option tm"
  where "lookup_hashtrie_tm (Nd b _ _) [] =1 return b"|
        "lookup_hashtrie_tm (Nd _ kts m) (x#xs) =1 (case m x of None \<Rightarrow> return None|
                                                           Some t \<Rightarrow> (lookup_hashtrie_tm t xs))"

definition V_lookup_hashtrie :: "('a, 'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> 'v option" where
"V_lookup_hashtrie t xs = val(lookup_hashtrie_tm t xs)"

definition T_lookup_hashtrie :: "('a, 'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> nat" where
"T_lookup_hashtrie t xs = time(lookup_hashtrie_tm t xs)"


lemma T_lookup_hashtrie_Nil:"T_lookup_hashtrie (Nd x1 x2 x3) [] = 1"
  by(simp add: T_lookup_hashtrie_def tm_simps)


lemma T_lookup_hashtrie_Cons:"\<And>uw kts m x xs. (\<And>x2. m x = Some x2 \<Longrightarrow> T_lookup_hashtrie x2 xs \<le> length xs + 1) \<Longrightarrow>
                                    T_lookup_hashtrie (Nd uw kts m) (x # xs) \<le> length (x # xs) + 1"
  by(auto simp: T_lookup_hashtrie_def tm_simps split: tm.split option.splits)

theorem V_lookup_hashtrie:"V_lookup_hashtrie t xs = lookup_hashtrie t xs"
  apply(induct t xs rule:lookup_hashtrie.induct)
  by (auto simp: V_lookup_hashtrie_def option.case_eq_if)

theorem T_lookup_hashtrie:"T_lookup_hashtrie t xs \<le> length xs + 1"
  apply(induct t xs rule:lookup_hashtrie.induct)
  by(auto simp: T_lookup_hashtrie_def tm_simps split: tm.split option.splits)


(*trie*)
fun nodes_num_trie :: "('k, 'v) trie \<Rightarrow> nat" where
"nodes_num_trie (Trie v []) = 1"|
"nodes_num_trie (Trie v xs) = 1 + length xs + sum_list (map (nodes_num_trie \<circ> snd) xs)"

lemma nodes_num_trie_nildef:
  "\<And>m v. m \<noteq> [] \<Longrightarrow> nodes_num_trie (Trie v m) = Suc (length m + sum_list (map (nodes_num_trie \<circ> snd) m))"
  apply (case_tac "m")
  by auto

lemma list_lesseq_nodes_num_trie:"length m \<le> nodes_num_trie (Trie v m)"
  apply(case_tac "m")
  by auto

definition "Ttree = update_trie [] ''[]'' (update_trie [99::nat,104,105,110,101,115,101] ''Chinese'' empty_trie)"

fun map_of_tm :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option tm"
  where "map_of_tm [] _ =1 return None"|
        "map_of_tm (p#ps) k =1 (if k = fst p then return (Some (snd p))
                                             else map_of_tm ps k)"

definition V_map_of :: "('a \<times> 'b) list \<Rightarrow> 'a  \<Rightarrow> 'b option" where
"V_map_of t xs = val(map_of_tm t xs)"

definition T_map_of :: "('a \<times> 'b) list \<Rightarrow> 'a  \<Rightarrow> nat" where
"T_map_of t xs = time(map_of_tm t xs)"

lemma V_map_of:"V_map_of t xs = map_of t xs"
  apply(induct t xs rule:map_of_tm.induct)
  by(auto simp: V_map_of_def tm_simps split: tm.split option.splits)

lemma T_map_of:"T_map_of t xs \<le> length t + 1"
  apply(induct t xs rule:map_of_tm.induct)
  by(auto simp: T_map_of_def tm_simps split: tm.split option.splits)

value"map_of_tm [(1::nat,''a''),(2,''b''),(3,''c''),(4,''d'')] 4"

fun lookup_trie_tm ::"('k, 'v) trie \<Rightarrow> 'k list \<Rightarrow> 'v option tm"
  where "lookup_trie_tm (Trie v m) [] =1 return v"|
        "lookup_trie_tm (Trie v m) (k#ks) =1
             do { s_t \<leftarrow> map_of_tm m k;
                  case s_t of None \<Rightarrow> return None|
                              Some st \<Rightarrow> lookup_trie_tm st ks}"

definition V_lookup_trie :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option" where
"V_lookup_trie t xs = val(lookup_trie_tm t xs)"

definition T_lookup_trie :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> nat" where
"T_lookup_trie t xs = time(lookup_trie_tm t xs)"
lemma allspec:"\<And>a b.(\<And>x s. P x s \<le> Q x s ) \<Longrightarrow> P a b  \<le> Q a b"
  by auto

theorem V_lookup_trie:"V_lookup_trie t xs = lookup_trie t xs"
  apply(induct t xs rule:lookup_trie_tm.induct)
  apply (auto simp:V_lookup_trie_def)
  by (metis V_map_of V_map_of_def option.case_eq_if val_return)

thm allspec spec

fun nodes_num_list :: "('k, 'v) trie \<Rightarrow> 'k list \<Rightarrow> nat" where
"nodes_num_list (Trie v m) []= 1"|
"nodes_num_list (Trie v m) (x#xs)= 1 + length m + (case map_of m x of
      None \<Rightarrow> 0 |
      Some st \<Rightarrow>nodes_num_list st xs)"

(*lemma "nodes_num_list t ks \<le> nodes_num_trie t"
  proof(induct t arbitrary:ks)
    case (Trie vo kvs)
    then show ?case
    proof(cases "ks")
      case Nil
      then show ?thesis
        by (metis diff_is_0_eq' length_0_conv less_one linorder_cases linorder_le_cases neq0_conv
           list_lesseq_nodes_num_trie nodes_num_list.simps(1) nodes_num_trie.simps(1) zero_less_diff)
    next
      case 1:(Cons a list)
      then show ?thesis
      proof(cases "kvs")
        case Nil
        then show ?thesis using "1" by auto
      next
        case 2:(Cons a list)
        then show ?thesis using 1 apply (auto split!:option.splits)
            apply (metis Trie list.set_intros(1) prod.collapse trans_le_add1)+
          using Trie
          oops
*)

thm T_map_of list_lesseq_nodes_num_trie

(*lemma T_lookup_trie_tm:"\<And>t. T_lookup_trie t xs \<le> nodes_num_trie t + length xs + 1"
    apply(induct xs rule:lookup_trie_tm.induct)
  apply(case_tac t)
   apply(auto simp: T_lookup_trie_def tm_simps split: tm.split option.splits)
  apply(case_tac t)
apply(auto simp: T_lookup_trie_def tm_simps split: tm.split option.splits)
  apply (metis T_map_of T_map_of_def list_lesseq_nodes_num_trie time.simps add.left_commute 
       add.right_neutral ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc le_add1)
  apply (case_tac "m")
   apply(simp add: T_lookup_trie_def tm_simps split: tm.split option.splits)
  apply (simp(no_asm_simp))
 apply (metis T_map_of T_map_of_def list_lesseq_nodes_num_trie trie_less_trielist time.simps add.left_commute
       add.right_neutral ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc le_add1)
  apply(auto)
  apply (simp)
*)
theorem T_lookup_trie_tm:"T_lookup_trie t xs \<le> nodes_num_list t xs + length xs + 1"
proof(induct t xs rule:lookup_trie_tm.induct)
  case (1 v m)
  then show ?case 
    by (auto simp:T_lookup_trie_def tm_simps)
next
  case (2 v m k ks)
  then show ?case 
proof(cases "map_of m k")
  case None
  then show ?thesis  apply (auto simp: T_lookup_trie_def tm_simps split: tm.split option.splits)
    apply (metis Suc_eq_plus1 T_map_of T_map_of_def add.assoc add.commute time.simps trans_le_add2)
    by (metis V_map_of V_map_of_def option.distinct(1) val.simps)
next
  case (Some a) 
  have "val (map_of_tm m k) = map_of m k"
    by (metis (full_types) V_map_of V_map_of_def)
 then show ?thesis   apply (auto simp: T_lookup_trie_def tm_simps split: tm.split option.splits)
    apply (metis Suc_eq_plus1 T_map_of T_map_of_def add.assoc add.commute time.simps trans_le_add2)
   using 2 "V_map_of"
   by (smt (verit, del_insts) T_lookup_trie_def T_map_of T_map_of_def 
            Suc_eq_plus1 add.assoc add.commute add_mono time.simps)
qed qed


(*theorem T_lookup_trie_tm:"\<And>v m. T_lookup_trie (Trie v m) xs \<le> nodes_num_trie (Trie v m) + length xs + 1"
   apply(induct xs)
   apply(auto simp: T_lookup_trie_def tm_simps split: tm.split option.splits)
   apply (metis T_map_of T_map_of_def list_lesseq_nodes_num_trie time.simps add.left_commute 
       add.right_neutral ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc le_add1)
  apply (case_tac "x2")
  apply (case_tac "m = []")
  apply(auto simp: T_lookup_trie_def tm_simps split: tm.split option.splits)
  apply(auto simp: nodes_num_trie_nildef)
  apply(subgoal_tac "x2a + x2b \<le> Suc (Suc (nodes_num_trie (Trie x1 x2c) + length xs + length m))")
  oops*)

value "HTtree"

value "lookup_hashtrie_tm HTtree [99::nat,104,105,110,101,115,101]"
value "lookup_trie_tm Ttree [99::nat,104,105,110,101,115,101]"
end