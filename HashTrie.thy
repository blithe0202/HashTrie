theory HashTrie
  imports "HOL-Library.AList" Set_Specs
begin
(*-------------------------------------hashhashtrie----------------------------------------------*)
subsection \<open> HashTrie\<close>
datatype 'a str = Ch 'a 'a|En 'a

datatype ('a, 'v) hashtrie = Nd ("value":"'v option")  (children:"('a * ('a, 'v) hashtrie) list") (mp:"'a \<Rightarrow> ('a, 'v) hashtrie option")
term fun_upd

definition empty_hashtrie ::"('a,'v) hashtrie"
  where "empty_hashtrie \<equiv> Nd None [] (\<lambda>_. None)"

fun is_empty_hashtrie::"('a,'v) hashtrie \<Rightarrow> bool"
  where "is_empty_hashtrie (Nd v kts m) = (v = None \<and> kts = [] \<and> m = (\<lambda>_. None))"

fun invar_hashtrie :: "('a, 'v) hashtrie \<Rightarrow> bool" where
"invar_hashtrie (Nd v kts m) = (distinct (map fst kts) \<and> (\<forall>ke st. m ke = Some st \<longleftrightarrow>  map_of kts ke = Some st) \<and>
                           (\<forall>(k, t) \<in> set kts. \<not> is_empty_hashtrie t \<and> invar_hashtrie t))"

fun isin_hashtrie::"'a list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> bool"
  where "isin_hashtrie [] (Nd None _ _) = False"|
        "isin_hashtrie [] (Nd (Some b) _ _) = True"|
        "isin_hashtrie (x#xs) (Nd _ kts m) = (case m x of None \<Rightarrow> False | Some t \<Rightarrow> isin_hashtrie xs t)"

definition set_hashtrie :: "('a,'v) hashtrie \<Rightarrow> 'a list set" where
[simp]: "set_hashtrie t = {xs. isin_hashtrie xs t}"

lemma ehashtrie_eq_eset:"is_empty_hashtrie t \<Longrightarrow> set_hashtrie t = {}"
  apply(cases "t")
  apply (auto)
  using isin_hashtrie.elims(1) by force

fun lookup_hashtrie::"('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> 'v option"
  where"lookup_hashtrie (Nd b _ _) [] = b" |
       "lookup_hashtrie (Nd _ kts m) (x#xs) = (case m x of None \<Rightarrow> None | 
                                                           Some t \<Rightarrow> lookup_hashtrie t xs)"

fun text_in_hashtrie::"('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> 'v option"
  where"text_in_hashtrie (Nd b _ _) [] = b" |
       "text_in_hashtrie (Nd b kts m) (x#xs) = 
           (if b = None then (case m x of None \<Rightarrow> None | 
                                          Some t \<Rightarrow> text_in_hashtrie t xs)
                              else b)"

fun lookup_pre_in_hashtrie::"('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> ('a,'v) hashtrie option"
  where"lookup_pre_in_hashtrie (Nd b kts m) [] = (case b of None \<Rightarrow> None | Some v \<Rightarrow> Some (Nd b kts m))"|
       "lookup_pre_in_hashtrie (Nd _ kts m) (x#[]) = (case m x of None \<Rightarrow> None | Some t \<Rightarrow> Some t)"|
       "lookup_pre_in_hashtrie (Nd _ kts m) (x#xs) = (case m x of None \<Rightarrow> None | Some t \<Rightarrow> lookup_pre_in_hashtrie t xs)"

fun mapup_with_aux ::
    "'val \<Rightarrow> 'key \<Rightarrow> ('val \<Rightarrow> 'val) \<Rightarrow> ('key \<rightharpoonup> 'val) \<Rightarrow> ('key \<rightharpoonup> 'val)"
    where "mapup_with_aux ou i f m =
      (case m i of None \<Rightarrow> m(i := Some (f ou)) | Some k' \<Rightarrow> m(i := Some (f k')))"

lemma mapup_with_aux_eq:
  "mapup_with_aux v k f m =
    m(k \<mapsto> (case m k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))"
  by (simp add: option.case_eq_if)    

fun insert_key_hashtrie::"'a list \<Rightarrow> ('v option \<Rightarrow> 'v) \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> ('a,'v) hashtrie"
  where"insert_key_hashtrie [] fv (Nd v kts m) = (Nd (Some (fv v)) kts m)"|
       "insert_key_hashtrie (x#xs) fv (Nd v kts m) =
        Nd v (AList.update_with_aux empty_hashtrie x (insert_key_hashtrie xs fv) kts)
              (mapup_with_aux empty_hashtrie x (insert_key_hashtrie xs fv) m)"
definition insert_hashtrie::"'a list \<Rightarrow> 'v \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> ('a,'v) hashtrie" 
  where"insert_hashtrie k v = insert_key_hashtrie k (\<lambda>_. v)"

definition"HTtree = insert_hashtrie [] ''[]'' (insert_hashtrie [99::nat,104,105,110,101,115,101] ''Chinese'' empty_hashtrie)"

lemma insert_hashtrie_induct:
  "\<lbrakk>\<And>v kts m. P [] (Nd v kts m); \<And>k ks v kts m. (\<And>x. P ks x) \<Longrightarrow> P (k#ks) (Nd v kts m)\<rbrakk> \<Longrightarrow> P xs t"
  by induction_schema (pat_completeness, lexicographic_order)

lemma insert_hashtrie_Nil: "insert_hashtrie [] v (Nd vo ts m) = (Nd (Some v) ts m)"
by(simp add: insert_hashtrie_def)

lemma insert_hashtrie_Cons: "insert_hashtrie (k#ks) v (Nd vo ts m) =
  Nd vo (AList.update_with_aux (Nd None [] (\<lambda>_. None)) k (insert_hashtrie ks v) ts) (mapup_with_aux (Nd None [] (\<lambda>_. None)) k (insert_hashtrie ks v) m)"
  by(simp add: insert_hashtrie_def empty_hashtrie_def)

lemma insert_key_hashtrie_value:"value (insert_key_hashtrie ks (\<lambda>_. v) t) = (if ks = [] then (Some v) else value t)"
  by (metis insert_key_hashtrie.simps(2) insert_hashtrie_Nil insert_hashtrie_def splice.elims hashtrie.exhaust_sel hashtrie.sel(1))


fun delete_hashtrie :: "'a list \<Rightarrow> ('a, 'v) hashtrie \<Rightarrow> ('a, 'v) hashtrie"
where
"delete_hashtrie [] (Nd v kts m) = Nd None kts m" |
"delete_hashtrie (k#ks) (Nd v kts m) =
   (case m k of
      None \<Rightarrow> Nd v kts m |
      Some t \<Rightarrow> let t' = delete_hashtrie ks t 
                in if is_empty_hashtrie t'
                   then Nd v (AList.delete_aux k kts) (m(k := None))
                   else Nd v (AList.update k t' kts) (m(k := Some t')))"

lemma is_empty_conv: "is_empty_hashtrie ts \<longleftrightarrow> ts = Nd None [] (\<lambda>_. None)"
  apply(cases ts)
  by(simp)

subsection \<open>@{const lookup_hashtrie}\<close>
lemma lookup_empty [simp]: "lookup_hashtrie empty_hashtrie = Map.empty"
proof                               
  fix ks show "lookup_hashtrie empty_hashtrie ks = Map.empty ks"
    apply(cases ks)
     apply(auto simp add: empty_hashtrie_def)
    done
qed

lemma lookup_empty' [simp]: "lookup_hashtrie (Nd None [] (\<lambda>_. None)) ks = None"
  by(simp add: lookup_empty[unfolded empty_hashtrie_def])

theorem lookup_None_set:"lookup_hashtrie t xs = None \<Longrightarrow> \<not> (xs \<in> set_hashtrie t)"
  apply (induct t xs rule:lookup_hashtrie.induct)
  apply simp
  using case_optionE by simp force

theorem lookup_Some_set:"lookup_hashtrie t xs = Some v\<Longrightarrow> xs \<in> set_hashtrie t"
 apply (induct t xs rule:lookup_hashtrie.induct)
  apply simp+
  by (metis option.case_eq_if option.collapse option.distinct(1))

lemma lookup_insert_Nd:"\<And>k ks va kts m ks'.
       (\<And>x ks'. lookup_hashtrie (insert_hashtrie ks v x) ks' = (if ks = ks' then Some v else lookup_hashtrie x ks')) \<Longrightarrow> 
         lookup_hashtrie (insert_hashtrie (k # ks) v (Nd va kts m)) ks' = (if k # ks = ks' then Some v else lookup_hashtrie (Nd va kts m) ks')"
 apply(case_tac ks')
    apply(simp add: insert_hashtrie_def)
    apply(auto simp: insert_hashtrie_def)
    apply (metis (mono_tags) fun_upd_same insert_hashtrie_def option.case_eq_if option.simps(5))
    apply (metis (no_types, lifting) fun_upd_other option.case_eq_if)
    apply(case_tac "a = k")
    apply (metis (mono_tags)  fun_upd_same insert_hashtrie_def lookup_empty option.exhaust option.simps(4) option.simps(5))
  by (metis (no_types, lifting) fun_upd_other option.case_eq_if)

lemma lookup_insert:
  "lookup_hashtrie (insert_hashtrie ks v t) ks' = (if ks = ks' then Some v else lookup_hashtrie t ks')"
proof(induct ks t arbitrary: ks' rule: insert_hashtrie_induct)
  case (1 vo ts ks')
  show ?case by(fastforce simp add: insert_hashtrie_def neq_Nil_conv dest: not_sym)
next
  case (2 k ks vo ts ks')
  show ?case
  by (simp only: "2" lookup_insert_Nd)
qed

lemma lookup_insert':
  "lookup_hashtrie (insert_hashtrie ks v t) = (lookup_hashtrie t)(ks \<mapsto> v)"
  by(rule ext)(simp add: lookup_insert)

lemma map_eq_map_of:"invar_hashtrie (Nd vo kvs m) \<Longrightarrow>  (m k = Some t) = (map_of kvs k = Some t)"
  by force

lemma map_eq_Some_iff:"distinct(map fst kvs) \<Longrightarrow> invar_hashtrie (Nd vo kvs m) \<Longrightarrow>  m k = Some t = ((k,t) \<in> set kvs)"
  apply(drule map_of_eq_Some_iff)
  apply(drule map_eq_map_of)
  by auto

theorem lookup_eq_Some_iff:
assumes invar: "invar_hashtrie ((Nd vo kvs m) :: ('key, 'val) hashtrie)"
shows "lookup_hashtrie (Nd vo kvs m) ks = Some v \<longleftrightarrow>
    (ks = [] \<and> vo = Some v) \<or> (\<exists>k t ks'. ks = k # ks' \<and>
    (k, t) \<in> set kvs \<and> m k = Some t \<and>  lookup_hashtrie t ks' = Some v)"
proof (cases ks)
  case Nil thus ?thesis by simp
next
  case (Cons k ks')  note ks_eq[simp] = Cons
  show ?thesis
  proof (cases "m k")
    case None thus ?thesis by (simp)
  next
    case (Some t') note map_eq = this
    from invar have dist_kvs: "distinct (map fst kvs)" by simp
    from map_eq_Some_iff[OF dist_kvs invar, of k] map_eq
    show ?thesis by simp metis     
  qed
qed

theorem lookup_eq_None_iff:
assumes invar: "invar_hashtrie ((Nd vo kvs m) :: ('key, 'val) hashtrie)"
shows "lookup_hashtrie (Nd vo kvs m) ks = None \<longleftrightarrow>
    (ks = [] \<and> vo = None) \<or>
    (\<exists>k t ks'. ks = k # ks' \<and> (\<forall>t. ((k, t) \<in> set kvs \<and> m k = Some t) 
    \<longrightarrow> lookup_hashtrie t ks' = None))"
    apply (cases ks)
    apply auto[]
    apply (auto split: option.split)
    using lookup_eq_Some_iff[of vo kvs m ks, OF invar]
    by auto


subsection \<open>@{const text_in_hashtrie}\<close>
lemma text_in_hashtrie_insert_Nd:"\<And>k ks va kts m ks'.
       (\<And>x ks'.
           text_in_hashtrie (insert_hashtrie ks v x) ks' =
           (if \<exists>sks. ks' = ks @ sks then text_in_hashtrie (insert_hashtrie ks v x) ks else text_in_hashtrie x ks')) \<Longrightarrow>
       text_in_hashtrie (insert_hashtrie (k # ks) v (Nd va kts m)) ks' =
       (if \<exists>sks. ks' = (k # ks) @ sks then text_in_hashtrie (insert_hashtrie (k # ks) v (Nd va kts m)) (k # ks)
        else text_in_hashtrie (Nd va kts m) ks')"
  apply(case_tac ks')
  apply (simp add: insert_hashtrie_Cons)
   apply(simp add: insert_hashtrie_def)
  apply (auto simp: option.case_eq_if)
  by (smt (verit, ccfv_threshold) empty_hashtrie_def is_empty_hashtrie.simps text_in_hashtrie.elims option.simps(4))
  
lemma text_in_hashtrie_empty [simp]: "text_in_hashtrie empty_hashtrie = Map.empty"
proof                               
  fix ks show "text_in_hashtrie empty_hashtrie ks = Map.empty ks"
    apply(cases ks)
     apply(auto simp add: empty_hashtrie_def)
    done
qed

lemma text_in_hashtrie_empty' [simp]: "text_in_hashtrie (Nd None [] (\<lambda>_. None)) ks = None"
  by(simp add: text_in_hashtrie_empty[unfolded empty_hashtrie_def])

lemma text_in_hashtrie_insert:
  "text_in_hashtrie (insert_hashtrie ks v t) ks' = 
   (if (\<exists>sks. ks' = ks@sks) then text_in_hashtrie (insert_hashtrie ks v t) ks
                            else text_in_hashtrie t ks')"
proof(induct ks t arbitrary: ks' rule: insert_hashtrie_induct)
  case (1 vo ts m ks')
  show ?case
    by (metis append.left_neutral insert_hashtrie_Nil isin_hashtrie.simps(1) isin_hashtrie.simps(2) list.exhaust text_in_hashtrie.simps(1) text_in_hashtrie.simps(2))
next
  case (2 k ks vo ts ks')
  show ?case
    by (simp add: "2" text_in_hashtrie_insert_Nd)
qed

lemma  text_in_hashtrie_eq_Some_iff:
assumes invar: "invar_hashtrie ((Nd vo kvs m) :: ('key, 'val) hashtrie)"
shows " text_in_hashtrie (Nd vo kvs m) ks = Some v \<longleftrightarrow>
    (vo = Some v) \<or> (\<exists>k t ks'. ks = k # ks'\<and> vo = None \<and> (k, t) \<in> set kvs \<and>
                      m k = Some t \<and> text_in_hashtrie t ks' = Some v)"
proof (cases ks)
  case Nil thus ?thesis by simp
next
  case (Cons k ks')
  note ks_eq[simp] = Cons
  show ?thesis
  proof (cases "m k")
    case None thus ?thesis 
      apply (simp)
    done
  next
    case (Some t') note map_eq = this
    from invar have dist_kvs: "distinct (map fst kvs)" by simp
    from map_eq_Some_iff[OF dist_kvs invar, of k] map_eq
    show ?thesis apply auto  apply fastforce done  
  qed
qed


lemma text_in_hashtrie_eq_None_iff:
assumes invar: "invar_hashtrie ((Nd vo kvs m) :: ('key, 'val) hashtrie)"
shows "text_in_hashtrie (Nd vo kvs m) ks = None \<longleftrightarrow>
    (ks = [] \<and> vo = None) \<or> ((\<exists>k t ks'. ks = k # ks' \<and> (vo = None) \<and>
    (\<forall>t.((k, t) \<in> set kvs \<and> m k = Some t) \<longrightarrow> text_in_hashtrie t ks' = None)))"
using text_in_hashtrie_eq_Some_iff[of vo kvs m ks, OF invar]
  apply (cases ks)
  apply simp+
  apply auto
  by (metis not_None_eq)

subsection \<open>@{const lookup_pre_in_hashtrie}\<close>
(*lemma lookup_pre_in_hashtrie_eq_Some_iff:
assumes invar: "invar_hashtrie ((Nd vo kvs m) :: ('key, 'val) hashtrie)"
shows "lookup_pre_in_hashtrie (Nd vo kvs m) ks = Some st \<longleftrightarrow>
    (ks = [] \<and> vo = Some v \<and> st =(Nd vo kvs m)) \<or> (\<exists>k t. ks = k#[] \<and> (k, t) \<in> set kvs \<and> m k = Some st) \<or>
    (\<exists>k t ks'. ks = k # ks' \<and> (k, t) \<in> set kvs \<and> m k = Some t \<and>  lookup_pre_in_hashtrie t ks' = Some st)"
proof (cases ks)
  case Nil thus ?thesis by simp
next
  case (Cons k ks')
  note ks_eq[simp] = Cons
  show ?thesis
  proof (cases "m k")
    case None thus ?thesis 
      apply (simp)
    done
  next
    case (Some t') note map_eq = this
    from invar have dist_kvs: "distinct (map fst kvs)" by simp
    from map_eq_Some_iff[OF dist_kvs invar, of k] map_eq
    show ?thesis by simp metis     
  qed
qed


lemma lookup_eq_None_iff:
assumes invar: "invar_hashtrie ((Nd vo kvs m) :: ('key, 'val) hashtrie)"
shows "lookup_hashtrie (Nd vo kvs m) ks = None \<longleftrightarrow>
    (ks = [] \<and> vo = None) \<or>
    (\<exists>k t ks'. ks = k # ks' \<and> (\<forall>t. ((k, t) \<in> set kvs \<and> m k = Some t) \<longrightarrow> lookup_hashtrie t ks' = None))"
using lookup_eq_Some_iff[of vo kvs m ks, OF invar]
  apply (cases ks)
    apply auto[]
  apply (auto split: option.split)
  by auto
*)

subsection \<open>@{const insert_hashtrie}\<close>
lemma isin_hashtrie_case: "isin_hashtrie xs (Nd b kst m) =
  (case xs of
   [] \<Rightarrow> (case b of None \<Rightarrow> False| b\<Rightarrow>True) |
   x # ys \<Rightarrow> (case m x of None \<Rightarrow> False | Some t \<Rightarrow> isin_hashtrie ys t))"
  apply(cases xs)
  by(cases b)auto

lemma set_insert_key: "set_hashtrie (insert_key_hashtrie xs f t) = set_hashtrie t \<union> {xs}"
  apply (induction xs f t rule: insert_key_hashtrie.induct)
  apply(auto simp: isin_hashtrie_case split!: if_splits option.splits list.splits)
  by (smt (verit, del_insts) case_optionE empty_hashtrie_def insert_Collect 
       isin_hashtrie.elims(2) mem_Collect_eq option.distinct(1) hashtrie.inject)+

theorem set_insert:"set_hashtrie (insert_hashtrie xs v t) = set_hashtrie t \<union> {xs}"
  by(simp only:insert_hashtrie_def set_insert_key)

lemma update_not_empty: "\<not> is_empty_hashtrie (insert_hashtrie ks v t)"
  apply(cases t)
  apply(cases ks)
  apply(case_tac [2] x2)
  apply (auto simp:insert_hashtrie_Nil insert_hashtrie_Cons)
  done

theorem invar_insert: "invar_hashtrie t \<Longrightarrow> invar_hashtrie (insert_hashtrie ks v t)"
  apply(induct ks t rule: insert_hashtrie_induct)
  apply (simp add:insert_hashtrie_Nil)
  apply (auto simp : insert_hashtrie_Cons set_update_with_aux
         update_not_empty option.discI split: option.splits)
  using eq_key_imp_eq_value by fastforce+

subsection \<open>@{const delete_hashtrie}\<close>
lemma delete_eq_empty_lookup_other_fail:
  "\<lbrakk> delete_hashtrie ks t = Nd None [] (\<lambda>_. None); ks' \<noteq> ks \<rbrakk> \<Longrightarrow> lookup_hashtrie t ks' = None"
proof(induct ks t arbitrary: ks' rule: delete_hashtrie.induct)
  case 1 thus ?case by(auto simp add: neq_Nil_conv)
next
  case (2 k ks vo ts m)
  show ?case
  proof(cases "m k")
    case (Some t)
    show ?thesis
    proof(cases ks')
      case (Cons k' ks'')
      show ?thesis
      proof(cases "k' = k")
        case False
        from Some Cons "2.prems"(1) have "m(k := None) = (\<lambda>_. None)"
          by(clarsimp simp add: Let_def split: if_split_asm)
        with False have "m k' = None"
          by (metis fun_upd_def)
        thus ?thesis using False Some Cons "2.prems"(1) by simp
      next
        case True
        with Some "2.prems" Cons show ?thesis
          by(clarsimp simp add: "2.hyps" Let_def is_empty_conv split: if_split_asm)
      qed
    qed(insert Some "2.prems"(1), simp add: Let_def split: if_split_asm)
  next
    case None thus ?thesis using "2.prems"(1) by simp
  qed
qed

lemma lookup_delete: "invar_hashtrie t \<Longrightarrow>
  lookup_hashtrie (delete_hashtrie ks t) ks' =
  (if ks = ks' then None else lookup_hashtrie t ks')"
proof(induct ks t arbitrary: ks' rule: delete_hashtrie.induct)
  case 1 show ?case by(fastforce dest: not_sym simp add: neq_Nil_conv)
next
  case (2 k ks vo ts m)
  show ?case
  proof(cases ks')
    case Nil thus ?thesis by(simp split: option.split add: Let_def)
  next
    case [simp]: (Cons k' ks'')
    show ?thesis
    proof(cases "k' = k")
      case False thus ?thesis using "2.prems"
        apply(auto split: option.split)
         apply(auto simp add: Let_def option.discI)
        using eq_key_imp_eq_value apply fastforce
        by force
    next
      case [simp]: True
      show ?thesis
      proof(cases "m k")
        case None thus ?thesis by simp
      next
        case (Some t)
        thus ?thesis 
        proof(cases "is_empty_hashtrie (delete_hashtrie ks t)")
          case True
          with  Some  show ?thesis
            apply simp
             apply(auto simp add: is_empty_conv)
            apply(auto dest: delete_eq_empty_lookup_other_fail)
            done
        next
          case False
          thus ?thesis using Some  2
            by (simp(no_asm_simp) add:Let_def)(auto simp add: Let_def)
        qed
      qed
    qed
  qed
qed

theorem set_delete: "set_hashtrie (delete_hashtrie xs t) = set_hashtrie t - {xs}"
  apply (induction xs t rule: delete_hashtrie.induct)
  apply(simp add: isin_hashtrie_case Let_def split!: if_splits option.splits list.splits)+
  using ehashtrie_eq_eset by fastforce+

lemma lookup_delete':
  "invar_hashtrie t \<Longrightarrow> lookup_hashtrie (delete_hashtrie ks t) = (lookup_hashtrie t)(ks := None)"
  by(rule ext)(simp add: lookup_delete)

theorem invar_delete:"invar_hashtrie t \<Longrightarrow> invar_hashtrie (delete_hashtrie ks t)"
proof(induct ks t rule: delete_hashtrie.induct)
  case 1 thus ?case by simp
next
  case (2 k ks vo ts m)
  show ?case
  proof(cases "m k")
    case None
    thus ?thesis using "2.prems" by simp
  next
    case (Some t)
    with "2.prems" have "invar_hashtrie t" by auto
    with Some have "invar_hashtrie (delete_hashtrie ks t)" by(rule 2)
    from "2.prems" Some have distinct: "distinct (map fst ts)" "\<not> is_empty_hashtrie t" by auto
    show ?thesis
    proof(cases "is_empty_hashtrie (delete_hashtrie ks t)")
      case True
      with "2.prems" have invar_empty_shashtrie:"invar_hashtrie (Nd vo (AList.delete_aux k ts) (m(k := None)))"
        by simp (smt (verit) distinct_delete_aux fst_conv graph_fun_upd_None 
           graph_map_of_if_distinct_dom map_of_delete_aux' mem_Collect_eq)
      thus ?thesis using Some "2.prems" True  by (simp add: Some)
        next             
      case False
      {  fix k' t'
        assume k't':"(k', t') \<in> set (AList.update k (delete_hashtrie ks t) ts)"
        hence "map_of (AList.update k (delete_hashtrie ks t) ts) k' = Some t'"
          using "2.prems" by(auto simp add: distinct_update)
        hence map_eq_list: "((map_of ts)(k \<mapsto> delete_hashtrie ks t)) k' = Some t'" unfolding update_conv .
        have invar_nempty_shashtrie:"\<not> is_empty_hashtrie t' \<and> invar_hashtrie t'"
        proof(cases "k' = k")
          case True
          with map_eq_list have "t' = delete_hashtrie ks t" by simp
          with \<open>invar_hashtrie (delete_hashtrie ks t)\<close> False
          show ?thesis by simp
        next
          case False
          with map_eq_list distinct have "(k', t') \<in> set ts" by simp
          with "2.prems" show ?thesis by auto
        qed }
      thus ?thesis using Some "2.prems" False apply simp
        by (smt (verit) Some case_prodI2 distinct_update fun_upd_apply invar_hashtrie.elims(3) option.simps(5) hashtrie.inject update_conv')
qed qed qed
        (*update*)
end