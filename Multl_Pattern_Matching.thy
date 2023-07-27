theory Multl_Pattern_Matching
  imports HashTrie HashTrie_TM
begin
(*---------------------------Multi-pattern matching based on HashTrie---------------------------*)
primrec hashtrie_automata::"('a list * 'v) list \<Rightarrow> ('a,'v) hashtrie \<Rightarrow> ('a,'v) hashtrie"
  where"hashtrie_automata [] t = t"|
       "hashtrie_automata (x#xs) t = hashtrie_automata xs (insert_hashtrie (fst x) (snd x) t)"

primrec hashtrie_match::"'a list \<Rightarrow>  ('a,'v) hashtrie \<Rightarrow> 'v list  \<Rightarrow> 'v list"
  where"hashtrie_match [] t vs = vs"|
       "hashtrie_match (x#xs) t vs = (case text_in_hashtrie t (x#xs) of None \<Rightarrow> hashtrie_match xs t vs|
                                                                    Some b \<Rightarrow> hashtrie_match xs t (vs@[b]))"

fun text_in_hashtrie_tm::"('a,'v) hashtrie \<Rightarrow> 'a list \<Rightarrow> 'v option tm"
  where"text_in_hashtrie_tm (Nd b _ _) [] =1 return b"|
       "text_in_hashtrie_tm (Nd b kts m) (x#xs) =1
             (if b = None then (case m x of None \<Rightarrow> return None | 
                                          Some t \<Rightarrow> text_in_hashtrie_tm t xs)
                          else return b)"

fun hashtrie_match_tm::"'a list \<Rightarrow>  ('a,'v) hashtrie \<Rightarrow> 'v list  \<Rightarrow> 'v list tm"
  where"hashtrie_match_tm [] t vs =1 return vs"|
       "hashtrie_match_tm (x#xs) t vs =1 
                   do { v \<leftarrow> text_in_hashtrie_tm t (x#xs);
                        case v of None \<Rightarrow> hashtrie_match_tm xs t vs|
                                  Some b \<Rightarrow> hashtrie_match_tm xs t (vs@[b]) }"  

definition V_hashtrie_match :: "'a list \<Rightarrow>  ('a,'v) hashtrie \<Rightarrow> 'v list  \<Rightarrow> 'v list" where
"V_hashtrie_match xs t vs = val(hashtrie_match_tm xs t vs)"

definition T_hashtrie_match :: "'a list \<Rightarrow>  ('a,'v) hashtrie \<Rightarrow> 'v list  \<Rightarrow> nat" where
"T_hashtrie_match xs t vs = time(hashtrie_match_tm xs t vs)"

(*-----------------------------Multi-pattern matching based on Trie-----------------------------*)
primrec trie_automata::"('k list * 'v) list \<Rightarrow> ('k, 'v) trie \<Rightarrow> ('k, 'v) trie"
  where"trie_automata [] t = t"|
       "trie_automata (k#ks) t = trie_automata ks (update_trie (fst k) (snd k) t)"

fun text_in_trie::"('k,'v) trie \<Rightarrow> 'k list \<Rightarrow> 'v option"
  where"text_in_trie (Trie v kts) [] = v"|
       "text_in_trie (Trie v kts) (k#ks) = 
             (if v = None then (case map_of kts k of None \<Rightarrow> None|
                                                     Some st \<Rightarrow> text_in_trie st ks)
                          else v)"

primrec trie_match::"'k list \<Rightarrow> ('k,'v) trie \<Rightarrow> 'v list \<Rightarrow> 'v list"
  where"trie_match [] t vs = vs"|
       "trie_match (k#ks) t vs = (case text_in_trie t (k#ks) of None \<Rightarrow> trie_match ks t vs|
                                                                    Some b \<Rightarrow> trie_match ks t (vs@[b]))"

fun text_in_trie_tm::"('k,'v) trie \<Rightarrow> 'k list \<Rightarrow> 'v option tm"
  where"text_in_trie_tm (Trie v kts) [] =1 return v"|
       "text_in_trie_tm (Trie v kts) (k#ks) =1
             (if v = None then do{ s_t \<leftarrow> map_of_tm kts k;
                                    case s_t of None \<Rightarrow> return None|
                                                Some st \<Rightarrow> text_in_trie_tm st ks}
                          else return v)"

fun trie_match_tm::"'k list \<Rightarrow>  ('k,'v) trie \<Rightarrow> 'v list  \<Rightarrow> 'v list tm"
  where"trie_match_tm [] t vs =1 return vs"|
       "trie_match_tm (x#xs) t vs =1 
                   do { v \<leftarrow> text_in_trie_tm t (x#xs);
                        case v of None \<Rightarrow> trie_match_tm xs t vs|
                                  Some b \<Rightarrow> trie_match_tm xs t (vs@[b]) }"   


definition V_trie_match :: "'k list \<Rightarrow>  ('k,'v) trie \<Rightarrow> 'v list  \<Rightarrow> 'v list" where
"V_trie_match xs t vs = val(trie_match_tm xs t vs)"

definition T_trie_match :: "'k list \<Rightarrow>  ('k,'v) trie \<Rightarrow> 'v list  \<Rightarrow> nat" where
"T_trie_match xs t vs = time(trie_match_tm xs t vs)"





(*----------------------------------------------case 1-------------------------------------------------------*)
definition "Ttree1 = trie_automata [([109::nat,97,110],''man''),
                                    ([112,101,111,112,108,101],''people''),
                                    ([112,101,114,115,111,110],''person'')] empty_trie"
definition "HTtree1 = hashtrie_automata [([109::nat,97,110],''man''),
                                         ([112,101,111,112,108,101],''people''),
                                         ([112,101,114,115,111,110],''person'')] empty_hashtrie"
(*Search in text "man"*)
value "trie_match_tm [109::nat,97,110] Ttree1 []"
value "hashtrie_match_tm [109::nat,97,110] HTtree1 []"
(*Search in text "kind"*)
value "trie_match_tm [107,105,110,100] Ttree1 []"
value "hashtrie_match_tm [107,105,110,100] HTtree1 []"
(*Search in text "agree"*)
value "trie_match_tm [97,103,114,101,101] Ttree1 []"
value "hashtrie_match_tm [97,103,114,101,101] HTtree1 []"
(*Search in text "happen"*)
value "trie_match_tm [104,97,112,112,101,110] Ttree1 []"
value "hashtrie_match_tm [104,97,112,112,101,110] HTtree1 []"
(*Search in text "people"*)
value "trie_match_tm [112::nat,101,111,112,108,101] Ttree1 []"
value "hashtrie_match_tm [112::nat,101,111,112,108,101] HTtree1 []"
(*Search in text "person"*)
value "trie_match_tm [112::nat,101,114,115,111,110] Ttree1 []"
value "hashtrie_match_tm [112::nat,101,114,115,111,110] HTtree1 []"
(*Search in text "account"*)
value "trie_match_tm [97,99,99,111,117,110,116] Ttree1 []"
value "hashtrie_match_tm [97,99,99,111,117,110,116] HTtree1 []"
(*Search in text "kindness"*)
value "trie_match_tm [107,105,110,100,110,101,115,115] Ttree1 []"
value "hashtrie_match_tm [107,105,110,100,110,101,115,115] HTtree1 []"
(*Search in text "announce"*)
value "trie_match_tm [97,110,110,111,117,110,99,101] Ttree1 []"
value "hashtrie_match_tm [97,110,110,111,117,110,99,101] HTtree1 []"
(*Search in text "anonymous"*)
value "trie_match_tm [97,110,111,110,121,109,111,117,115] Ttree1 []"
value "hashtrie_match_tm [97,110,111,110,121,109,111,117,115] HTtree1 []"
(*Search in text "individual"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108] Ttree1 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108] HTtree1 []"
(*Search in text "individual people"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,111,112,108,101] Ttree1 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,111,112,108,101] HTtree1 []"
(*Search in text "individual person"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,114,115,111,110] Ttree1 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,114,115,111,110] HTtree1 []"
(*Search in text "the quality of being kind"*)
value "trie_match_tm [116,104,101,32,113,117,97,108,105,116,121,32,111,102,32,98,101,105,110,103,32,107,105,110,100] Ttree1 []"
value "hashtrie_match_tm [116,104,101,32,113,117,97,108,105,116,121,32,111,102,32,98,101,105,110,103,32,107,105,110,100] HTtree1 []"
(*Search in text "We finally agreed a deal."*)
value "trie_match_tm [87,101,32,102,105,110,97,108,108,121,32,97,103,114,101,101,100,32,97,32,100,101,97,108,46] Ttree1 []"
value "hashtrie_match_tm [87,101,32,102,105,110,97,108,108,121,32,97,103,114,101,101,100,32,97,32,100,101,97,108,46] HTtree1 []"
(*Search in text "Be persistent - don't give up."*)
value "trie_match_tm [66,101,32,112,101,114,115,105,115,116,101,110,116,32,45,32,100,111,110,39,116,32,103,105,118,101,32,117,112,46] Ttree1 []"
value "hashtrie_match_tm [66,101,32,112,101,114,115,105,115,116,101,110,116,32,45,32,100,111,110,39,116,32,103,105,118,101,32,117,112,46] HTtree1 []"
(*Search in text "He has a rather anonymous face."*)
value "trie_match_tm [72,101,32,104,97,115,32,97,32,114,97,116,104,101,114,32,97,110,111,110,121,109,111,117,115,32,102,97,99,101,46] Ttree1 []"
value "hashtrie_match_tm [72,101,32,104,97,115,32,97,32,114,97,116,104,101,114,32,97,110,111,110,121,109,111,117,115,32,102,97,99,101,46] HTtree1 []"
(*Search in text "The school is noted for its academic excellence."*)
value "trie_match_tm [84,104,101,32,115,99,104,111,111,108,32,105,115,32,110,111,116,101,100,32,102,111,114,32,105,116,115,32,97,99,97,100,
                      101,109,105,99,32,101,120,99,101,108,108,101,110,99,101,46] Ttree1 []"
value "hashtrie_match_tm [84,104,101,32,115,99,104,111,111,108,32,105,115,32,110,111,116,101,100,32,102,111,114,32,105,116,115,32,97,99,97,
                          100,101,109,105,99,32,101,120,99,101,108,108,101,110,99,101,46] HTtree1 []"
(*Search in text "Now consider what happens if learning plays a role."*)
value "trie_match_tm [78,111,119,32,99,111,110,115,105,100,101,114,32,119,104,97,116,32,104,97,112,112,101,110,115,32,105,102,32,108,101,97,
                      114,110,105,110,103,32,112,108,97,121,115,32,97,32,114,111,108,101,46] Ttree1 []"
value "hashtrie_match_tm [78,111,119,32,99,111,110,115,105,100,101,114,32,119,104,97,116,32,104,97,112,112,101,110,115,32,105,102,32,108,101,97,
                      114,110,105,110,103,32,112,108,97,121,115,32,97,32,114,111,108,101,46] HTtree1 []"
(*Search in text "She gave a thrilling account of her life in the jungle."*)
value "trie_match_tm [83,104,101,32,103,97,118,101,32,97,32,116,104,114,105,108,108,105,110,103,32,97,99,99,111,117,110,116,32,111,102,32,
                      104,101,114,32,108,105,102,101,32,105,110,32,116,104,101,32,106,117,110,103,108,101,46] Ttree1 []"
value "hashtrie_match_tm [83,104,101,32,103,97,118,101,32,97,32,116,104,114,105,108,108,105,110,103,32,97,99,99,111,117,110,116,32,111,102,32,
                      104,101,114,32,108,105,102,101,32,105,110,32,116,104,101,32,106,117,110,103,108,101,46] HTtree1 []"
(*Search in text "He tackled the problem in a typically haphazard manner."*)
value "trie_match_tm [72,101,32,116,97,99,107,108,101,100,32,116,104,101,32,112,114,111,98,108,101,109,32,105,110,32,97,32,116,121,112,105,
                      99,97,108,108,121,32,104,97,112,104,97,122,97,114,100,32,109,97,110,110,101,114,46] Ttree1 []"
value "hashtrie_match_tm [72,101,32,116,97,99,107,108,101,100,32,116,104,101,32,112,114,111,98,108,101,109,32,105,110,32,97,32,116,121,112,
                          105,99,97,108,108,121,32,104,97,112,104,97,122,97,114,100,32,109,97,110,110,101,114,46] HTtree1 []"
(*Search in text "anonymous kindnesses should be flushed out and announced."*)
value "trie_match_tm [97,110,111,110,121,109,111,117,115,32,107,105,110,100,110,101,115,115,101,115,32,115,104,111,117,108,100,32,98,
                      101,32,102,108,117,115,104,101,100,32,111,117,116,32,97,110,110,111,117,110,99,101,100,46] Ttree1 []"
value "hashtrie_match_tm [97,110,111,110,121,109,111,117,115,32,107,105,110,100,110,101,115,115,101,115,32,115,104,111,117,108,100,32,
                          98,101,32,102,108,117,115,104,101,100,32,111,117,116,32,97,110,110,111,117,110,99,101,100,46] HTtree1 []"
(*Search in text "We have five accounts of what happened and none of them agree."*)
value "trie_match_tm [87,101,32,104,97,118,101,32,102,105,118,101,32,97,99,99,111,117,110,116,115,32,111,102,32,119,104,97,116,32,104,97,112,
                      112,101,110,101,100,32,97,110,100,32,110,111,110,101,32,111,102,32,116,104,101,109,32,97,103,114,101,101,46] Ttree1 []"
value "hashtrie_match_tm [87,101,32,104,97,118,101,32,102,105,118,101,32,97,99,99,111,117,110,116,115,32,111,102,32,119,104,97,116,32,104,97,
                          112,112,101,110,101,100,32,97,110,100,32,110,111,110,101,32,111,102,32,116,104,101,109,32,97,103,114,101,101,46] HTtree1 []"
(*Search in text "The first few leaves in the gutter announced the beginning of autumn."*)
value "trie_match_tm [84,104,101,32,102,105,114,115,116,32,102,101,119,32,108,101,97,118,101,115,32,105,110,32,116,104,101,32,103,117,
                      116,116,101,114,32,97,110,110,111,117,110,99,101,100,32,116,104,101,32,98,101,103,105,110,110,105,110,32,111,102,
                      32,97,117,116,117,109,110,46] Ttree1 []"
value "hashtrie_match_tm [84,104,101,32,102,105,114,115,116,32,102,101,119,32,108,101,97,118,101,115,32,105,110,32,116,104,101,32,103,
                          117,116,116,101,114,32,97,110,110,111,117,110,99,101,100,32,116,104,101,32,98,101,103,105,110,110,105,110,32,
                          111,102,32,97,117,116,117,109,110,46] HTtree1 []"
(*Search in text "He's nice enough as a person, but he's not the right man for this job."*)
value "trie_match_tm [72::nat,101,39,115,32,110,105,99,101,32,101,110,111,117,103,104,32,97,115,32,97,32,112,101,114,115,111,110,44,32,
                      98,117,116,32,104,101,39,115,32,110,111,116,32,116,104,101,32,114,105,103,104,116,32,109,97,110,32,102,111,114,32,
                      116,104,105,115,32,106,111,98,46] Ttree1 []"
value "hashtrie_match_tm [72::nat,101,39,115,32,110,105,99,101,32,101,110,111,117,103,104,32,97,115,32,97,32,112,101,114,115,111,110,44,32,
                          98,117,116,32,104,101,39,115,32,110,111,116,32,116,104,101,32,114,105,103,104,116,32,109,97,110,32,102,111,114,32,
                          116,104,105,115,32,106,111,98,46] HTtree1 []"
(*Search in text "The new translation of the Latin work includes extensive annotation by scholars."*)
value "trie_match_tm [84,104,101,32,110,101,119,32,116,114,97,110,115,108,97,116,105,111,110,32,111,102,32,116,104,101,32,76,97,116,105,
                      110,32,119,111,114,107,32,105,110,99,108,117,100,101,115,32,101,120,116,101,110,115,105,118,101,32,97,110,110,111,
                      116,97,116,105,111,110,32,98,121,32,115,99,104,111,108,97,114,115,46] Ttree1 []"
value "hashtrie_match_tm [84,104,101,32,110,101,119,32,116,114,97,110,115,108,97,116,105,111,110,32,111,102,32,116,104,101,32,76,97,116,
                          105,110,32,119,111,114,107,32,105,110,99,108,117,100,101,115,32,101,120,116,101,110,115,105,118,101,32,97,110,
                          110,111,116,97,116,105,111,110,32,98,121,32,115,99,104,111,108,97,114,115,46] HTtree1 []"
(*Search in text "Three people were interviewed for the job, but only one person had the right qualifications"*)
value "trie_match_tm [84::nat,104,114,101,101,32,112,101,111,112,108,101,32,119,101,114,101,32,105,110,116,101,114,118,105,101,119,101,
                      100,32,102,111,114,32,116,104,101,32,106,111,98,44,32,98,117,116,32,111,110,108,121,32,111,110,101,32,112,101,114,
                      115,111,110,32,104,97,100,32,116,104,101,32,114,105,103,104,116,32,113,117,97,108,105,102,105,99,97,116,105,111,110,115] Ttree1 []"
value "hashtrie_match_tm [84::nat,104,114,101,101,32,112,101,111,112,108,101,32,119,101,114,101,32,105,110,116,101,114,118,105,101,119,101,
                      100,32,102,111,114,32,116,104,101,32,106,111,98,44,32,98,117,116,32,111,110,108,121,32,111,110,101,32,112,101,114,
                      115,111,110,32,104,97,100,32,116,104,101,32,114,105,103,104,116,32,113,117,97,108,105,102,105,99,97,116,105,111,110,115] HTtree1 []"

(*----------------------------------------------case 2-------------------------------------------------------*)
definition "Ttree2 = trie_automata [([97::nat,110,111,110,121,109,111,117,115],''anonymous''),
                                    ([107,105,110,100,110,101,115,115],''kindness''),
                                    ([97,110,110,111,117,110,99,101],''announce'')] empty_trie"
definition "HTtree2 = hashtrie_automata [([97::nat,110,111,110,121,109,111,117,115],''anonymous''),
                                         ([107,105,110,100,110,101,115,115],''kindness''),
                                         ([97,110,110,111,117,110,99,101],''announce'')] empty_hashtrie"
(*Search in text "man"*)
value "trie_match_tm [109::nat,97,110] Ttree2 []"
value "hashtrie_match_tm [109::nat,97,110] HTtree2 []"
(*Search in text "kind"*)
value "trie_match_tm [107,105,110,100] Ttree2 []"
value "hashtrie_match_tm [107,105,110,100] HTtree2 []"
(*Search in text "agree"*)
value "trie_match_tm [97,103,114,101,101] Ttree2 []"
value "hashtrie_match_tm [97,103,114,101,101] HTtree2 []"
(*Search in text "happen"*)
value "trie_match_tm [104,97,112,112,101,110] Ttree2 []"
value "hashtrie_match_tm [104,97,112,112,101,110] HTtree2 []"
(*Search in text "people"*)
value "trie_match_tm [112::nat,101,111,112,108,101] Ttree2 []"
value "hashtrie_match_tm [112::nat,101,111,112,108,101] HTtree2 []"
(*Search in text "person"*)
value "trie_match_tm [112::nat,101,114,115,111,110] Ttree2 []"
value "hashtrie_match_tm [112::nat,101,114,115,111,110] HTtree2 []"
(*Search in text "account"*)
value "trie_match_tm [97,99,99,111,117,110,116] Ttree2 []"
value "hashtrie_match_tm [97,99,99,111,117,110,116] HTtree2 []"
(*Search in text "kindness"*)
value "trie_match_tm [107,105,110,100,110,101,115,115] Ttree2 []"
value "hashtrie_match_tm [107,105,110,100,110,101,115,115] HTtree2 []"
(*Search in text "announce"*)
value "trie_match_tm [97,110,110,111,117,110,99,101] Ttree2 []"
value "hashtrie_match_tm [97,110,110,111,117,110,99,101] HTtree2 []"
(*Search in text "anonymous"*)
value "trie_match_tm [97,110,111,110,121,109,111,117,115] Ttree2 []"
value "hashtrie_match_tm [97,110,111,110,121,109,111,117,115] HTtree2 []"
(*Search in text "individual"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108] Ttree2 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108] HTtree2 []"
(*Search in text "individual people"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,111,112,108,101] Ttree2 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,111,112,108,101] HTtree2 []"
(*Search in text "individual person"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,114,115,111,110] Ttree2 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,114,115,111,110] HTtree2 []"
(*Search in text "the quality of being kind"*)
value "trie_match_tm [116,104,101,32,113,117,97,108,105,116,121,32,111,102,32,98,101,105,110,103,32,107,105,110,100] Ttree2 []"
value "hashtrie_match_tm [116,104,101,32,113,117,97,108,105,116,121,32,111,102,32,98,101,105,110,103,32,107,105,110,100] HTtree2 []"
(*Search in text "We finally agreed a deal."*)
value "trie_match_tm [87,101,32,102,105,110,97,108,108,121,32,97,103,114,101,101,100,32,97,32,100,101,97,108,46] Ttree2 []"
value "hashtrie_match_tm [87,101,32,102,105,110,97,108,108,121,32,97,103,114,101,101,100,32,97,32,100,101,97,108,46] HTtree2 []"
(*Search in text "Be persistent - don't give up."*)
value "trie_match_tm [66,101,32,112,101,114,115,105,115,116,101,110,116,32,45,32,100,111,110,39,116,32,103,105,118,101,32,117,112,46] Ttree2 []"
value "hashtrie_match_tm [66,101,32,112,101,114,115,105,115,116,101,110,116,32,45,32,100,111,110,39,116,32,103,105,118,101,32,117,112,46] HTtree2 []"
(*Search in text "He has a rather anonymous face."*)
value "trie_match_tm [72,101,32,104,97,115,32,97,32,114,97,116,104,101,114,32,97,110,111,110,121,109,111,117,115,32,102,97,99,101,46] Ttree2 []"
value "hashtrie_match_tm [72,101,32,104,97,115,32,97,32,114,97,116,104,101,114,32,97,110,111,110,121,109,111,117,115,32,102,97,99,101,46] HTtree2 []"
(*Search in text "The school is noted for its academic excellence."*)
value "trie_match_tm [84,104,101,32,115,99,104,111,111,108,32,105,115,32,110,111,116,101,100,32,102,111,114,32,105,116,115,32,97,99,97,100,
                      101,109,105,99,32,101,120,99,101,108,108,101,110,99,101,46] Ttree2 []"
value "hashtrie_match_tm [84,104,101,32,115,99,104,111,111,108,32,105,115,32,110,111,116,101,100,32,102,111,114,32,105,116,115,32,97,99,97,
                          100,101,109,105,99,32,101,120,99,101,108,108,101,110,99,101,46] HTtree2 []"
(*Search in text "Now consider what happens if learning plays a role."*)
value "trie_match_tm [78,111,119,32,99,111,110,115,105,100,101,114,32,119,104,97,116,32,104,97,112,112,101,110,115,32,105,102,32,108,101,97,
                      114,110,105,110,103,32,112,108,97,121,115,32,97,32,114,111,108,101,46] Ttree2 []"
value "hashtrie_match_tm [78,111,119,32,99,111,110,115,105,100,101,114,32,119,104,97,116,32,104,97,112,112,101,110,115,32,105,102,32,108,101,97,
                      114,110,105,110,103,32,112,108,97,121,115,32,97,32,114,111,108,101,46] HTtree2 []"
(*Search in text "She gave a thrilling account of her life in the jungle."*)
value "trie_match_tm [83,104,101,32,103,97,118,101,32,97,32,116,104,114,105,108,108,105,110,103,32,97,99,99,111,117,110,116,32,111,102,32,
                      104,101,114,32,108,105,102,101,32,105,110,32,116,104,101,32,106,117,110,103,108,101,46] Ttree2 []"
value "hashtrie_match_tm [83,104,101,32,103,97,118,101,32,97,32,116,104,114,105,108,108,105,110,103,32,97,99,99,111,117,110,116,32,111,102,32,
                      104,101,114,32,108,105,102,101,32,105,110,32,116,104,101,32,106,117,110,103,108,101,46] HTtree2 []"
(*Search in text "He tackled the problem in a typically haphazard manner."*)
value "trie_match_tm [72,101,32,116,97,99,107,108,101,100,32,116,104,101,32,112,114,111,98,108,101,109,32,105,110,32,97,32,116,121,112,105,
                      99,97,108,108,121,32,104,97,112,104,97,122,97,114,100,32,109,97,110,110,101,114,46] Ttree2 []"
value "hashtrie_match_tm [72,101,32,116,97,99,107,108,101,100,32,116,104,101,32,112,114,111,98,108,101,109,32,105,110,32,97,32,116,121,112,
                          105,99,97,108,108,121,32,104,97,112,104,97,122,97,114,100,32,109,97,110,110,101,114,46] HTtree2 []"
(*Search in text "anonymous kindnesses should be flushed out and announced."*)
value "trie_match_tm [97,110,111,110,121,109,111,117,115,32,107,105,110,100,110,101,115,115,101,115,32,115,104,111,117,108,100,32,98,
                      101,32,102,108,117,115,104,101,100,32,111,117,116,32,97,110,110,111,117,110,99,101,100,46] Ttree2 []"
value "hashtrie_match_tm [97,110,111,110,121,109,111,117,115,32,107,105,110,100,110,101,115,115,101,115,32,115,104,111,117,108,100,32,
                          98,101,32,102,108,117,115,104,101,100,32,111,117,116,32,97,110,110,111,117,110,99,101,100,46] HTtree2 []"
(*Search in text "We have five accounts of what happened and none of them agree."*)
value "trie_match_tm [87,101,32,104,97,118,101,32,102,105,118,101,32,97,99,99,111,117,110,116,115,32,111,102,32,119,104,97,116,32,104,97,112,
                      112,101,110,101,100,32,97,110,100,32,110,111,110,101,32,111,102,32,116,104,101,109,32,97,103,114,101,101,46] Ttree2 []"
value "hashtrie_match_tm [87,101,32,104,97,118,101,32,102,105,118,101,32,97,99,99,111,117,110,116,115,32,111,102,32,119,104,97,116,32,104,97,
                          112,112,101,110,101,100,32,97,110,100,32,110,111,110,101,32,111,102,32,116,104,101,109,32,97,103,114,101,101,46] HTtree2 []"
(*Search in text "The first few leaves in the gutter announced the beginning of autumn."*)
value "trie_match_tm [84,104,101,32,102,105,114,115,116,32,102,101,119,32,108,101,97,118,101,115,32,105,110,32,116,104,101,32,103,117,
                      116,116,101,114,32,97,110,110,111,117,110,99,101,100,32,116,104,101,32,98,101,103,105,110,110,105,110,32,111,102,
                      32,97,117,116,117,109,110,46] Ttree2 []"
value "hashtrie_match_tm [84,104,101,32,102,105,114,115,116,32,102,101,119,32,108,101,97,118,101,115,32,105,110,32,116,104,101,32,103,
                          117,116,116,101,114,32,97,110,110,111,117,110,99,101,100,32,116,104,101,32,98,101,103,105,110,110,105,110,32,
                          111,102,32,97,117,116,117,109,110,46] HTtree2 []"
(*Search in text "He's nice enough as a person, but he's not the right man for this job."*)
value "trie_match_tm [72::nat,101,39,115,32,110,105,99,101,32,101,110,111,117,103,104,32,97,115,32,97,32,112,101,114,115,111,110,44,32,
                      98,117,116,32,104,101,39,115,32,110,111,116,32,116,104,101,32,114,105,103,104,116,32,109,97,110,32,102,111,114,32,
                      116,104,105,115,32,106,111,98,46] Ttree2 []"
value "hashtrie_match_tm [72::nat,101,39,115,32,110,105,99,101,32,101,110,111,117,103,104,32,97,115,32,97,32,112,101,114,115,111,110,44,32,
                          98,117,116,32,104,101,39,115,32,110,111,116,32,116,104,101,32,114,105,103,104,116,32,109,97,110,32,102,111,114,32,
                          116,104,105,115,32,106,111,98,46] HTtree2 []"
(*Search in text "The new translation of the Latin work includes extensive annotation by scholars."*)
value "trie_match_tm [84,104,101,32,110,101,119,32,116,114,97,110,115,108,97,116,105,111,110,32,111,102,32,116,104,101,32,76,97,116,105,
                      110,32,119,111,114,107,32,105,110,99,108,117,100,101,115,32,101,120,116,101,110,115,105,118,101,32,97,110,110,111,
                      116,97,116,105,111,110,32,98,121,32,115,99,104,111,108,97,114,115,46] Ttree2 []"
value "hashtrie_match_tm [84,104,101,32,110,101,119,32,116,114,97,110,115,108,97,116,105,111,110,32,111,102,32,116,104,101,32,76,97,116,
                          105,110,32,119,111,114,107,32,105,110,99,108,117,100,101,115,32,101,120,116,101,110,115,105,118,101,32,97,110,
                          110,111,116,97,116,105,111,110,32,98,121,32,115,99,104,111,108,97,114,115,46] HTtree2 []"
(*Search in text "Three people were interviewed for the job, but only one person had the right qualifications"*)
value "trie_match_tm [84::nat,104,114,101,101,32,112,101,111,112,108,101,32,119,101,114,101,32,105,110,116,101,114,118,105,101,119,101,
                      100,32,102,111,114,32,116,104,101,32,106,111,98,44,32,98,117,116,32,111,110,108,121,32,111,110,101,32,112,101,114,
                      115,111,110,32,104,97,100,32,116,104,101,32,114,105,103,104,116,32,113,117,97,108,105,102,105,99,97,116,105,111,110,115] Ttree2 []"
value "hashtrie_match_tm [84::nat,104,114,101,101,32,112,101,111,112,108,101,32,119,101,114,101,32,105,110,116,101,114,118,105,101,119,101,
                      100,32,102,111,114,32,116,104,101,32,106,111,98,44,32,98,117,116,32,111,110,108,121,32,111,110,101,32,112,101,114,
                      115,111,110,32,104,97,100,32,116,104,101,32,114,105,103,104,116,32,113,117,97,108,105,102,105,99,97,116,105,111,110,115] HTtree2 []"

(*----------------------------------------------case 3-------------------------------------------------------*)
definition "Ttree3 = trie_automata [([97::nat,103,114,101,101],''agree''),
                                    ([97,99,99,111,117,110,116],''account''),
                                    ([104,97,112,112,101,110],''happen'')] empty_trie"
definition "HTtree3 = hashtrie_automata [([97::nat,103,114,101,101],''agree''),
                                         ([97,99,99,111,117,110,116],''account''),
                                         ([104,97,112,112,101,110],''happen'')] empty_hashtrie"

(*Search in text "man"*)
value "trie_match_tm [109::nat,97,110] Ttree3 []"
value "hashtrie_match_tm [109::nat,97,110] HTtree3 []"
(*Search in text "kind"*)
value "trie_match_tm [107,105,110,100] Ttree3 []"
value "hashtrie_match_tm [107,105,110,100] HTtree3 []"
(*Search in text "agree"*)
value "trie_match_tm [97,103,114,101,101] Ttree3 []"
value "hashtrie_match_tm [97,103,114,101,101] HTtree3 []"
(*Search in text "happen"*)
value "trie_match_tm [104,97,112,112,101,110] Ttree3 []"
value "hashtrie_match_tm [104,97,112,112,101,110] HTtree3 []"
(*Search in text "people"*)
value "trie_match_tm [112::nat,101,111,112,108,101] Ttree3 []"
value "hashtrie_match_tm [112::nat,101,111,112,108,101] HTtree3 []"
(*Search in text "person"*)
value "trie_match_tm [112::nat,101,114,115,111,110] Ttree3 []"
value "hashtrie_match_tm [112::nat,101,114,115,111,110] HTtree3 []"
(*Search in text "account"*)
value "trie_match_tm [97,99,99,111,117,110,116] Ttree3 []"
value "hashtrie_match_tm [97,99,99,111,117,110,116] HTtree3 []"
(*Search in text "kindness"*)
value "trie_match_tm [107,105,110,100,110,101,115,115] Ttree3 []"
value "hashtrie_match_tm [107,105,110,100,110,101,115,115] HTtree3 []"
(*Search in text "announce"*)
value "trie_match_tm [97,110,110,111,117,110,99,101] Ttree3 []"
value "hashtrie_match_tm [97,110,110,111,117,110,99,101] HTtree3 []"
(*Search in text "anonymous"*)
value "trie_match_tm [97,110,111,110,121,109,111,117,115] Ttree3 []"
value "hashtrie_match_tm [97,110,111,110,121,109,111,117,115] HTtree3 []"
(*Search in text "individual"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108] Ttree3 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108] HTtree3 []"
(*Search in text "individual people"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,111,112,108,101] Ttree3 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,111,112,108,101] HTtree3 []"
(*Search in text "individual person"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,114,115,111,110] Ttree3 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,114,115,111,110] HTtree3 []"
(*Search in text "the quality of being kind"*)
value "trie_match_tm [116,104,101,32,113,117,97,108,105,116,121,32,111,102,32,98,101,105,110,103,32,107,105,110,100] Ttree3 []"
value "hashtrie_match_tm [116,104,101,32,113,117,97,108,105,116,121,32,111,102,32,98,101,105,110,103,32,107,105,110,100] HTtree3 []"
(*Search in text "We finally agreed a deal."*)
value "trie_match_tm [87,101,32,102,105,110,97,108,108,121,32,97,103,114,101,101,100,32,97,32,100,101,97,108,46] Ttree3 []"
value "hashtrie_match_tm [87,101,32,102,105,110,97,108,108,121,32,97,103,114,101,101,100,32,97,32,100,101,97,108,46] HTtree3 []"
(*Search in text "Be persistent - don't give up."*)
value "trie_match_tm [66,101,32,112,101,114,115,105,115,116,101,110,116,32,45,32,100,111,110,39,116,32,103,105,118,101,32,117,112,46] Ttree3 []"
value "hashtrie_match_tm [66,101,32,112,101,114,115,105,115,116,101,110,116,32,45,32,100,111,110,39,116,32,103,105,118,101,32,117,112,46] HTtree3 []"
(*Search in text "He has a rather anonymous face."*)
value "trie_match_tm [72,101,32,104,97,115,32,97,32,114,97,116,104,101,114,32,97,110,111,110,121,109,111,117,115,32,102,97,99,101,46] Ttree3 []"
value "hashtrie_match_tm [72,101,32,104,97,115,32,97,32,114,97,116,104,101,114,32,97,110,111,110,121,109,111,117,115,32,102,97,99,101,46] HTtree3 []"
(*Search in text "The school is noted for its academic excellence."*)
value "trie_match_tm [84,104,101,32,115,99,104,111,111,108,32,105,115,32,110,111,116,101,100,32,102,111,114,32,105,116,115,32,97,99,97,100,
                      101,109,105,99,32,101,120,99,101,108,108,101,110,99,101,46] Ttree3 []"
value "hashtrie_match_tm [84,104,101,32,115,99,104,111,111,108,32,105,115,32,110,111,116,101,100,32,102,111,114,32,105,116,115,32,97,99,97,
                          100,101,109,105,99,32,101,120,99,101,108,108,101,110,99,101,46] HTtree3 []"
(*Search in text "Now consider what happens if learning plays a role."*)
value "trie_match_tm [78,111,119,32,99,111,110,115,105,100,101,114,32,119,104,97,116,32,104,97,112,112,101,110,115,32,105,102,32,108,101,97,
                      114,110,105,110,103,32,112,108,97,121,115,32,97,32,114,111,108,101,46] Ttree3 []"
value "hashtrie_match_tm [78,111,119,32,99,111,110,115,105,100,101,114,32,119,104,97,116,32,104,97,112,112,101,110,115,32,105,102,32,108,101,97,
                      114,110,105,110,103,32,112,108,97,121,115,32,97,32,114,111,108,101,46] HTtree3 []"
(*Search in text "She gave a thrilling account of her life in the jungle."*)
value "trie_match_tm [83,104,101,32,103,97,118,101,32,97,32,116,104,114,105,108,108,105,110,103,32,97,99,99,111,117,110,116,32,111,102,32,
                      104,101,114,32,108,105,102,101,32,105,110,32,116,104,101,32,106,117,110,103,108,101,46] Ttree3 []"
value "hashtrie_match_tm [83,104,101,32,103,97,118,101,32,97,32,116,104,114,105,108,108,105,110,103,32,97,99,99,111,117,110,116,32,111,102,32,
                      104,101,114,32,108,105,102,101,32,105,110,32,116,104,101,32,106,117,110,103,108,101,46] HTtree3 []"
(*Search in text "He tackled the problem in a typically haphazard manner."*)
value "trie_match_tm [72,101,32,116,97,99,107,108,101,100,32,116,104,101,32,112,114,111,98,108,101,109,32,105,110,32,97,32,116,121,112,105,
                      99,97,108,108,121,32,104,97,112,104,97,122,97,114,100,32,109,97,110,110,101,114,46] Ttree3 []"
value "hashtrie_match_tm [72,101,32,116,97,99,107,108,101,100,32,116,104,101,32,112,114,111,98,108,101,109,32,105,110,32,97,32,116,121,112,
                          105,99,97,108,108,121,32,104,97,112,104,97,122,97,114,100,32,109,97,110,110,101,114,46] HTtree3 []"
(*Search in text "anonymous kindnesses should be flushed out and announced."*)
value "trie_match_tm [97,110,111,110,121,109,111,117,115,32,107,105,110,100,110,101,115,115,101,115,32,115,104,111,117,108,100,32,98,
                      101,32,102,108,117,115,104,101,100,32,111,117,116,32,97,110,110,111,117,110,99,101,100,46] Ttree3 []"
value "hashtrie_match_tm [97,110,111,110,121,109,111,117,115,32,107,105,110,100,110,101,115,115,101,115,32,115,104,111,117,108,100,32,
                          98,101,32,102,108,117,115,104,101,100,32,111,117,116,32,97,110,110,111,117,110,99,101,100,46] HTtree3 []"
(*Search in text "We have five accounts of what happened and none of them agree."*)
value "trie_match_tm [87,101,32,104,97,118,101,32,102,105,118,101,32,97,99,99,111,117,110,116,115,32,111,102,32,119,104,97,116,32,104,97,112,
                      112,101,110,101,100,32,97,110,100,32,110,111,110,101,32,111,102,32,116,104,101,109,32,97,103,114,101,101,46] Ttree3 []"
value "hashtrie_match_tm [87,101,32,104,97,118,101,32,102,105,118,101,32,97,99,99,111,117,110,116,115,32,111,102,32,119,104,97,116,32,104,97,
                          112,112,101,110,101,100,32,97,110,100,32,110,111,110,101,32,111,102,32,116,104,101,109,32,97,103,114,101,101,46] HTtree3 []"
(*Search in text "The first few leaves in the gutter announced the beginning of autumn."*)
value "trie_match_tm [84,104,101,32,102,105,114,115,116,32,102,101,119,32,108,101,97,118,101,115,32,105,110,32,116,104,101,32,103,117,
                      116,116,101,114,32,97,110,110,111,117,110,99,101,100,32,116,104,101,32,98,101,103,105,110,110,105,110,32,111,102,
                      32,97,117,116,117,109,110,46] Ttree3 []"
value "hashtrie_match_tm [84,104,101,32,102,105,114,115,116,32,102,101,119,32,108,101,97,118,101,115,32,105,110,32,116,104,101,32,103,
                          117,116,116,101,114,32,97,110,110,111,117,110,99,101,100,32,116,104,101,32,98,101,103,105,110,110,105,110,32,
                          111,102,32,97,117,116,117,109,110,46] HTtree3 []"
(*Search in text "He's nice enough as a person, but he's not the right man for this job."*)
value "trie_match_tm [72::nat,101,39,115,32,110,105,99,101,32,101,110,111,117,103,104,32,97,115,32,97,32,112,101,114,115,111,110,44,32,
                      98,117,116,32,104,101,39,115,32,110,111,116,32,116,104,101,32,114,105,103,104,116,32,109,97,110,32,102,111,114,32,
                      116,104,105,115,32,106,111,98,46] Ttree3 []"
value "hashtrie_match_tm [72::nat,101,39,115,32,110,105,99,101,32,101,110,111,117,103,104,32,97,115,32,97,32,112,101,114,115,111,110,44,32,
                          98,117,116,32,104,101,39,115,32,110,111,116,32,116,104,101,32,114,105,103,104,116,32,109,97,110,32,102,111,114,32,
                          116,104,105,115,32,106,111,98,46] HTtree3 []"
(*Search in text "The new translation of the Latin work includes extensive annotation by scholars."*)
value "trie_match_tm [84,104,101,32,110,101,119,32,116,114,97,110,115,108,97,116,105,111,110,32,111,102,32,116,104,101,32,76,97,116,105,
                      110,32,119,111,114,107,32,105,110,99,108,117,100,101,115,32,101,120,116,101,110,115,105,118,101,32,97,110,110,111,
                      116,97,116,105,111,110,32,98,121,32,115,99,104,111,108,97,114,115,46] Ttree3 []"
value "hashtrie_match_tm [84,104,101,32,110,101,119,32,116,114,97,110,115,108,97,116,105,111,110,32,111,102,32,116,104,101,32,76,97,116,
                          105,110,32,119,111,114,107,32,105,110,99,108,117,100,101,115,32,101,120,116,101,110,115,105,118,101,32,97,110,
                          110,111,116,97,116,105,111,110,32,98,121,32,115,99,104,111,108,97,114,115,46] HTtree3 []"
(*Search in text "Three people were interviewed for the job, but only one person had the right qualifications"*)
value "trie_match_tm [84::nat,104,114,101,101,32,112,101,111,112,108,101,32,119,101,114,101,32,105,110,116,101,114,118,105,101,119,101,
                      100,32,102,111,114,32,116,104,101,32,106,111,98,44,32,98,117,116,32,111,110,108,121,32,111,110,101,32,112,101,114,
                      115,111,110,32,104,97,100,32,116,104,101,32,114,105,103,104,116,32,113,117,97,108,105,102,105,99,97,116,105,111,110,115] Ttree3 []"
value "hashtrie_match_tm [84::nat,104,114,101,101,32,112,101,111,112,108,101,32,119,101,114,101,32,105,110,116,101,114,118,105,101,119,101,
                      100,32,102,111,114,32,116,104,101,32,106,111,98,44,32,98,117,116,32,111,110,108,121,32,111,110,101,32,112,101,114,
                      115,111,110,32,104,97,100,32,116,104,101,32,114,105,103,104,116,32,113,117,97,108,105,102,105,99,97,116,105,111,110,115] HTtree3 []"


(*----------------------------------------------case 4-------------------------------------------------------*)
definition "Ttree4 = trie_automata [([102::nat,97,99,101],''face''),
                                    ([102,105,114,115,116],''first''),
                                    ([102,105,118,101],''five''),
                                    ([114,105,103,104,116],''right''),
                                    ([114,111,108,101],''role'')] empty_trie"
definition "HTtree4 = hashtrie_automata [([102::nat,97,99,101],''face''),
                                         ([102,105,114,115,116],''first''),
                                         ([102,105,118,101],''five''),
                                         ([114,105,103,104,116],''right''),
                                         ([114,111,108,101],''role'')] empty_hashtrie"
(*Search in text "man"*)
value "trie_match_tm [109::nat,97,110] Ttree4 []"
value "hashtrie_match_tm [109::nat,97,110] HTtree4 []"
(*Search in text "kind"*)
value "trie_match_tm [107,105,110,100] Ttree4 []"
value "hashtrie_match_tm [107,105,110,100] HTtree4 []"
(*Search in text "agree"*)
value "trie_match_tm [97,103,114,101,101] Ttree4 []"
value "hashtrie_match_tm [97,103,114,101,101] HTtree4 []"
(*Search in text "happen"*)
value "trie_match_tm [104,97,112,112,101,110] Ttree4 []"
value "hashtrie_match_tm [104,97,112,112,101,110] HTtree4 []"
(*Search in text "people"*)
value "trie_match_tm [112::nat,101,111,112,108,101] Ttree4 []"
value "hashtrie_match_tm [112::nat,101,111,112,108,101] HTtree4 []"
(*Search in text "person"*)
value "trie_match_tm [112::nat,101,114,115,111,110] Ttree4 []"
value "hashtrie_match_tm [112::nat,101,114,115,111,110] HTtree4 []"
(*Search in text "account"*)
value "trie_match_tm [97,99,99,111,117,110,116] Ttree4 []"
value "hashtrie_match_tm [97,99,99,111,117,110,116] HTtree4 []"
(*Search in text "kindness"*)
value "trie_match_tm [107,105,110,100,110,101,115,115] Ttree4 []"
value "hashtrie_match_tm [107,105,110,100,110,101,115,115] HTtree4 []"
(*Search in text "announce"*)
value "trie_match_tm [97,110,110,111,117,110,99,101] Ttree4 []"
value "hashtrie_match_tm [97,110,110,111,117,110,99,101] HTtree4 []"
(*Search in text "anonymous"*)
value "trie_match_tm [97,110,111,110,121,109,111,117,115] Ttree4 []"
value "hashtrie_match_tm [97,110,111,110,121,109,111,117,115] HTtree4 []"
(*Search in text "individual"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108] Ttree4 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108] HTtree4 []"
(*Search in text "individual people"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,111,112,108,101] Ttree4 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,111,112,108,101] HTtree4 []"
(*Search in text "individual person"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,114,115,111,110] Ttree4 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,114,115,111,110] HTtree4 []"
(*Search in text "the quality of being kind"*)
value "trie_match_tm [116,104,101,32,113,117,97,108,105,116,121,32,111,102,32,98,101,105,110,103,32,107,105,110,100] Ttree4 []"
value "hashtrie_match_tm [116,104,101,32,113,117,97,108,105,116,121,32,111,102,32,98,101,105,110,103,32,107,105,110,100] HTtree4 []"
(*Search in text "We finally agreed a deal."*)
value "trie_match_tm [87,101,32,102,105,110,97,108,108,121,32,97,103,114,101,101,100,32,97,32,100,101,97,108,46] Ttree4 []"
value "hashtrie_match_tm [87,101,32,102,105,110,97,108,108,121,32,97,103,114,101,101,100,32,97,32,100,101,97,108,46] HTtree4 []"
(*Search in text "Be persistent - don't give up."*)
value "trie_match_tm [66,101,32,112,101,114,115,105,115,116,101,110,116,32,45,32,100,111,110,39,116,32,103,105,118,101,32,117,112,46] Ttree4 []"
value "hashtrie_match_tm [66,101,32,112,101,114,115,105,115,116,101,110,116,32,45,32,100,111,110,39,116,32,103,105,118,101,32,117,112,46] HTtree4 []"
(*Search in text "He has a rather anonymous face."*)
value "trie_match_tm [72,101,32,104,97,115,32,97,32,114,97,116,104,101,114,32,97,110,111,110,121,109,111,117,115,32,102,97,99,101,46] Ttree4 []"
value "hashtrie_match_tm [72,101,32,104,97,115,32,97,32,114,97,116,104,101,114,32,97,110,111,110,121,109,111,117,115,32,102,97,99,101,46] HTtree4 []"
(*Search in text "The school is noted for its academic excellence."*)
value "trie_match_tm [84,104,101,32,115,99,104,111,111,108,32,105,115,32,110,111,116,101,100,32,102,111,114,32,105,116,115,32,97,99,97,100,
                      101,109,105,99,32,101,120,99,101,108,108,101,110,99,101,46] Ttree4 []"
value "hashtrie_match_tm [84,104,101,32,115,99,104,111,111,108,32,105,115,32,110,111,116,101,100,32,102,111,114,32,105,116,115,32,97,99,97,
                          100,101,109,105,99,32,101,120,99,101,108,108,101,110,99,101,46] HTtree4 []"
(*Search in text "Now consider what happens if learning plays a role."*)
value "trie_match_tm [78,111,119,32,99,111,110,115,105,100,101,114,32,119,104,97,116,32,104,97,112,112,101,110,115,32,105,102,32,108,101,97,
                      114,110,105,110,103,32,112,108,97,121,115,32,97,32,114,111,108,101,46] Ttree4 []"
value "hashtrie_match_tm [78,111,119,32,99,111,110,115,105,100,101,114,32,119,104,97,116,32,104,97,112,112,101,110,115,32,105,102,32,108,101,97,
                      114,110,105,110,103,32,112,108,97,121,115,32,97,32,114,111,108,101,46] HTtree4 []"
(*Search in text "She gave a thrilling account of her life in the jungle."*)
value "trie_match_tm [83,104,101,32,103,97,118,101,32,97,32,116,104,114,105,108,108,105,110,103,32,97,99,99,111,117,110,116,32,111,102,32,
                      104,101,114,32,108,105,102,101,32,105,110,32,116,104,101,32,106,117,110,103,108,101,46] Ttree4 []"
value "hashtrie_match_tm [83,104,101,32,103,97,118,101,32,97,32,116,104,114,105,108,108,105,110,103,32,97,99,99,111,117,110,116,32,111,102,32,
                      104,101,114,32,108,105,102,101,32,105,110,32,116,104,101,32,106,117,110,103,108,101,46] HTtree4 []"
(*Search in text "He tackled the problem in a typically haphazard manner."*)
value "trie_match_tm [72,101,32,116,97,99,107,108,101,100,32,116,104,101,32,112,114,111,98,108,101,109,32,105,110,32,97,32,116,121,112,105,
                      99,97,108,108,121,32,104,97,112,104,97,122,97,114,100,32,109,97,110,110,101,114,46] Ttree4 []"
value "hashtrie_match_tm [72,101,32,116,97,99,107,108,101,100,32,116,104,101,32,112,114,111,98,108,101,109,32,105,110,32,97,32,116,121,112,
                          105,99,97,108,108,121,32,104,97,112,104,97,122,97,114,100,32,109,97,110,110,101,114,46] HTtree4 []"
(*Search in text "anonymous kindnesses should be flushed out and announced."*)
value "trie_match_tm [97,110,111,110,121,109,111,117,115,32,107,105,110,100,110,101,115,115,101,115,32,115,104,111,117,108,100,32,98,
                      101,32,102,108,117,115,104,101,100,32,111,117,116,32,97,110,110,111,117,110,99,101,100,46] Ttree4 []"
value "hashtrie_match_tm [97,110,111,110,121,109,111,117,115,32,107,105,110,100,110,101,115,115,101,115,32,115,104,111,117,108,100,32,
                          98,101,32,102,108,117,115,104,101,100,32,111,117,116,32,97,110,110,111,117,110,99,101,100,46] HTtree4 []"
(*Search in text "We have five accounts of what happened and none of them agree."*)
value "trie_match_tm [87,101,32,104,97,118,101,32,102,105,118,101,32,97,99,99,111,117,110,116,115,32,111,102,32,119,104,97,116,32,104,97,112,
                      112,101,110,101,100,32,97,110,100,32,110,111,110,101,32,111,102,32,116,104,101,109,32,97,103,114,101,101,46] Ttree4 []"
value "hashtrie_match_tm [87,101,32,104,97,118,101,32,102,105,118,101,32,97,99,99,111,117,110,116,115,32,111,102,32,119,104,97,116,32,104,97,
                          112,112,101,110,101,100,32,97,110,100,32,110,111,110,101,32,111,102,32,116,104,101,109,32,97,103,114,101,101,46] HTtree4 []"
(*Search in text "The first few leaves in the gutter announced the beginning of autumn."*)
value "trie_match_tm [84,104,101,32,102,105,114,115,116,32,102,101,119,32,108,101,97,118,101,115,32,105,110,32,116,104,101,32,103,117,
                      116,116,101,114,32,97,110,110,111,117,110,99,101,100,32,116,104,101,32,98,101,103,105,110,110,105,110,32,111,102,
                      32,97,117,116,117,109,110,46] Ttree4 []"
value "hashtrie_match_tm [84,104,101,32,102,105,114,115,116,32,102,101,119,32,108,101,97,118,101,115,32,105,110,32,116,104,101,32,103,
                          117,116,116,101,114,32,97,110,110,111,117,110,99,101,100,32,116,104,101,32,98,101,103,105,110,110,105,110,32,
                          111,102,32,97,117,116,117,109,110,46] HTtree4 []"
(*Search in text "He's nice enough as a person, but he's not the right man for this job."*)
value "trie_match_tm [72::nat,101,39,115,32,110,105,99,101,32,101,110,111,117,103,104,32,97,115,32,97,32,112,101,114,115,111,110,44,32,
                      98,117,116,32,104,101,39,115,32,110,111,116,32,116,104,101,32,114,105,103,104,116,32,109,97,110,32,102,111,114,32,
                      116,104,105,115,32,106,111,98,46] Ttree4 []"
value "hashtrie_match_tm [72::nat,101,39,115,32,110,105,99,101,32,101,110,111,117,103,104,32,97,115,32,97,32,112,101,114,115,111,110,44,32,
                          98,117,116,32,104,101,39,115,32,110,111,116,32,116,104,101,32,114,105,103,104,116,32,109,97,110,32,102,111,114,32,
                          116,104,105,115,32,106,111,98,46] HTtree4 []"
(*Search in text "The new translation of the Latin work includes extensive annotation by scholars."*)
value "trie_match_tm [84,104,101,32,110,101,119,32,116,114,97,110,115,108,97,116,105,111,110,32,111,102,32,116,104,101,32,76,97,116,105,
                      110,32,119,111,114,107,32,105,110,99,108,117,100,101,115,32,101,120,116,101,110,115,105,118,101,32,97,110,110,111,
                      116,97,116,105,111,110,32,98,121,32,115,99,104,111,108,97,114,115,46] Ttree4 []"
value "hashtrie_match_tm [84,104,101,32,110,101,119,32,116,114,97,110,115,108,97,116,105,111,110,32,111,102,32,116,104,101,32,76,97,116,
                          105,110,32,119,111,114,107,32,105,110,99,108,117,100,101,115,32,101,120,116,101,110,115,105,118,101,32,97,110,
                          110,111,116,97,116,105,111,110,32,98,121,32,115,99,104,111,108,97,114,115,46] HTtree4 []"
(*Search in text "Three people were interviewed for the job, but only one person had the right qualifications"*)
value "trie_match_tm [84::nat,104,114,101,101,32,112,101,111,112,108,101,32,119,101,114,101,32,105,110,116,101,114,118,105,101,119,101,
                      100,32,102,111,114,32,116,104,101,32,106,111,98,44,32,98,117,116,32,111,110,108,121,32,111,110,101,32,112,101,114,
                      115,111,110,32,104,97,100,32,116,104,101,32,114,105,103,104,116,32,113,117,97,108,105,102,105,99,97,116,105,111,110,115] Ttree4 []"
value "hashtrie_match_tm [84::nat,104,114,101,101,32,112,101,111,112,108,101,32,119,101,114,101,32,105,110,116,101,114,118,105,101,119,101,
                      100,32,102,111,114,32,116,104,101,32,106,111,98,44,32,98,117,116,32,111,110,108,121,32,111,110,101,32,112,101,114,
                      115,111,110,32,104,97,100,32,116,104,101,32,114,105,103,104,116,32,113,117,97,108,105,102,105,99,97,116,105,111,110,115] HTtree4 []"


(*----------------------------------------------case 5-------------------------------------------------------*)
definition "Ttree5 = trie_automata [([109::nat,97,110],''man''),
                                    ([112,101,111,112,108,101],''people''),
                                    ([112,101,114,115,111,110],''person''),
                                    ([97::nat,110,111,110,121,109,111,117,115],''anonymous''),
                                    ([107,105,110,100,110,101,115,115],''kindness''),
                                    ([97,110,110,111,117,110,99,101],''announce''),
                                    ([97::nat,103,114,101,101],''agree''),
                                    ([97,99,99,111,117,110,116],''account''),
                                    ([104,97,112,112,101,110],''happen''),
                                    ([102::nat,97,99,101],''face''),
                                    ([102,105,114,115,116],''first''),
                                    ([102,105,118,101],''five''),
                                    ([114,105,103,104,116],''right''),
                                    ([114,111,108,101],''role'')] empty_trie"
definition "HTtree5 = hashtrie_automata [([109::nat,97,110],''man''),
                                         ([112,101,111,112,108,101],''people''),
                                         ([112,101,114,115,111,110],''person''),
                                         ([97::nat,110,111,110,121,109,111,117,115],''anonymous''),
                                         ([107,105,110,100,110,101,115,115],''kindness''),
                                         ([97,110,110,111,117,110,99,101],''announce''),
                                         ([97::nat,103,114,101,101],''agree''),
                                         ([97,99,99,111,117,110,116],''account''),
                                         ([104,97,112,112,101,110],''happen''),
                                         ([102::nat,97,99,101],''face''),
                                         ([102,105,114,115,116],''first''),
                                         ([102,105,118,101],''five''),
                                         ([114,105,103,104,116],''right''),
                                         ([114,111,108,101],''role'')] empty_hashtrie"
(*Search in text "man"*)
value "trie_match_tm [109::nat,97,110] Ttree5 []"
value "hashtrie_match_tm [109::nat,97,110] HTtree5 []"
(*Search in text "kind"*)
value "trie_match_tm [107,105,110,100] Ttree5 []"
value "hashtrie_match_tm [107,105,110,100] HTtree5 []"
(*Search in text "agree"*)
value "trie_match_tm [97,103,114,101,101] Ttree5 []"
value "hashtrie_match_tm [97,103,114,101,101] HTtree5 []"
(*Search in text "happen"*)
value "trie_match_tm [104,97,112,112,101,110] Ttree5 []"
value "hashtrie_match_tm [104,97,112,112,101,110] HTtree5 []"
(*Search in text "people"*)
value "trie_match_tm [112::nat,101,111,112,108,101] Ttree5 []"
value "hashtrie_match_tm [112::nat,101,111,112,108,101] HTtree5 []"
(*Search in text "person"*)
value "trie_match_tm [112::nat,101,114,115,111,110] Ttree5 []"
value "hashtrie_match_tm [112::nat,101,114,115,111,110] HTtree5 []"
(*Search in text "account"*)
value "trie_match_tm [97,99,99,111,117,110,116] Ttree5 []"
value "hashtrie_match_tm [97,99,99,111,117,110,116] HTtree5 []"
(*Search in text "kindness"*)
value "trie_match_tm [107,105,110,100,110,101,115,115] Ttree5 []"
value "hashtrie_match_tm [107,105,110,100,110,101,115,115] HTtree5 []"
(*Search in text "announce"*)
value "trie_match_tm [97,110,110,111,117,110,99,101] Ttree5 []"
value "hashtrie_match_tm [97,110,110,111,117,110,99,101] HTtree5 []"
(*Search in text "anonymous"*)
value "trie_match_tm [97,110,111,110,121,109,111,117,115] Ttree5 []"
value "hashtrie_match_tm [97,110,111,110,121,109,111,117,115] HTtree5 []"
(*Search in text "individual"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108] Ttree5 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108] HTtree5 []"
(*Search in text "individual people"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,111,112,108,101] Ttree5 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,111,112,108,101] HTtree5 []"
(*Search in text "individual person"*)
value "trie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,114,115,111,110] Ttree5 []"
value "hashtrie_match_tm [105::nat,110,100,105,118,105,100,117,97,108,32,112,101,114,115,111,110] HTtree5 []"
(*Search in text "the quality of being kind"*)
value "trie_match_tm [116,104,101,32,113,117,97,108,105,116,121,32,111,102,32,98,101,105,110,103,32,107,105,110,100] Ttree5 []"
value "hashtrie_match_tm [116,104,101,32,113,117,97,108,105,116,121,32,111,102,32,98,101,105,110,103,32,107,105,110,100] HTtree5 []"
(*Search in text "We finally agreed a deal."*)
value "trie_match_tm [87,101,32,102,105,110,97,108,108,121,32,97,103,114,101,101,100,32,97,32,100,101,97,108,46] Ttree5 []"
value "hashtrie_match_tm [87,101,32,102,105,110,97,108,108,121,32,97,103,114,101,101,100,32,97,32,100,101,97,108,46] HTtree5 []"
(*Search in text "Be persistent - don't give up."*)
value "trie_match_tm [66,101,32,112,101,114,115,105,115,116,101,110,116,32,45,32,100,111,110,39,116,32,103,105,118,101,32,117,112,46] Ttree5 []"
value "hashtrie_match_tm [66,101,32,112,101,114,115,105,115,116,101,110,116,32,45,32,100,111,110,39,116,32,103,105,118,101,32,117,112,46] HTtree5 []"
(*Search in text "He has a rather anonymous face."*)
value "trie_match_tm [72,101,32,104,97,115,32,97,32,114,97,116,104,101,114,32,97,110,111,110,121,109,111,117,115,32,102,97,99,101,46] Ttree5 []"
value "hashtrie_match_tm [72,101,32,104,97,115,32,97,32,114,97,116,104,101,114,32,97,110,111,110,121,109,111,117,115,32,102,97,99,101,46] HTtree5 []"
(*Search in text "The school is noted for its academic excellence."*)
value "trie_match_tm [84,104,101,32,115,99,104,111,111,108,32,105,115,32,110,111,116,101,100,32,102,111,114,32,105,116,115,32,97,99,97,100,
                      101,109,105,99,32,101,120,99,101,108,108,101,110,99,101,46] Ttree5 []"
value "hashtrie_match_tm [84,104,101,32,115,99,104,111,111,108,32,105,115,32,110,111,116,101,100,32,102,111,114,32,105,116,115,32,97,99,97,
                          100,101,109,105,99,32,101,120,99,101,108,108,101,110,99,101,46] HTtree5 []"
(*Search in text "Now consider what happens if learning plays a role."*)
value "trie_match_tm [78,111,119,32,99,111,110,115,105,100,101,114,32,119,104,97,116,32,104,97,112,112,101,110,115,32,105,102,32,108,101,97,
                      114,110,105,110,103,32,112,108,97,121,115,32,97,32,114,111,108,101,46] Ttree5 []"
value "hashtrie_match_tm [78,111,119,32,99,111,110,115,105,100,101,114,32,119,104,97,116,32,104,97,112,112,101,110,115,32,105,102,32,108,101,97,
                      114,110,105,110,103,32,112,108,97,121,115,32,97,32,114,111,108,101,46] HTtree5 []"
(*Search in text "She gave a thrilling account of her life in the jungle."*)
value "trie_match_tm [83,104,101,32,103,97,118,101,32,97,32,116,104,114,105,108,108,105,110,103,32,97,99,99,111,117,110,116,32,111,102,32,
                      104,101,114,32,108,105,102,101,32,105,110,32,116,104,101,32,106,117,110,103,108,101,46] Ttree5 []"
value "hashtrie_match_tm [83,104,101,32,103,97,118,101,32,97,32,116,104,114,105,108,108,105,110,103,32,97,99,99,111,117,110,116,32,111,102,32,
                      104,101,114,32,108,105,102,101,32,105,110,32,116,104,101,32,106,117,110,103,108,101,46] HTtree5 []"
(*Search in text "He tackled the problem in a typically haphazard manner."*)
value "trie_match_tm [72,101,32,116,97,99,107,108,101,100,32,116,104,101,32,112,114,111,98,108,101,109,32,105,110,32,97,32,116,121,112,105,
                      99,97,108,108,121,32,104,97,112,104,97,122,97,114,100,32,109,97,110,110,101,114,46] Ttree5 []"
value "hashtrie_match_tm [72,101,32,116,97,99,107,108,101,100,32,116,104,101,32,112,114,111,98,108,101,109,32,105,110,32,97,32,116,121,112,
                          105,99,97,108,108,121,32,104,97,112,104,97,122,97,114,100,32,109,97,110,110,101,114,46] HTtree5 []"
(*Search in text "anonymous kindnesses should be flushed out and announced."*)
value "trie_match_tm [97,110,111,110,121,109,111,117,115,32,107,105,110,100,110,101,115,115,101,115,32,115,104,111,117,108,100,32,98,
                      101,32,102,108,117,115,104,101,100,32,111,117,116,32,97,110,110,111,117,110,99,101,100,46] Ttree5 []"
value "hashtrie_match_tm [97,110,111,110,121,109,111,117,115,32,107,105,110,100,110,101,115,115,101,115,32,115,104,111,117,108,100,32,
                          98,101,32,102,108,117,115,104,101,100,32,111,117,116,32,97,110,110,111,117,110,99,101,100,46] HTtree5 []"
(*Search in text "We have five accounts of what happened and none of them agree."*)
value "trie_match_tm [87,101,32,104,97,118,101,32,102,105,118,101,32,97,99,99,111,117,110,116,115,32,111,102,32,119,104,97,116,32,104,97,112,
                      112,101,110,101,100,32,97,110,100,32,110,111,110,101,32,111,102,32,116,104,101,109,32,97,103,114,101,101,46] Ttree5 []"
value "hashtrie_match_tm [87,101,32,104,97,118,101,32,102,105,118,101,32,97,99,99,111,117,110,116,115,32,111,102,32,119,104,97,116,32,104,97,
                          112,112,101,110,101,100,32,97,110,100,32,110,111,110,101,32,111,102,32,116,104,101,109,32,97,103,114,101,101,46] HTtree5 []"
(*Search in text "The first few leaves in the gutter announced the beginning of autumn."*)
value "trie_match_tm [84,104,101,32,102,105,114,115,116,32,102,101,119,32,108,101,97,118,101,115,32,105,110,32,116,104,101,32,103,117,
                      116,116,101,114,32,97,110,110,111,117,110,99,101,100,32,116,104,101,32,98,101,103,105,110,110,105,110,32,111,102,
                      32,97,117,116,117,109,110,46] Ttree5 []"
value "hashtrie_match_tm [84,104,101,32,102,105,114,115,116,32,102,101,119,32,108,101,97,118,101,115,32,105,110,32,116,104,101,32,103,
                          117,116,116,101,114,32,97,110,110,111,117,110,99,101,100,32,116,104,101,32,98,101,103,105,110,110,105,110,32,
                          111,102,32,97,117,116,117,109,110,46] HTtree5 []"
(*Search in text "He's nice enough as a person, but he's not the right man for this job."*)
value "trie_match_tm [72::nat,101,39,115,32,110,105,99,101,32,101,110,111,117,103,104,32,97,115,32,97,32,112,101,114,115,111,110,44,32,
                      98,117,116,32,104,101,39,115,32,110,111,116,32,116,104,101,32,114,105,103,104,116,32,109,97,110,32,102,111,114,32,
                      116,104,105,115,32,106,111,98,46] Ttree5 []"
value "hashtrie_match_tm [72::nat,101,39,115,32,110,105,99,101,32,101,110,111,117,103,104,32,97,115,32,97,32,112,101,114,115,111,110,44,32,
                          98,117,116,32,104,101,39,115,32,110,111,116,32,116,104,101,32,114,105,103,104,116,32,109,97,110,32,102,111,114,32,
                          116,104,105,115,32,106,111,98,46] HTtree5 []"
(*Search in text "The new translation of the Latin work includes extensive annotation by scholars."*)
value "trie_match_tm [84,104,101,32,110,101,119,32,116,114,97,110,115,108,97,116,105,111,110,32,111,102,32,116,104,101,32,76,97,116,105,
                      110,32,119,111,114,107,32,105,110,99,108,117,100,101,115,32,101,120,116,101,110,115,105,118,101,32,97,110,110,111,
                      116,97,116,105,111,110,32,98,121,32,115,99,104,111,108,97,114,115,46] Ttree5 []"
value "hashtrie_match_tm [84,104,101,32,110,101,119,32,116,114,97,110,115,108,97,116,105,111,110,32,111,102,32,116,104,101,32,76,97,116,
                          105,110,32,119,111,114,107,32,105,110,99,108,117,100,101,115,32,101,120,116,101,110,115,105,118,101,32,97,110,
                          110,111,116,97,116,105,111,110,32,98,121,32,115,99,104,111,108,97,114,115,46] HTtree5 []"
(*Search in text "Three people were interviewed for the job, but only one person had the right qualifications"*)
value "trie_match_tm [84::nat,104,114,101,101,32,112,101,111,112,108,101,32,119,101,114,101,32,105,110,116,101,114,118,105,101,119,101,
                      100,32,102,111,114,32,116,104,101,32,106,111,98,44,32,98,117,116,32,111,110,108,121,32,111,110,101,32,112,101,114,
                      115,111,110,32,104,97,100,32,116,104,101,32,114,105,103,104,116,32,113,117,97,108,105,102,105,99,97,116,105,111,110,115] Ttree5 []"
value "hashtrie_match_tm [84::nat,104,114,101,101,32,112,101,111,112,108,101,32,119,101,114,101,32,105,110,116,101,114,118,105,101,119,101,
                      100,32,102,111,114,32,116,104,101,32,106,111,98,44,32,98,117,116,32,111,110,108,121,32,111,110,101,32,112,101,114,
                      115,111,110,32,104,97,100,32,116,104,101,32,114,105,103,104,116,32,113,117,97,108,105,102,105,99,97,116,105,111,110,115] HTtree5 []"

