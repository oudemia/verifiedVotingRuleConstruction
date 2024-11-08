theory Profile
  imports 
     Main
     Auxiliary_Lemmas
     Preference_Relation
     "HOL-Library.Extended_Nat"
     "HOL-Combinatorics.Permutations"
begin

subsection \<open>Definition\<close>

text \<open>
  A ballot contains information about the preferences of a single voter towards electable
  alternatives. 
  A profile is a function that assigns a ballot to each voter in the election. 
  An election consists of a set of participating voters,
  a set of eligible alternatives, and a corresponding profile.
\<close>

type_synonym ('v, 'b) Profile = "'v \<Rightarrow> 'b"

type_synonym ('a, 'v, 'b) Election = "'a set \<times> 'v set \<times> ('v, 'b) Profile"

fun alternatives_\<E> :: "('a, 'v, 'b) Election \<Rightarrow> 'a set" where
  "alternatives_\<E> E = fst E"

fun voters_\<E> :: "('a, 'v, 'b) Election \<Rightarrow> 'v set" where
  "voters_\<E> E = fst (snd E)"

fun profile_\<E> :: "('a, 'v, 'b) Election \<Rightarrow> ('v, 'b) Profile" where
  "profile_\<E> E = snd (snd E)"

fun election_equality :: "('a, 'v, 'b) Election \<Rightarrow> ('a, 'v, 'b) Election \<Rightarrow> bool" where
  "election_equality (A, V, p) (A', V', p') =
        (A = A' \<and> V = V' \<and> (\<forall> v \<in> V. p v = p' v))"

\<comment> \<open>Here, we count the occurrences of a ballot in an election,
    i.e., how many voters specifically chose that exact ballot.\<close>
fun vote_count :: "'b \<Rightarrow> ('a, 'v, 'b) Election \<Rightarrow> nat" where
  "vote_count p E = card {v \<in> (voters_\<E> E). (profile_\<E> E) v = p}"
  

locale ballot =
  fixes 
    well_formed_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> bool" and
    empty_ballot :: "'b" and
    prefers :: "'b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" and
    wins :: "'b \<Rightarrow> 'a \<Rightarrow> bool" and
    limit_ballot :: "'a set \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes 
    winner_top: "\<And> (b::'b) (a1::'a) (a2::'a). 
      (a1 \<noteq> a2 \<and> prefers b a1 a2) \<Longrightarrow> \<not> wins b a2" and
    only_known_alts: "\<And> (A :: 'a set) (b :: 'b). 
      well_formed_ballot A b \<Longrightarrow> (limit_ballot A b = b)" and
    limit_trans: "\<And> (A::'a set) (B::'a set) (b::'b). 
      (A \<subseteq> B) \<Longrightarrow> limit_ballot A b = limit_ballot A (limit_ballot B b)" and
    limit_sound: "\<And> (A::'a set) (B::'a set) (b::'b).
      well_formed_ballot B b \<and> A \<subseteq> B \<Longrightarrow> well_formed_ballot A (limit_ballot A b)"
begin

text \<open>
  A profile on a set of alternatives A and a voter set V consists of ballots
  that are well formed on A for all voters in V.
  A finite profile is one with finitely many alternatives and voters.
\<close>

definition well_formed_profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "well_formed_profile V A p \<equiv> (\<forall> v \<in> V. well_formed_ballot A (p v))"

abbreviation finite_profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
  "finite_profile V A p \<equiv> finite A \<and> finite V \<and> well_formed_profile V A p"

abbreviation finite_election :: "('a, 'v, 'b) Election \<Rightarrow> bool" where
  "finite_election E \<equiv> finite_profile (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E)"

definition finite_elections_\<V> :: "('a, 'v, 'b) Election set" where
  "finite_elections_\<V> = {E :: ('a, 'v, 'b) Election. finite (voters_\<E> E)}"

definition finite_elections :: "('a, 'v, 'b) Election set" where
  "finite_elections = {E :: ('a, 'v, 'b) Election. finite_election E}"

definition valid_elections :: "('a, 'v, 'b) Election set" where
  "valid_elections = {E. well_formed_profile (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E)}"


fun limit_profile :: "'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'b) Profile" where
  "limit_profile A p = (\<lambda> v. limit_ballot A (p v))"

\<comment> \<open>This function subsumes elections with fixed alternatives, finite voters, and
    a default value for the profile value on non-voters.\<close>
fun elections_\<A> :: "'a set \<Rightarrow> ('a, 'v, 'b) Election set" where
  "elections_\<A> A =
        valid_elections
      \<inter> {E. alternatives_\<E> E = A \<and> finite (voters_\<E> E)
            \<and> (\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = empty_ballot)}"


subsection \<open>Vote Count\<close>

lemma vote_count_sum:
  fixes E :: "('a, 'v, 'b) Election"
  assumes
    "finite (voters_\<E> E)" and
    "finite (UNIV::('a \<times> 'a) set)"
  shows "sum (\<lambda> p. vote_count p E) UNIV = card (voters_\<E> E)"
proof (unfold vote_count.simps)
  have "\<forall> p. finite {v \<in> voters_\<E> E. profile_\<E> E v = p}"
    using assms
    by force
  moreover have
    "disjoint {{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"
    unfolding disjoint_def
    by fastforce
  moreover have partition:
    "voters_\<E> E = \<Union> {{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"
    using Union_eq[of "{{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"]
    by blast
  ultimately have card_eq_sum':
    "card (voters_\<E> E) =
        sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"
    using card_Union_disjoint[of
            "{{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"]
    by auto
  have "finite {{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV}"
    using partition assms
    by (simp add: finite_UnionD)
  moreover have
    "{{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV} =
        {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
      \<union> {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}"
    by blast
  moreover have
    "{} =
        {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
      \<inter> {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}"
    by blast
  ultimately have
    "sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p} | p. p \<in> UNIV} =
        sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
      + sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}"
    using sum.union_disjoint[of
            "{{v \<in> voters_\<E> E. profile_\<E> E v = p}
                | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
            "{{v \<in> voters_\<E> E. profile_\<E> E v = p}
                | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}"]
    by simp
  moreover have
    "\<forall> X \<in> {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}.
        card X = 0"
    using card_eq_0_iff
    by fastforce
  ultimately have card_eq_sum:
    "card (voters_\<E> E) =
        sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    using card_eq_sum'
    by simp
  have
    "inj_on (\<lambda> p. {v \<in> voters_\<E> E. profile_\<E> E v = p})
        {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    unfolding inj_on_def
    by blast
  moreover have
    "(\<lambda> p. {v \<in> voters_\<E> E. profile_\<E> E v = p})
            ` {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
        \<subseteq> {{v \<in> voters_\<E> E. profile_\<E> E v = p}
              | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    by blast
  moreover have
    "(\<lambda> p. {v \<in> voters_\<E> E. profile_\<E> E v = p})
            ` {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
        \<supseteq> {{v \<in> voters_\<E> E. profile_\<E> E v = p}
              | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    by blast
  ultimately have
    "bij_betw (\<lambda> p. {v \<in> voters_\<E> E. profile_\<E> E v = p})
            {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}
        {{v \<in> voters_\<E> E. profile_\<E> E v = p}
          | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    unfolding bij_betw_def
    by simp
  hence sum_rewrite:
    "(\<Sum> x \<in> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}.
            card {v \<in> voters_\<E> E. profile_\<E> E v = x}) =
        sum card {{v \<in> voters_\<E> E. profile_\<E> E v = p}
            | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
    using sum_comp[of
            "\<lambda> p. {v \<in> voters_\<E> E. profile_\<E> E v = p}"
            "{p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
            "{{v \<in> voters_\<E> E. profile_\<E> E v = p}
                | p. p \<in> UNIV \<and> {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"
            "card"]
    unfolding comp_def
    by simp
  have "{p. {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}
        \<inter> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}} = {}"
    by blast
  moreover have
    "{p. {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}
        \<union> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}} = UNIV"
    by blast
  ultimately have
    "(\<Sum> p \<in> UNIV. card {v \<in> voters_\<E> E. profile_\<E> E v = p}) =
        (\<Sum> x \<in> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}.
          card {v \<in> voters_\<E> E. profile_\<E> E v = x})
      + (\<Sum> x \<in> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}.
          card {v \<in> voters_\<E> E. profile_\<E> E v = x})"
    using assms
          sum.union_disjoint[of
            "{p. {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}"
            "{p. {v \<in> voters_\<E> E. profile_\<E> E v = p} \<noteq> {}}"]
    using Finite_Set.finite_set add.commute finite_Un
    by (metis (mono_tags, lifting))
  moreover have
    "\<forall> x \<in> {p. {v \<in> voters_\<E> E. profile_\<E> E v = p} = {}}.
        card {v \<in> voters_\<E> E. profile_\<E> E v = x} = 0"
    using card_eq_0_iff
    by fastforce
  ultimately show
    "(\<Sum> p \<in> UNIV. card {v \<in> voters_\<E> E. profile_\<E> E v = p}) =
        card (voters_\<E> E)"
    using card_eq_sum sum_rewrite
    by simp
qed


subsection \<open>Voter Permutations\<close>

text \<open>
  A common action of interest on elections is renaming the voters,
  e.g., when talking about anonymity.
\<close>
fun rename :: "('v \<Rightarrow> 'v) \<Rightarrow> ('x, 'v, 'y) Election \<Rightarrow> ('x, 'v, 'y) Election" where
  "rename \<pi> (X, V, p) = (X, \<pi> ` V, p \<circ> (the_inv \<pi>))"

lemma rename_sound:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'b) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    prof: "well_formed_profile V A p" and
    renamed: "(A, V', q) = rename \<pi> (A, V, p)" and
    bij: "bij \<pi>"
  shows "well_formed_profile V' A q"
proof (unfold well_formed_profile_def, safe)
  fix v' :: "'v"
  assume "v' \<in> V'"
  moreover have "V' = \<pi> ` V"
    using renamed
    by simp
  ultimately have "((the_inv \<pi>) v') \<in> V"
    using UNIV_I bij bij_is_inj bij_is_surj
          f_the_inv_into_f inj_image_mem_iff
    by metis
  thus "well_formed_ballot A (q v')"
    using renamed bij prof
    unfolding well_formed_profile_def
    by simp
  qed

lemma rename_finite:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'b) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    "finite_profile V A p" and
    "(A, V', q) = rename \<pi> (A, V, p)" and
    "bij \<pi>"
  shows "finite_profile V' A q"
  using assms
proof (safe)
  show "finite V'"
    using assms
    by simp
next
  show "well_formed_profile V' A q"
    using assms rename_sound
    by metis
qed

lemma rename_inv:
  fixes
    \<pi> :: "'v \<Rightarrow> 'v" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'b) Profile"
  assumes "bij \<pi>"
  shows "rename \<pi> (rename (the_inv \<pi>) (A, V, p)) = (A, V, p)"
proof -
  have "rename \<pi> (rename (the_inv \<pi>) (A, V, p)) =
        (A, \<pi> ` (the_inv \<pi>) ` V, p \<circ> (the_inv (the_inv \<pi>)) \<circ> (the_inv \<pi>))"
    by simp
  moreover have "\<pi> ` (the_inv \<pi>) ` V = V"
    using assms
    by (simp add: f_the_inv_into_f_bij_betw image_comp)
  moreover have "(the_inv (the_inv \<pi>)) = \<pi>"
    using assms surj_def inj_on_the_inv_into surj_imp_inv_eq the_inv_f_f
    unfolding bij_betw_def
    by (metis (mono_tags, opaque_lifting))
  moreover have "\<pi> \<circ> (the_inv \<pi>) = id"
    using assms f_the_inv_into_f_bij_betw
    by fastforce
  ultimately show "rename \<pi> (rename (the_inv \<pi>) (A, V, p)) = (A, V, p)"
    by (simp add: rewriteR_comp_comp)
qed

lemma rename_inj:
  fixes \<pi> :: "'v \<Rightarrow> 'v"
  assumes "bij \<pi>"
  shows "inj (rename \<pi>)"
proof (unfold inj_def split_paired_All rename.simps, safe)
  fix
    A A' :: "'x set" and
    V V' :: "'v set" and
    p q :: "('v, 'y) Profile" and
    v :: "'v"
  assume
    "p \<circ> the_inv \<pi> = q \<circ> the_inv \<pi>" and
    "\<pi> ` V = \<pi> ` V'"
  thus
    "v \<in> V \<Longrightarrow> v \<in> V'" and
    "v \<in> V' \<Longrightarrow> v \<in> V" and
    "p = q"
    using assms
    by (metis bij_betw_imp_inj_on inj_image_eq_iff,
        metis bij_betw_imp_inj_on inj_image_eq_iff,
        metis bij_betw_the_inv_into bij_is_surj surj_fun_eq)
qed

lemma rename_surj:
  fixes \<pi> :: "'v \<Rightarrow> 'v"
  assumes "bij \<pi>"
  shows
    on_valid_elections: "rename \<pi> ` valid_elections = valid_elections" and
    on_finite_elections: "rename \<pi> ` finite_elections = finite_elections"
proof (safe)
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('v, 'b) Profile" and
    p' :: "('v, 'b) Profile"
  assume valid: "(A, V, p) \<in> valid_elections"
  hence "rename (the_inv \<pi>) (A, V, p) \<in> valid_elections"
    using assms bij_betw_the_inv_into rename_sound
    unfolding valid_elections_def
    by fastforce
  thus "(A, V, p) \<in> rename \<pi> ` valid_elections"
    using assms image_eqI rename_inv
    by metis
  assume "(A', V', p') = rename \<pi> (A, V, p)"
  thus "(A', V', p') \<in> valid_elections"
    using rename_sound valid assms
    unfolding valid_elections_def
    by fastforce
next
  fix
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    V' :: "'v set" and
    p :: "('v, 'b) Profile" and
    p' :: "('v, 'b) Profile"
  assume finite: "(A, V, p) \<in> finite_elections"
  hence "rename (the_inv \<pi>) (A, V, p) \<in> finite_elections"
    using assms bij_betw_the_inv_into rename_finite
    unfolding finite_elections_def
    by fastforce
  thus "(A, V, p) \<in> rename \<pi> ` finite_elections"
    using assms image_eqI rename_inv
    by metis
  assume "(A', V', p') = rename \<pi> (A, V, p)"
  thus "(A', V', p') \<in> finite_elections"
    using rename_sound finite assms
    unfolding finite_elections_def
    by fastforce
qed
    

subsection \<open>Preference Counts and Comparisons\<close>

text \<open>
  The win count for an alternative a with respect to a finite voter set V in a profile p is
  the amount of ballots from V in p which a wins. The interpretation of a 'win'
  depends on the interpretation of the profile locale.
  If the voter set is infinite, counting is not generally possible.
\<close>
fun win_count :: "'v set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'a \<Rightarrow> enat" where
  "win_count V p a = (if (finite V)
    then card {v \<in> V. wins (p v) a} else infinity)"

fun prefer_count :: "'v set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "prefer_count V p x y = (if (finite V)
      then card {v \<in> V. prefers (p v) x y} else infinity)"

fun preferred_overall :: "'v set \<Rightarrow> 'a \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "preferred_overall V a p b =
    (prefer_count V p a b > prefer_count V p b a)"
    
lemma pref_count_voter_set_card:
  fixes
    V :: "'v set" and
    p :: "('v, 'b) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes "finite V"
  shows "prefer_count V p a b \<le> card V"
  using assms
  by (simp add: card_mono)

lemma set_compr:
  fixes
    A :: "'a set" and
    f :: "'a \<Rightarrow> 'a set"
  shows "{f x | x. x \<in> A} = f ` A"
  by blast

lemma pref_count_set_compr:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'b) Profile" and
    a :: "'a"
  shows "{prefer_count V p a a' | a'. a' \<in> A - {a}} =
            (prefer_count V p a) ` (A - {a})"
  by blast


lemma preferred_inf_voters:
  fixes
    p :: "('v, 'b) Profile" and
    a :: "'a" and
    b :: "'a" and
    V :: "'v set"
  assumes "infinite V"
  shows "\<not> preferred_overall V b p a"
  using assms
  by simp

text \<open>
  Having alternative \<open>a\<close> win against \<open>b\<close> implies that \<open>b\<close> does not win against \<open>a\<close>.
\<close>

lemma preferred_antisym:
  fixes
    p :: "('v, 'b) Profile" and
    a :: "'a" and
    b :: "'a" and
    V :: "'v set"
  assumes "preferred_overall V a p b" \<comment> \<open>This already implies that \<open>V\<close> is finite.\<close>
  shows "\<not> preferred_overall V b p a"
  using assms
  by simp

lemma preferred_irreflex:
  fixes
    p :: "('v, 'b) Profile" and
    a :: "'a" and
    V :: "'v set"
  shows "\<not> preferred_overall V a p a"
  using preferred_antisym
  by metis

subsection \<open>Condorcet Winner\<close>

fun condorcet_winner :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner V A p a =
      (finite_profile V A p \<and> a \<in> A \<and> (\<forall> x \<in> A - {a}. preferred_overall V a p x))"

lemma cond_winner_unique_eq:
  fixes
    V :: "'v set" and
    A :: "'a set" and
    p :: "('v, 'b) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    "condorcet_winner V A p a" and
    "condorcet_winner V A p b"
  shows "b = a"
proof (rule ccontr)
  assume b_neq_a: "b \<noteq> a"
  hence "preferred_overall V b p a"
    using insert_Diff insert_iff assms
    by simp
  hence "\<not> preferred_overall V a p b"
    by (simp add: preferred_antisym)
  moreover have "preferred_overall V a p b"
    using Diff_iff b_neq_a singletonD assms
    by auto
  ultimately show False
    by simp
qed

lemma cond_winner_unique:
  fixes
    A :: "'a set" and
    p :: "('v, 'b) Profile" and
    a :: "'a"
  assumes "condorcet_winner V A p a"
  shows "{a' \<in> A. condorcet_winner V A p a'} = {a}"
proof (safe)
  fix a' :: "'a"
  assume "condorcet_winner V A p a'"
  thus "a' = a"
    using assms cond_winner_unique_eq
    by metis
next
  show "a \<in> A"
    using assms
    unfolding condorcet_winner.simps
    by (metis (no_types))
next
  show "condorcet_winner V A p a"
    using assms
    by presburger
qed

lemma cond_winner_unique_2:
  fixes
    V :: "'v set" and
    A :: "'a set" and
    p :: "('v, 'b) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    "condorcet_winner V A p a" and
    "b \<noteq> a"
  shows "\<not> condorcet_winner V A p b"
  using cond_winner_unique_eq assms
  by metis

subsection \<open>Limited Profile\<close>

text \<open>
  This function restricts a profile p to a set A of alternatives and
  a set V of voters s.t. voters outside of V do not have any preferences or
  do not cast a vote.
  This keeps all of A's preferences.
\<close>


lemma limit_prof_trans:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    C :: "'a set" and
    p :: "('v, 'b) Profile"
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B"
  shows "limit_profile C p = limit_profile C (limit_profile B p)"
  using assms
  by (metis limit_profile.simps limit_trans)


lemma limit_profile_sound:
  fixes
    A :: "'a set" and
    B :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'b) Profile"
  assumes
    "well_formed_profile V B p" and
    "A \<subseteq> B"
  shows "well_formed_profile V A (limit_profile A p)"
proof -
  have "\<forall> v \<in> V. well_formed_ballot A (limit_ballot A (p v))"
    using assms limit_sound well_formed_profile_def by meson
  hence "\<forall> v \<in> V. well_formed_ballot A ((limit_profile A p) v)"
    by simp
  thus "well_formed_profile V A (limit_profile A p)" 
    using well_formed_profile_def by blast
qed
 
lemma empty_prof_imp_zero_pref_count:
  fixes
    p :: "('v, 'b) Profile" and
    V :: "'v set" and
    a :: "'a" and
    b :: "'a"
  assumes "V = {}"
  shows "prefer_count V p a b = 0"
  unfolding zero_enat_def
  using assms
  by simp

end

subsection \<open>Combintions of Profiles\<close>

fun n_copy :: "nat \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'b) Profile \<Rightarrow> bool" where
"n_copy n V W p q = (\<forall>b. card {w | w. w \<in> W \<and> q w = b} = n * card {v | v. v \<in> V \<and> p v = b})"

fun (in ballot) joint_profile :: "'v set \<Rightarrow> 'v set \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'b) Profile \<Rightarrow> ('v, 'b) Profile" where
"joint_profile V W p q v = (if v \<in> V then p v else (if v \<in> W then q v else empty_ballot))"


subsection \<open>List Representation for Ordered Voters\<close>

text \<open>
  A profile on a voter set that has a natural order can be viewed as a list of ballots.
\<close>

fun to_list :: "'v::linorder set \<Rightarrow> ('v, 'b) Profile
                  \<Rightarrow> 'b list" where
  "to_list V p = (if (finite V)
                    then (map p (sorted_list_of_set V))
                    else [])"

lemma map2_helper:
  fixes
    f :: "'x \<Rightarrow> 'y \<Rightarrow> 'z" and
    g :: "'x \<Rightarrow> 'x" and
    h :: "'y \<Rightarrow> 'y" and
    l :: "'x list" and
    l' :: "'y list"
  shows "map2 f (map g l) (map h l') = map2 (\<lambda> x y. f (g x) (h y)) l l'"
proof -
  have "map2 f (map g l) (map h l') =
          map (\<lambda> (x, y). f x y) (map (\<lambda> (x, y). (g x, h y)) (zip l l'))"
    using zip_map_map
    by metis
  also have "\<dots> = map2 (\<lambda> x y. f (g x) (h y)) l l'"
    by auto
  finally show ?thesis
    by presburger
qed

lemma to_list_simp:
  fixes
    i :: "nat" and
    V :: "'v::linorder set" and
    p :: "('v, 'b) Profile"
  assumes "i < card V"
  shows "(to_list V p)!i = p ((sorted_list_of_set V)!i)"
proof -
  have "(to_list V p)!i = (map p (sorted_list_of_set V))!i"
    by simp
  also have "\<dots> = p ((sorted_list_of_set V)!i)"
    using assms
    by simp
  finally show ?thesis
    by presburger
qed

lemma to_list_comp:
  fixes
    V :: "'v::linorder set" and
    p :: "('v, 'b) Profile" and
    f :: "'b \<Rightarrow> 'b"
  shows "to_list V (f \<circ> p) = map f (to_list V p)"
  by simp

lemma set_card_upper_bound:
  fixes
    i :: "nat" and
    V :: "nat set"
  assumes
    fin_V: "finite V" and
    bound_v: "\<forall> v \<in> V. v < i"
  shows "card V \<le> i"
proof (cases "V = {}")
  case True
  thus ?thesis
    by simp
next
  case False
  moreover with fin_V
  have "Max V \<in> V"
    by simp
  ultimately show ?thesis
    using assms Suc_leI card_le_Suc_Max order_trans
    by metis
qed

lemma sorted_list_of_set_nth_equals_card:
  fixes
    V :: "'v :: linorder set" and
    x :: "'v"
  assumes
    fin_V: "finite V" and
    x_V: "x \<in> V"
  shows "sorted_list_of_set V!(card {v \<in> V. v < x}) = x"
proof -
  let ?c = "card {v \<in> V. v < x}" and
      ?set = "{v \<in> V. v < x}"
  have "\<forall> v \<in> V. \<exists> n. n < card V \<and> (sorted_list_of_set V!n) = v"
    using length_sorted_list_of_set sorted_list_of_set_unique in_set_conv_nth fin_V
    by metis
  then obtain \<phi> :: "'v \<Rightarrow> nat" where
    index_\<phi>: "\<forall> v \<in> V. \<phi> v < card V \<and> (sorted_list_of_set V!(\<phi> v)) = v"
    by metis
  \<comment> \<open>\<open>\<phi> x = ?c\<close>, i.e., \<open>\<phi> x \<ge> ?c\<close> and \<open>\<phi> x \<le> ?c\<close>\<close>
  let ?i = "\<phi> x"
  have inj_\<phi>: "inj_on \<phi> V"
    using inj_onI index_\<phi>
    by metis
  have "\<forall> v \<in> V. \<forall> v' \<in> V. v < v' \<longrightarrow> \<phi> v < \<phi> v'"
    using leD linorder_le_less_linear sorted_list_of_set_unique
          sorted_sorted_list_of_set sorted_nth_mono fin_V index_\<phi>
    by metis
  hence "\<forall> j \<in> {\<phi> v | v. v \<in> ?set}. j < ?i"
    using x_V
    by blast
  moreover have fin_img: "finite ?set"
    using fin_V
    by simp
  ultimately have "?i \<ge> card {\<phi> v | v. v \<in> ?set}"
    using set_card_upper_bound
    by simp
  also have "card {\<phi> v | v. v \<in> ?set} = ?c"
    using inj_\<phi>
    by (simp add: card_image inj_on_subset setcompr_eq_image)
  finally have geq: "?c \<le> ?i"
    by simp
  have sorted_\<phi>:
    "\<forall> i < card V. \<forall> j < card V. i < j
        \<longrightarrow> (sorted_list_of_set V!i) < (sorted_list_of_set V!j)"
    by (simp add: sorted_wrt_nth_less)
  have leq: "?i \<le> ?c"
  proof (rule ccontr, cases "?c < card V")
    case True
    let ?A = "\<lambda> j. {sorted_list_of_set V!j}"
    assume "\<not> ?i \<le> ?c"
    hence "?c < ?i"
      by simp
    hence "\<forall> j \<le> ?c. sorted_list_of_set V!j \<in> V \<and> sorted_list_of_set V!j < x"
      using sorted_\<phi> geq index_\<phi> x_V fin_V set_sorted_list_of_set
            length_sorted_list_of_set nth_mem order.strict_trans1
      by (metis (mono_tags, lifting))
    hence "{sorted_list_of_set V!j | j. j \<le> ?c} \<subseteq> {v \<in> V. v < x}"
      by blast
    also have "{sorted_list_of_set V!j | j. j \<le> ?c} =
                  {sorted_list_of_set V!j | j. j \<in> {0 ..< (?c + 1)}}"
      using add.commute
      by auto
    also have "{sorted_list_of_set V!j | j. j \<in> {0 ..< (?c + 1)}} =
                  (\<Union> j \<in> {0 ..< (?c + 1)}. {sorted_list_of_set V!j})"
      by blast
    finally have subset: "(\<Union> j \<in> {0 ..< (?c + 1)}. ?A j) \<subseteq> {v \<in> V. v < x}"
      by simp
    have "\<forall> i \<le> ?c. \<forall> j \<le> ?c.
              i \<noteq> j \<longrightarrow> sorted_list_of_set V!i \<noteq> sorted_list_of_set V!j"
      using True
      by (simp add: nth_eq_iff_index_eq)
    hence "\<forall> i \<in> {0 ..< (?c + 1)}. \<forall> j \<in> {0 ..< (?c + 1)}.
              (i \<noteq> j \<longrightarrow> {sorted_list_of_set V!i} \<inter> {sorted_list_of_set V!j} = {})"
      by fastforce
    hence "disjoint_family_on ?A {0 ..< (?c + 1)}"
      unfolding disjoint_family_on_def
      by simp
    moreover have "\<forall> j \<in> {0 ..< (?c + 1)}. card (?A j) = 1"
      by simp
    ultimately have
      "card (\<Union> j \<in> {0 ..< (?c + 1)}. ?A j) = (\<Sum> j \<in> {0 ..< (?c + 1)}. 1)"
      using card_UN_disjoint'
      by fastforce
    hence "card (\<Union> j \<in> {0 ..< (?c + 1)}. ?A j) = ?c + 1"
      by simp
    hence "?c + 1 \<le> ?c"
      using subset card_mono fin_img
      by (metis (no_types, lifting))
    thus False
      by simp
  next
    case False
    thus False
      using x_V index_\<phi> geq order_le_less_trans
      by blast
  qed
  thus ?thesis
    using geq leq x_V index_\<phi>
    by simp
qed

lemma to_list_permutes_under_bij:
  fixes
    \<pi> :: "'v::linorder \<Rightarrow> 'v" and
    V :: "'v set" and
    p :: "('v, 'b) Profile"
  assumes "bij \<pi>"
  shows
    "let \<phi> = (\<lambda> i. card {v \<in> \<pi> ` V. v < \<pi> ((sorted_list_of_set V)!i)})
      in (to_list V p) = permute_list \<phi> (to_list (\<pi> ` V) (\<lambda> x. p (the_inv \<pi> x)))"
proof (cases "finite V")
  case False
  \<comment> \<open>If \<open>V\<close> is infinite, both lists are empty.\<close>
  hence "to_list V p = []"
    by simp
  moreover have "infinite (\<pi> ` V)"
    using False assms bij_betw_finite bij_betw_subset top_greatest
    by metis
  hence "to_list (\<pi> ` V) (\<lambda> x. p (the_inv \<pi> x)) = []"
    by simp
  ultimately show ?thesis
    by simp
next
  case True
  let
    ?q = "\<lambda> x. p (the_inv \<pi> x)" and
    ?img = "\<pi> ` V" and
    ?n = "length (to_list V p)" and
    ?perm = "\<lambda> i. card {v \<in> \<pi> ` V. v < \<pi> ((sorted_list_of_set V)!i)}"
    \<comment> \<open>These are auxiliary statements equating everything with \<open>?n\<close>.\<close>
  have card_eq: "card ?img = card V"
    using assms bij_betw_same_card bij_betw_subset top_greatest
    by metis
  also have card_length_V: "?n = card V"
    by simp
  also have card_length_img: "length (to_list ?img ?q) = card ?img"
    using True
    by simp
  finally have eq_length: "length (to_list ?img ?q) = ?n"
    by simp
  show ?thesis
  proof (unfold Let_def permute_list_def, rule nth_equalityI)
    \<comment> \<open>The lists have equal lengths.\<close>
    show
      "length (to_list V p) =
          length (map
            (\<lambda> i. to_list ?img ?q!(card {v \<in> ?img.
                v < \<pi> (sorted_list_of_set V!i)}))
              [0 ..< length (to_list ?img ?q)])"
      using eq_length
      by simp
  next
    \<comment> \<open>The \<open>i\<close>th entries of the lists coincide.\<close>
    fix i :: "nat"
    assume in_bnds: "i < ?n"
    let ?c = "card {v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}"
    have "map (\<lambda> i. (to_list ?img ?q)!?c) [0 ..< ?n]!i =
            p ((sorted_list_of_set V)!i)"
    proof -
      have "\<forall> v. v \<in> ?img \<longrightarrow> {v' \<in> ?img. v' < v} \<subseteq> ?img - {v}"
        by blast
      moreover have elem_of_img: "\<pi> (sorted_list_of_set V!i) \<in> ?img"
        using True in_bnds image_eqI nth_mem card_length_V
              length_sorted_list_of_set set_sorted_list_of_set
        by metis
      ultimately have
        "{v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}
      \<subseteq> ?img - {\<pi> (sorted_list_of_set V!i)}"
        by simp
      hence "{v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)} \<subset> ?img"
        using elem_of_img
        by blast
      moreover have img_card_eq_V_length: "card ?img = ?n"
        using card_eq card_length_V
        by presburger
      ultimately have card_in_bnds: "?c < ?n"
        using True finite_imageI psubset_card_mono
        by (metis (mono_tags, lifting))
      moreover have img_list_map:
        "map (\<lambda> i. to_list ?img ?q!?c) [0 ..< ?n]!i = to_list ?img ?q!?c"
        using in_bnds
        by simp
      have img_list_card_eq_inv_img_list:
        "to_list ?img ?q!?c = ?q ((sorted_list_of_set ?img)!?c)"
        using in_bnds to_list_simp in_bnds img_card_eq_V_length card_in_bnds
        by (metis (no_types, lifting))
      have img_card_eq_img_list_i:
        "(sorted_list_of_set ?img)!?c = \<pi> (sorted_list_of_set V!i)"
        using True elem_of_img sorted_list_of_set_nth_equals_card
        by blast
      finally show ?thesis
        using assms bij_betw_imp_inj_on the_inv_f_f
              img_list_map img_card_eq_img_list_i
              img_list_card_eq_inv_img_list
        by metis
    qed
    also have "to_list V p!i = p ((sorted_list_of_set V)!i)"
      using True in_bnds
      by simp
    finally show "to_list V p!i =
        map (\<lambda> i. (to_list ?img ?q)!(card {v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}))
          [0 ..< length (to_list ?img ?q)]!i"
      using in_bnds eq_length Collect_cong card_eq
      by simp
  qed
qed

end