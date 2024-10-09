theory Profile_Interpretations
  imports Profile
          Approval_Profile
          Preference_Profile
          Collections.Locale_Code
begin

text \<open>
  Interpretations of the result locale are placed inside a Locale-Code block
  in order to enable code generation of later definitions in the locale.
  Those definitions need to be added via a Locale-Code block as well.
\<close>

setup Locale_Code.open_block

subsection \<open>Approval Profiles\<close>

global_interpretation \<A>\<V>_profile:
  ballot "ballot_\<A>\<V>" "default_ballot_\<A>\<V>" "prefers_\<A>\<V>" "wins_\<A>\<V>" "limit_\<A>\<V>_ballot"
proof (unfold_locales)
  fix
    A :: "'a Approval_Set" and
    a1 :: "'a" and
    a2 :: "'a"
  assume "a1 \<noteq> a2 \<and> prefers_\<A>\<V> A a1 a2"
  thus "\<not> wins_\<A>\<V> A a2" by simp
  next
  fix
    A :: "'a set" and
    b :: "'a Approval_Set"
    assume "ballot_\<A>\<V> A b"
    hence "(b  \<subseteq> A)" by simp
    thus "limit_\<A>\<V>_ballot A b = b" by (simp add: Int_commute inf.order_iff)
  next
    fix
      A :: "'a set" and
      B ::"'a set" and
      b :: "'a Approval_Set"
    assume "A \<subseteq> B"
    thus " limit_\<A>\<V>_ballot A b = limit_\<A>\<V>_ballot A (limit_\<A>\<V>_ballot B b)" by auto
  next
    fix
      A :: "'a set" and
      B ::"'a set" and
      b :: "'a Approval_Set"
    assume 
      assm: "ballot_\<A>\<V> B b \<and> A \<subseteq> B"
    hence ballot: "ballot_\<A>\<V> B b" by simp
    moreover have  sub: " A \<subseteq> B" using assm by simp
    thus "ballot_\<A>\<V> A (limit_\<A>\<V>_ballot A b)" by simp
qed
  

subsection \<open>Preference Profiles\<close>

global_interpretation \<P>\<V>_profile:
  ballot "ballot_\<P>\<V>" "default_ballot_\<P>\<V>" "prefers_\<P>\<V>" "wins_\<P>\<V>" "limit_\<P>\<V>_ballot"
proof (unfold_locales)
  fix
    b :: "'a Preference_Relation" and
    a1 :: "'a" and
    a2 :: "'a"
  assume "a1 \<noteq> a2 \<and> prefers_\<P>\<V> b a1 a2"
  thus "\<not> wins_\<P>\<V> b a2" by auto
  next
  fix
    A :: "'a set" and
    b :: "'a Preference_Relation"
    assume "ballot_\<P>\<V> A b"
    hence "linear_order_on A b" by simp
    hence "b \<subseteq> A \<times> A" by (simp add: order_on_defs refl_on_def)
    thus "limit_\<P>\<V>_ballot A b = b" by auto
  next
    fix
      A :: "'a set" and
      B ::"'a set" and
      b :: "'a Preference_Relation"
    assume "A \<subseteq> B"
    thus " limit_\<P>\<V>_ballot A b = limit_\<P>\<V>_ballot A (limit_\<P>\<V>_ballot B b)" by auto
  next
    fix
      A :: "'a set" and
      B ::"'a set" and
      b :: "'a Preference_Relation"
    assume 
      assm: "ballot_\<P>\<V> B b \<and> A \<subseteq> B"
    hence ballot: "ballot_\<P>\<V> B b" by simp
    moreover have  sub: " A \<subseteq> B" using assm by simp
    have "linear_order_on B b" using ballot by simp
    thus "ballot_\<P>\<V> A (limit_\<P>\<V>_ballot A b)" using sub limit_presv_lin_ord by auto
qed


lemma pref_count:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a Preference_Relation) Profile" and
    a :: "'a" and
    b :: "'a"
  assumes
    prof: "\<P>\<V>_profile.well_formed_profile V A p" and
    fin: "finite V" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    neq: "a \<noteq> b"
  shows "\<P>\<V>_profile.prefer_count V p a b = card V - (\<P>\<V>_profile.prefer_count V p b a)"
proof -
  have "\<forall> v \<in> V. \<not> (let r = (p v) in (b \<preceq>\<^sub>r a)) \<longrightarrow> (let r = (p v) in (a \<preceq>\<^sub>r b))"
    using a_in_A b_in_A prof lin_ord_imp_connex \<P>\<V>_profile.well_formed_profile_def ballot_\<P>\<V>.simps
    unfolding ballot_def connex_def
    by metis
  hence "\<forall> v \<in> V. \<not> (prefers_\<P>\<V> (p v) b a) \<longrightarrow> (prefers_\<P>\<V> (p v) a b)"
    using above_def 
    by fastforce
  moreover have "\<forall> v \<in> V. ((b, a) \<in> (p v) \<longrightarrow> (a, b) \<notin> (p v))"
    using antisymD neq lin_imp_antisym prof \<P>\<V>_profile.well_formed_profile_def ballot_\<P>\<V>.simps
    unfolding ballot_def
    by metis
  ultimately have "\<forall> v \<in> V. (a \<in> (above (p v) b) \<longleftrightarrow> \<not>(b \<in> (above (p v) a)))"
    using above_def by fastforce
  hence
    "{v \<in> V. prefers_\<P>\<V> (p v) b a} =
        V - {v \<in> V. prefers_\<P>\<V> (p v) a b}" by fastforce
  hence
    "card {v \<in> V. prefers_\<P>\<V> (p v) b a} =
        card V - card {v \<in> V. prefers_\<P>\<V> (p v) a b}"
    by (simp add: card_Diff_subset fin)
  thus ?thesis 
    using \<P>\<V>_profile.prefer_count.simps fin
    by (metis (mono_tags, lifting) \<P>\<V>_profile.pref_count_voter_set_card diff_diff_cancel enat_ord_simps(1) idiff_enat_enat)
qed

lemma pref_count_sym:
  fixes
    p :: "('v, 'a Preference_Relation) Profile" and
    V :: "'v set" and
    a :: "'a" and
    b :: "'a" and
    c :: "'a"
  assumes
    pref_count_ineq: "\<P>\<V>_profile.prefer_count V p a c \<ge> \<P>\<V>_profile.prefer_count V p c b" and
    prof: "\<P>\<V>_profile.well_formed_profile V A p" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    c_in_A: "c \<in> A" and
    a_neq_c: "a \<noteq> c" and
    c_neq_b: "c \<noteq> b"
  shows "\<P>\<V>_profile.prefer_count V p b c \<ge> \<P>\<V>_profile.prefer_count V p c a"
proof (cases "finite V")
  case True
  moreover have
    nat1: "\<P>\<V>_profile.prefer_count V p c a \<in> \<nat>" and
    nat2: "\<P>\<V>_profile.prefer_count V p b c \<in> \<nat>"
    unfolding Nats_def
    using True of_nat_eq_enat
    by (simp, simp)
  moreover have smaller: "\<P>\<V>_profile.prefer_count V p c a \<le> card V"
    using True prof \<P>\<V>_profile.pref_count_voter_set_card
    by metis
  moreover have
    "\<P>\<V>_profile.prefer_count V p a c = card V - (\<P>\<V>_profile.prefer_count V p c a)" and
    pref_count_b_eq:
    "\<P>\<V>_profile.prefer_count V p c b = card V - (\<P>\<V>_profile.prefer_count V p b c)"
    using True pref_count prof c_in_A
    by (metis (no_types, opaque_lifting) a_in_A a_neq_c,
        metis (no_types, opaque_lifting) b_in_A c_neq_b)
  hence "card V - (\<P>\<V>_profile.prefer_count V p b c) + (\<P>\<V>_profile.prefer_count V p c a)
      \<le> card V - (\<P>\<V>_profile.prefer_count V p c a) + (\<P>\<V>_profile.prefer_count V p c a)"
    using pref_count_b_eq pref_count_ineq
    by simp
  ultimately show ?thesis
    by simp
next
  case False
  thus ?thesis
    by simp
qed


subsubsection \<open>Lifting Property\<close>
  
definition equiv_prof_except_a :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'a Preference_Relation) Profile \<Rightarrow>
        ('v, 'a Preference_Relation) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "equiv_prof_except_a V A p p' a \<equiv>
    \<P>\<V>_profile.well_formed_profile V A p \<and> \<P>\<V>_profile.well_formed_profile V A p' \<and> a \<in> A \<and>
      (\<forall> v \<in> V. equiv_rel_except_a A (p v) (p' v) a)"

text \<open>
  An alternative gets lifted from one profile to another iff
  its ranking increases in at least one ballot, and nothing else changes.
\<close>

definition lifted :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v, 'a Preference_Relation) Profile \<Rightarrow> 
      ('v, 'a Preference_Relation) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted V A p p' a \<equiv>
    \<P>\<V>_profile.finite_profile V A p \<and> \<P>\<V>_profile.finite_profile V A p' \<and> a \<in> A
      \<and> (\<forall> v \<in> V. \<not> Preference_Relation.lifted A (p v) (p' v) a \<longrightarrow> (p v) = (p' v))
      \<and> (\<exists> v \<in> V. Preference_Relation.lifted A (p v) (p' v) a)"

lemma lifted_imp_equiv_prof_except_a:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a Preference_Relation) Profile" and
    p' :: "('v, 'a Preference_Relation) Profile" and
    a :: "'a"
  assumes "lifted V A p p' a"
  shows "equiv_prof_except_a V A p p' a"
proof (unfold equiv_prof_except_a_def, safe)
  show
    "\<P>\<V>_profile.well_formed_profile V A p" and
    "\<P>\<V>_profile.well_formed_profile V A p'" and
    "a \<in> A"
    using assms
    unfolding lifted_def
    by (metis, metis, metis)
next
  fix v :: "'v"
  assume "v \<in> V"
  thus "equiv_rel_except_a A (p v) (p' v) a"
    using assms lifted_imp_equiv_rel_except_a trivial_equiv_rel
    unfolding lifted_def \<P>\<V>_profile.well_formed_profile_def
    by fastforce
qed

lemma negl_diff_imp_eq_limit_prof:
  fixes
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a Preference_Relation) Profile" and
    p' :: "('v, 'a Preference_Relation) Profile" and
    a :: "'a"
  assumes
    change: "equiv_prof_except_a V A' p q a" and
    subset: "A \<subseteq> A'" and
    not_in_A: "a \<notin> A"
  shows "\<forall> v \<in> V. (\<P>\<V>_profile.limit_profile A p) v = (\<P>\<V>_profile.limit_profile A q) v"
  \<comment> \<open>With the current definitions of \<open>equiv_prof_except_a\<close> and \<open>limit_prof\<close>, we can
      only conclude that the limited profiles coincide on the given voter set, since
      \<open>limit_prof\<close> may change the profiles everywhere, while \<open>equiv_prof_except_a\<close>
      only makes statements about the voter set.\<close>
proof (clarify)
  fix
    v :: 'v
  assume "v \<in> V"
  hence "equiv_rel_except_a A' (p v) (q v) a"
    using change equiv_prof_except_a_def
    by metis
  thus "\<P>\<V>_profile.limit_profile A p v = \<P>\<V>_profile.limit_profile A q v"
    using subset not_in_A negl_diff_imp_eq_limit
    by simp
qed

lemma limit_prof_eq_or_lifted:
  fixes
    A :: "'a set" and
    A' :: "'a set" and
    V :: "'v set" and
    p :: "('v, 'a Preference_Relation) Profile" and
    p' :: "('v, 'a Preference_Relation) Profile" and
    a :: "'a"
  assumes
    lifted_a: "lifted V A' p p' a" and
    subset: "A \<subseteq> A'"
  shows "(\<forall> v \<in> V. \<P>\<V>_profile.limit_profile A p v = \<P>\<V>_profile.limit_profile A p' v)
        \<or> lifted V A (\<P>\<V>_profile.limit_profile A p) (\<P>\<V>_profile.limit_profile A p') a"
proof (cases "a \<in> A")
  case True
  have "\<forall> v \<in> V. Preference_Relation.lifted A' (p v) (p' v) a \<or> (p v) = (p' v)"
    using lifted_a
    unfolding lifted_def
    by metis
  hence one:
    "\<forall> v \<in> V.
         Preference_Relation.lifted A (limit A (p v)) (limit A (p' v)) a \<or>
           (limit A (p v)) = (limit A (p' v))"
    using limit_lifted_imp_eq_or_lifted subset
    by metis
  thus ?thesis
  proof (cases "\<forall> v \<in> V. limit A (p v) = limit A (p' v)")
    case True
    thus ?thesis
      by simp
  next
    case False
    let ?p = "\<P>\<V>_profile.limit_profile A p"
    let ?q = "\<P>\<V>_profile.limit_profile A p'"
    have
      "\<P>\<V>_profile.well_formed_profile V A ?p" and
      "\<P>\<V>_profile.well_formed_profile V A ?q"
      using lifted_a subset \<P>\<V>_profile.limit_profile_sound
      unfolding lifted_def
      by (safe, safe)
    moreover have
      "\<exists> v \<in> V. Preference_Relation.lifted A (?p v) (?q v) a"
      using False one
      unfolding \<P>\<V>_profile.limit_profile.simps 
      by auto
    ultimately have "lifted V A ?p ?q a"
      using True lifted_a one rev_finite_subset subset
      unfolding lifted_def \<P>\<V>_profile.limit_profile.simps
      by auto
    thus ?thesis
      by simp
  qed
next
  case False
  thus ?thesis
    using lifted_a negl_diff_imp_eq_limit_prof subset lifted_imp_equiv_prof_except_a
    by metis
qed




setup Locale_Code.close_block

end