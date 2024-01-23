section \<open>Function Symmetry Properties\<close>

theory Symmetry_Of_Functions
  imports "HOL.Equiv_Relations"
          "HOL-Algebra.Bij"
          "HOL-Algebra.Group_Action"
          "HOL-Algebra.Generated_Groups"
begin

subsection \<open>Functions\<close>

type_synonym ('x, 'y) binary_fun = "'x \<Rightarrow> 'y \<Rightarrow> 'y"

fun extensional_continuation :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> ('x \<Rightarrow> 'y)" where
  "extensional_continuation f S = (\<lambda> x. if (x \<in> S) then (f x) else undefined)"

fun preimg :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x set \<Rightarrow> 'y \<Rightarrow> 'x set" where
  "preimg f X y = {x \<in> X. f x = y}"

text \<open>Relations\<close>

fun restr_rel :: "'x rel \<Rightarrow> 'x set \<Rightarrow> 'x set \<Rightarrow> 'x rel" where
  "restr_rel r F S = r \<inter> F \<times> S"

fun closed_under_restr_rel :: "'x rel \<Rightarrow> 'x set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "closed_under_restr_rel r X Y = ((restr_rel r Y X) `` Y \<subseteq> Y)"

fun rel_induced_by_action :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x, 'y) binary_fun \<Rightarrow> 'y rel" where
  "rel_induced_by_action X Y \<phi> = {(y1, y2) \<in> Y \<times> Y. \<exists> x \<in> X. \<phi> x y1 = y2}"

fun product_rel :: "'x rel \<Rightarrow> ('x * 'x) rel" where
  "product_rel r = {(pair1, pair2). (fst pair1, fst pair2) \<in> r \<and> (snd pair1, snd pair2) \<in> r}"

fun equivariance_rel :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x,'y) binary_fun \<Rightarrow> ('y * 'y) rel" where
  "equivariance_rel X Y \<phi> = {((a, b), (c, d)). (a, b) \<in> Y \<times> Y \<and> (\<exists> x \<in> X. c = \<phi> x a \<and> d = \<phi> x b)}"

fun set_closed_under_rel :: "'x set \<Rightarrow> 'x rel \<Rightarrow> bool" where
  "set_closed_under_rel X r = (\<forall> x y. (x, y) \<in> r \<longrightarrow> x \<in> X \<longrightarrow> y \<in> X)"

fun singleton_set_system :: "'x set \<Rightarrow> 'x set set" where
  "singleton_set_system X = {{x} | x. x \<in> X}"

fun set_action :: "('x, 'r) binary_fun \<Rightarrow> ('x, 'r set) binary_fun" where
  "set_action \<psi> x = image (\<psi> x)"

subsection \<open>Invariance and Equivariance\<close>

text \<open>
  Invariance and equivariance are symmetry properties of functions:
  Invariance means that related preimages have identical images and
  equivariance denotes consistent changes.
\<close>

datatype ('x, 'y) property =
  Invariance "'x rel" |
  Equivariance "'x set" "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set"

fun satisfies :: "('x \<Rightarrow> 'y) \<Rightarrow> ('x, 'y) property \<Rightarrow> bool" where
  "satisfies f (Invariance r) = (\<forall> a. \<forall> b. ((a, b) \<in> r \<longrightarrow> f a = f b))" |
  "satisfies f (Equivariance X Act) =
    (\<forall> (\<phi>, \<psi>) \<in> Act. \<forall> x \<in> X. \<phi> x \<in> X \<longrightarrow> f (\<phi> x) = \<psi> (f x))"

definition equivar_ind_by_act :: "'z set \<Rightarrow> 'x set \<Rightarrow> ('z, 'x) binary_fun
      \<Rightarrow> ('z, 'y) binary_fun \<Rightarrow> ('x,'y) property" where
  "equivar_ind_by_act Param X \<phi> \<psi> = Equivariance X {(\<phi> g, \<psi> g) | g. g \<in> Param}"

subsection \<open>Auxiliary Lemmas\<close>

lemma bij_imp_bij_on_set_system:
  fixes f :: "'x \<Rightarrow> 'y"
  assumes "bij f"
  shows "bij (\<lambda> \<A>. {f ` A | A. A \<in> \<A>})"
proof (unfold bij_def inj_def surj_def, safe)
  {
    fix
      \<A> :: "'x set set" and
      \<B> :: "'x set set" and
      A :: "'x set"
    assume
      "{f ` A | A. A \<in> \<A>} = {f ` B | B. B \<in> \<B>}" and
      "A \<in> \<A>"
    hence "f ` A \<in> {f ` B | B. B \<in> \<B>}"
      by blast
    then obtain B :: "'x set" where
      el_Y': "B \<in> \<B>" and
      f_B_eq_f_A: "f ` B = f ` A"
      by auto
    hence "the_inv f ` f ` B = the_inv f ` f ` A"
      by simp
    hence "B = A"
      using image_inv_f_f assms f_B_eq_f_A
      unfolding bij_betw_def
      by metis
    thus "A \<in> \<B>"
      using el_Y'
      by simp
  }
  note img_set_eq_imp_subs =
    \<open>\<And> \<A> \<B> A. {f ` A | A. A \<in> \<A>} = {f ` B | B. B \<in> \<B>} \<Longrightarrow> A \<in> \<A> \<Longrightarrow> A \<in> \<B>\<close>
  fix
    \<A> :: "'x set set" and
    \<B> :: "'x set set" and
    A :: "'x set"
  assume 
    "{f ` A | A. A \<in> \<A>} = {f ` B | B. B \<in> \<B>}" and
    "A \<in> \<B>"
  thus "A \<in> \<A>"
    using img_set_eq_imp_subs[of \<B> \<A> A] \<comment> \<open>Symmetry of "="\<close>
    by presburger
next
  fix \<A> :: "'y set set"
  have "\<forall> A. f ` (the_inv f) ` A = A"
    using image_f_inv_f[of f] assms bij_betw_def surj_imp_inv_eq the_inv_f_f
    by metis
  hence "{A | A. A \<in> \<A>} = {f ` (the_inv f) ` A | A. A \<in> \<A>}"
    by presburger
  hence "\<A> = {f ` (the_inv f) ` A | A. A \<in> \<A>}"
    by simp
  also have "{f ` (the_inv f) ` A | A. A \<in> \<A>} =
              {f ` A | A. A \<in> {(the_inv f) ` A | A. A \<in> \<A>}}"
    by blast
  finally show "\<exists> \<B>. \<A> = {f ` B | B. B \<in> \<B>}"
    by blast
qed

lemma un_left_inv_singleton_set_system: "\<Union> \<circ> singleton_set_system = id"
proof
  fix X :: "'x set"
  have "(\<Union> \<circ> singleton_set_system) X = {x. \<exists> x' \<in> singleton_set_system X. x \<in> x'}"
    by auto
  also have "{x. \<exists> x' \<in> singleton_set_system X. x \<in> x'} = {x. {x} \<in> singleton_set_system X}"
    by auto
  also have "{x. {x} \<in> singleton_set_system X} = {x. {x} \<in> {{x} | x. x \<in> X}}"
    by simp
  also have "{x. {x} \<in> {{x} | x. x \<in> X}} = {x. x \<in> X}"
    by simp
  finally show "(\<Union> \<circ> singleton_set_system) X = id X"
    by simp
qed

lemma the_inv_comp:
  fixes
    f :: "'y \<Rightarrow> 'z" and
    g :: "'x \<Rightarrow> 'y" and
    X :: "'x set" and
    Y :: "'y set" and
    Z :: "'z set" and
    z :: "'z"
  assumes
    "bij_betw f Y Z" and
    "bij_betw g X Y" and
    "z \<in> Z"
  shows "the_inv_into X (f \<circ> g) z = ((the_inv_into X g) \<circ> (the_inv_into Y f)) z"
proof (clarsimp)
  have el_Y: "the_inv_into Y f z \<in> Y"
    using assms bij_betw_apply bij_betw_the_inv_into
    by metis
  hence "g (the_inv_into X g (the_inv_into Y f z)) = the_inv_into Y f z"
    using assms f_the_inv_into_f_bij_betw
    by metis
  moreover have "f (the_inv_into Y f z) = z"
    using el_Y assms f_the_inv_into_f_bij_betw
    by metis
  ultimately have "(f \<circ> g) (the_inv_into X g (the_inv_into Y f z)) = z"
    by simp
  hence "the_inv_into X (f \<circ> g) z =
      the_inv_into X (f \<circ> g) ((f \<circ> g) (the_inv_into X g (the_inv_into Y f z)))"
    by presburger
  also have
    "the_inv_into X (f \<circ> g) ((f \<circ> g) (the_inv_into X g (the_inv_into Y f z))) =
      the_inv_into X g (the_inv_into Y f z)"
    using assms bij_betw_apply bij_betw_imp_inj_on bij_betw_the_inv_into bij_betw_trans
          the_inv_into_f_eq
    by meson
  finally show "the_inv_into X (f \<circ> g) z = the_inv_into X g (the_inv_into Y f z)"
    by blast
qed

lemma preimg_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'x \<Rightarrow> 'x" and
    X :: "'x set" and
    y :: "'y"
  shows "preimg f (g ` X) y = g ` preimg (f \<circ> g) X y"
proof (safe)
  fix x :: "'x"
  assume "x \<in> preimg f (g ` X) y"
  hence "f x = y \<and> x \<in> g ` X"
    by simp
  then obtain x' :: "'x" where
    "x' \<in> X" and
    "g x' = x" and
    "x' \<in> preimg (f \<circ> g) X y"
    unfolding comp_def
    by fastforce
  thus "x \<in> g ` preimg (f \<circ> g) X y"
    by blast
next
   fix x :: "'x"
  assume "x \<in> preimg (f \<circ> g) X y"
  hence "f (g x) = y \<and> x \<in> X"
    by simp
  thus "g x \<in> preimg f (g ` X) y"
    by simp
qed

subsection \<open>Rewrite Rules\<close>

theorem rewrite_invar_as_equivar:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    X :: "'x set" and
    G :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows "satisfies f (Invariance (rel_induced_by_action G X \<phi>)) =
            satisfies f (equivar_ind_by_act G X \<phi> (\<lambda> g. id))"
proof (unfold equivar_ind_by_act_def, simp, safe)
  fix
    x :: "'x" and
    g :: "'z"
  assume
    "x \<in> X" and
    "g \<in> G" and
    "\<phi> g x \<in> X" and
    "\<forall> a b. a \<in> X \<and> b \<in> X \<and> (\<exists> x \<in> G. \<phi> x a = b) \<longrightarrow> f a = f b"
  thus "f (\<phi> g x) = id (f x)"
    unfolding id_def
    by metis
next
  fix
    x :: "'x" and
    g :: "'z"
  assume
    x_in_X: "x \<in> X" and
    \<phi>_g_x_in_X: "\<phi> g x \<in> X" and
    g_in_G: "g \<in> G" and
    equivar: "\<forall> a b. (\<exists> g. a = \<phi> g \<and> b = id \<and> g \<in> G) \<longrightarrow>
                (\<forall> x \<in> X. a x \<in> X \<longrightarrow> f (a x) = b (f x))"
  hence "\<phi> g = \<phi> g \<and> id = id \<and> g \<in> G"
    by blast
  hence "\<forall> x \<in> X. \<phi> g x \<in> X \<longrightarrow> f (\<phi> g x) = id (f x)"
    using equivar
    by blast
  thus "f x = f (\<phi> g x)"
    using x_in_X \<phi>_g_x_in_X id_def
    by metis
qed

lemma rewrite_invar_ind_by_act:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    G :: "'z set" and
    X :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows "satisfies f (Invariance (rel_induced_by_action G X \<phi>)) =
          (\<forall> a \<in> X. \<forall> g \<in> G. \<phi> g a \<in> X \<longrightarrow> f a = f (\<phi> g a))"
proof (safe)
  fix
    a :: "'x" and
    g :: "'z"
  assume
    invar: "satisfies f (Invariance (rel_induced_by_action G X \<phi>))" and
    a_in_X: "a \<in> X" and
    g_in_G: "g \<in> G" and
    \<phi>_g_a_in_X: "\<phi> g a \<in> X"
  hence "(a, \<phi> g a) \<in> rel_induced_by_action G X \<phi>"
    unfolding rel_induced_by_action.simps
    by blast
  thus "f a = f (\<phi> g a)"
    using invar
    by simp
next
  assume invar: "\<forall> a \<in> X. \<forall> g \<in> G. \<phi> g a \<in> X \<longrightarrow> f a = f (\<phi> g a)"
  have "\<forall> (a, b) \<in> rel_induced_by_action G X \<phi>. a \<in> X \<and> b \<in> X \<and> (\<exists> g \<in> G. b = \<phi> g a)"
    by auto
  hence "\<forall> (a, b) \<in> rel_induced_by_action G X \<phi>. f a = f b"
    using invar
    by fastforce
  thus "satisfies f (Invariance (rel_induced_by_action G X \<phi>))"
    by simp
qed

lemma rewrite_equivar_ind_by_act:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    G :: "'z set" and
    X :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  shows "satisfies f (equivar_ind_by_act G X \<phi> \<psi>) =
          (\<forall> g \<in> G. \<forall> x \<in> X. \<phi> g x \<in> X \<longrightarrow> f (\<phi> g x) = \<psi> g (f x))"
  unfolding equivar_ind_by_act_def
  by fastforce

lemma rewrite_grp_act_img:
  fixes
    G :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  assumes
    grp_act: "group_action G Y \<phi>"
  shows "\<forall> Z g h. Z \<subseteq> Y \<longrightarrow> g \<in> carrier G \<longrightarrow> h \<in> carrier G \<longrightarrow>
              \<phi> (g \<otimes> \<^bsub>G\<^esub> h) ` Z = \<phi> g ` \<phi> h ` Z"
proof (safe)
  fix
    Z :: "'y set" and
    z :: "'y" and
    g :: "'x" and
    h :: "'x"
  assume
    "g \<in> carrier G" and
    "h \<in> carrier G" and
    z_in_Z: "z \<in> Z" and
    "Z \<subseteq> Y"
  hence eq: "\<phi> (g \<otimes> \<^bsub>G\<^esub> h) z = \<phi> g (\<phi> h z)"
    using grp_act group_action.composition_rule[of G Y]
    by blast
  thus "\<phi> (g \<otimes> \<^bsub>G\<^esub> h) z \<in> \<phi> g ` \<phi> h ` Z"
    using z_in_Z
    by blast
  show "\<phi> g (\<phi> h z) \<in> \<phi> (g \<otimes>\<^bsub>G\<^esub> h) ` Z"
    using z_in_Z eq
    by force
qed

lemma rewrite_sym_group:
  shows
    rewrite_carrier: "carrier (BijGroup UNIV) = {f. bij f}" and
    bij_car_el: "\<And> f. f \<in> carrier (BijGroup UNIV) \<Longrightarrow> bij f" and
    rewrite_mult:
      "\<And> S x y. x \<in> carrier (BijGroup S) \<Longrightarrow>
                  y \<in> carrier (BijGroup S) \<Longrightarrow>
                  x \<otimes> \<^bsub>BijGroup S\<^esub> y = extensional_continuation (x \<circ> y) S" and
    rewrite_mult_univ:
      "\<And> x y. x \<in> carrier (BijGroup UNIV) \<Longrightarrow>
              y \<in> carrier (BijGroup UNIV) \<Longrightarrow>
              x \<otimes> \<^bsub>BijGroup UNIV\<^esub> y = x \<circ> y"
proof -
  show rew: "carrier (BijGroup UNIV) = {f. bij f}"
    unfolding BijGroup_def Bij_def
    by simp
  fix f :: "'b \<Rightarrow> 'b"
  assume "f \<in> carrier (BijGroup UNIV)"
  thus "bij f"
    using rew
    by blast
next
  fix
    S :: "'c set" and
    x :: "'c \<Rightarrow> 'c" and
    y :: "'c \<Rightarrow> 'c"
  assume
    "x \<in> carrier (BijGroup S)" and
    "y \<in> carrier (BijGroup S)"
  thus "x \<otimes> \<^bsub>BijGroup S\<^esub> y = extensional_continuation (x \<circ> y) S"
    unfolding BijGroup_def compose_def comp_def restrict_def
    by simp
next
  fix
    x :: "'d \<Rightarrow> 'd" and
    y :: "'d \<Rightarrow> 'd"
  assume
    "x \<in> carrier (BijGroup UNIV)" and
    "y \<in> carrier (BijGroup UNIV)"
  thus "x \<otimes> \<^bsub>BijGroup UNIV\<^esub> y = x \<circ> y"
    unfolding BijGroup_def compose_def comp_def restrict_def
    by simp
qed

lemma simp_extensional_univ: "extensional_continuation f UNIV = f"
  unfolding If_def
  by simp

lemma extensional_continuation_subset:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    X :: "'x set" and
    Y :: "'x set"
  assumes "Y \<subseteq> X"
  shows "\<forall> y \<in> Y. extensional_continuation f X y = extensional_continuation f Y y"
  using assms
  unfolding subset_iff
  by simp

lemma rel_ind_by_coinciding_action_on_subset_eq_restr:
  fixes
    X :: "'x set" and
    Y :: "'y set" and
    Z :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun" and
    \<phi>' :: "('x, 'y) binary_fun"
  assumes
    "Z \<subseteq> Y" and
    "\<forall> x \<in> X. \<forall> z \<in> Z. \<phi>' x z = \<phi> x z"
  shows "rel_induced_by_action X Z \<phi>' = Restr (rel_induced_by_action X Y \<phi>) Z"
proof (unfold rel_induced_by_action.simps)
  have  "{(y1, y2). (y1, y2) \<in> Z \<times> Z \<and> (\<exists> x \<in> X. \<phi>' x y1 = y2)} =
            {(y1, y2). (y1, y2) \<in> Z \<times> Z \<and> (\<exists> x \<in> X. \<phi> x y1 = y2)}"
    using assms
    by auto
  also have "... = Restr {(y1, y2). (y1, y2) \<in> Y \<times> Y \<and> (\<exists> x \<in> X. \<phi> x y1 = y2)} Z"
    using assms
    by blast
  finally show "{(y1, y2). (y1, y2) \<in> Z \<times> Z \<and> (\<exists> x \<in> X. \<phi>' x y1 = y2)} =
                  Restr {(y1, y2). (y1, y2) \<in> Y \<times> Y \<and> (\<exists> x \<in> X. \<phi> x y1 = y2)} Z"
    by simp
qed

lemma coinciding_actions_ind_equal_rel:
  fixes
    X :: "'x set" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun" and
    \<phi>' :: "('x, 'y) binary_fun"
  assumes "\<forall> x \<in> X. \<forall> y \<in> Y. \<phi> x y = \<phi>' x y"
  shows "rel_induced_by_action X Y \<phi> = rel_induced_by_action X Y \<phi>'"
  unfolding extensional_continuation.simps
  using assms
  by auto

subsection \<open>Group Actions\<close>

lemma const_id_is_grp_act:
  fixes G :: "'x monoid"
  assumes "group G"
  shows "group_action G UNIV (\<lambda> g. id)"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, safe)
  show "group G"
    using assms
    by blast
next
  show "group (BijGroup UNIV)"
    using group_BijGroup
    by metis
next
  show "id \<in> carrier (BijGroup UNIV)"
    unfolding BijGroup_def Bij_def
    by simp
  thus "id = id \<otimes> \<^bsub>BijGroup UNIV\<^esub> id"
    using rewrite_mult_univ comp_id
    by metis
qed

theorem grp_act_induces_set_grp_act:
  fixes
    G :: "'x monoid" and
    Y :: "'y set" and
    \<phi> :: "('x, 'y) binary_fun"
  defines "\<phi>_img \<equiv> (\<lambda> g. extensional_continuation (image (\<phi> g)) (Pow Y))"
  assumes grp_act: "group_action G Y \<phi>"
  shows "group_action G (Pow Y) \<phi>_img"
proof (unfold group_action_def group_hom_def group_hom_axioms_def hom_def, safe)
  show "group G" 
    using assms
    unfolding group_action_def group_hom_def
    by simp
next
  show "group (BijGroup (Pow Y))"
    using group_BijGroup
    by metis
next
  {
    fix
      g :: "'x"
    assume "g \<in> carrier G"
    hence "bij_betw (\<phi> g) Y Y"
      using grp_act group_action.surj_prop
      unfolding bij_betw_def
      by (simp add: group_action.inj_prop)
    hence "bij_betw (image (\<phi> g)) (Pow Y) (Pow Y)"
      using bij_betw_Pow
      by metis
    moreover have "\<forall> A \<in> Pow Y. \<phi>_img g A = image (\<phi> g) A"
      unfolding \<phi>_img_def
      by simp
    ultimately have "bij_betw (\<phi>_img g) (Pow Y) (Pow Y)"
      using bij_betw_cong
      by fastforce
    moreover have "\<phi>_img g \<in> extensional (Pow Y)"
      unfolding \<phi>_img_def extensional_def
      by simp
    ultimately show "\<phi>_img g \<in> carrier (BijGroup (Pow Y))"
      unfolding BijGroup_def Bij_def
      by simp
  }
  note car_el =
    \<open>\<And> g. g \<in> carrier G \<Longrightarrow> \<phi>_img g \<in> carrier (BijGroup (Pow Y))\<close>
  fix
    g :: "'x" and
    h :: "'x"
  assume 
    car_g: "g \<in> carrier G" and
    car_h: "h \<in> carrier G"
  hence car_els: "\<phi>_img g \<in> carrier (BijGroup (Pow Y)) \<and> \<phi>_img h \<in> carrier (BijGroup (Pow Y))"
    using car_el
    by blast
  hence h_closed: "\<forall> A. A \<in> Pow Y \<longrightarrow> \<phi>_img h A \<in> Pow Y"
    using bij_betw_apply Int_Collect partial_object.select_convs(1)
    unfolding BijGroup_def Bij_def
    by metis
  from car_els
  have "\<phi>_img g \<otimes> \<^bsub>BijGroup (Pow Y)\<^esub> \<phi>_img h =
          extensional_continuation (\<phi>_img g \<circ> \<phi>_img h) (Pow Y)"
    using rewrite_mult
    by blast
  moreover have
    "\<forall> A. A \<notin> Pow Y \<longrightarrow> extensional_continuation (\<phi>_img g \<circ> \<phi>_img h) (Pow Y) A = undefined"
    by simp
  moreover have "\<forall> A. A \<notin> Pow Y \<longrightarrow> \<phi>_img (g \<otimes> \<^bsub>G\<^esub> h) A = undefined"
    unfolding \<phi>_img_def
    by simp
  moreover have
    "\<forall> A. A \<in> Pow Y \<longrightarrow> extensional_continuation (\<phi>_img g \<circ> \<phi>_img h) (Pow Y) A = \<phi> g ` \<phi> h ` A"
    using h_closed
    unfolding \<phi>_img_def
    by simp
  moreover have "\<forall> A. A \<in> Pow Y \<longrightarrow> \<phi>_img (g \<otimes> \<^bsub>G\<^esub> h) A = \<phi> g ` \<phi> h ` A"
    unfolding \<phi>_img_def extensional_continuation.simps
    using rewrite_grp_act_img car_g car_h grp_act PowD
    by metis
  ultimately have "\<forall> A. \<phi>_img (g \<otimes> \<^bsub>G\<^esub> h) A = (\<phi>_img g \<otimes> \<^bsub>BijGroup (Pow Y)\<^esub> \<phi>_img h) A"
    by metis
  thus "\<phi>_img (g \<otimes> \<^bsub>G\<^esub> h) = \<phi>_img g \<otimes> \<^bsub>BijGroup (Pow Y)\<^esub> \<phi>_img h"
    by blast
qed

subsection \<open>Invariance and Equivariance\<close>

text \<open>
  It suffices to show invariance under the group action of a generating set of a group
  to show invariance under the group action of the whole group.
  For example, it is enough to show invariance under transpositions to show invariance
  under a complete finite symmetric group.
\<close>

(* TODO Same for monoid actions? Equivariance? *)

theorem invar_generating_system_imp_invar:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    G :: "'z monoid" and
    H :: "'z set" and
    X :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun"
  assumes
    invar: "satisfies f (Invariance (rel_induced_by_action H X \<phi>))" and
    grp_act: "group_action G X \<phi>" and
    gen: "carrier G = generate G H"
  shows "satisfies f (Invariance (rel_induced_by_action (carrier G) X \<phi>))"
proof (unfold satisfies.simps rel_induced_by_action.simps, safe)
  fix
    x :: "'x" and
    g :: "'z"
  assume
    grp_el: "g \<in> carrier G" and
    x_in_X: "x \<in> X"
  interpret grp_act: group_action G X \<phi>
    using grp_act
    by blast
  have "g \<in> generate G H"
    using grp_el gen
    by blast
  hence "\<forall> x \<in> X. f x = f (\<phi> g x)"
  proof (induct g rule: generate.induct)
    case one
    hence "\<forall> x \<in> X. \<phi> \<one> \<^bsub>G\<^esub> x = x"
      using grp_act group_action.id_eq_one restrict_apply
      by metis
    thus "?case"
      by simp
  next
    case (incl g)
    hence "\<forall> x \<in> X. (x, \<phi> g x) \<in> rel_induced_by_action H X \<phi>"
      using gen grp_act generate.incl group_action.element_image
      unfolding rel_induced_by_action.simps
      by fastforce
    thus "?case"
      using invar
      unfolding satisfies.simps
      by blast
  next
    case (inv g)
    hence "\<forall> x \<in> X. \<phi> (inv \<^bsub>G\<^esub> g) x \<in> X"
      using grp_act gen generate.inv group_action.element_image
      by metis
    hence "\<forall> x \<in> X. f (\<phi> g (\<phi> (inv \<^bsub>G\<^esub> g) x)) = f (\<phi> (inv \<^bsub>G\<^esub> g) x)"
      using gen generate.incl group_action.element_image grp_act
            invar local.inv rewrite_invar_ind_by_act
      by metis
    moreover have "\<forall> x \<in> X. \<phi> g (\<phi> (inv\<^bsub>G\<^esub> g) x) = x"
      using grp_act gen generate.incl group.inv_closed group_action.orbit_sym_aux
            group.inv_inv group_hom.axioms(1) grp_act.group_hom local.inv
      by (metis (full_types))
    ultimately show "?case"
      by simp
  next
    case (eng g1 g2)
    assume
      invar1: "\<forall> x \<in> X. f x = f (\<phi> g1 x)" and
      invar2: "\<forall> x \<in> X. f x = f (\<phi> g2 x)" and
      gen1: "g1 \<in> generate G H" and
      gen2: "g2 \<in> generate G H"
    hence "\<forall> x \<in> X. \<phi> g2 x \<in> X"
      using gen grp_act.element_image
      by blast
    hence "\<forall> x \<in> X. f (\<phi> g1 (\<phi> g2 x)) = f (\<phi> g2 x)"
      using invar1
      by simp
    moreover have "\<forall> x \<in> X. f (\<phi> g2 x) = f x"
      using invar2
      by simp
    moreover have "\<forall> x \<in> X. f (\<phi> (g1 \<otimes> \<^bsub>G\<^esub> g2) x) = f (\<phi> g1 (\<phi> g2 x))"
      using grp_act gen grp_act.composition_rule gen1 gen2
      by simp
    ultimately show "?case"
      by simp
  qed
  thus "f x = f (\<phi> g x)"
    using x_in_X
    by simp
qed

lemma invar_parameterized_fun:
  fixes
    f :: "'x \<Rightarrow> ('x \<Rightarrow> 'y)" and
    rel :: "'x rel"
  assumes
    param_invar: "\<forall> x. satisfies (f x) (Invariance rel)" and
    invar: "satisfies f (Invariance rel)"
  shows "satisfies (\<lambda> x. f x x) (Invariance rel)"
  using invar param_invar 
  by auto

lemma invar_under_subset_rel:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    rel' :: "'x rel"
  assumes
    subset: "rel' \<subseteq> rel" and
    invar: "satisfies f (Invariance rel)"
  shows "satisfies f (Invariance rel')"
  using assms
  by auto

lemma equivar_ind_by_act_coincide:
  fixes
    X :: "'x set" and
    Y :: "'y set" and
    f :: "'y \<Rightarrow> 'z" and
    \<phi> :: "('x, 'y) binary_fun" and
    \<phi>' :: "('x, 'y) binary_fun" and
    \<psi> :: "('x, 'z) binary_fun"
  assumes "\<forall> x \<in> X. \<forall> y \<in> Y. \<phi> x y = \<phi>' x y"
  shows "satisfies f (equivar_ind_by_act X Y \<phi> \<psi>) = satisfies f (equivar_ind_by_act X Y \<phi>' \<psi>)"
  using assms
  unfolding rewrite_equivar_ind_by_act
  by simp

lemma equivar_under_subset:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    G :: "'z set" and
    X :: "'x set" and
    Y :: "'x set" and
    Act :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set"
  assumes
    "satisfies f (Equivariance X Act)" and
    "Y \<subseteq> X"
  shows "satisfies f (Equivariance Y Act)"
  using assms
  unfolding satisfies.simps
  by blast

lemma equivar_under_subset':
  fixes
    f :: "'x \<Rightarrow> 'y" and
    G :: "'z set" and
    X :: "'x set" and
    Act :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set" and
    Act' :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set"
  assumes
    "satisfies f (Equivariance X Act)" and
    "Act' \<subseteq> Act"
  shows "satisfies f (Equivariance X Act')"
  using assms
  unfolding satisfies.simps
  by blast

theorem grp_act_equivar_f_imp_equivar_preimg:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    domain\<^sub>f :: "'x set" and
    X :: "'x set" and
    G :: "'z monoid" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun" and
    g :: "'z"
  defines "equivar_prop \<equiv> equivar_ind_by_act (carrier G) domain\<^sub>f \<phi> \<psi>"
  assumes
    grp_act: "group_action G X \<phi>" and
    grp_act_res: "group_action G UNIV \<psi>" and
    dom_in_X: "domain\<^sub>f \<subseteq> X" and
    closed_domain: (* Could the closed_domain requirement be weakened? *)
      "closed_under_restr_rel (rel_induced_by_action (carrier G) X \<phi>) X domain\<^sub>f" and
    equivar_f: "satisfies f equivar_prop" and
    grp_el: "g \<in> carrier G"
  shows "\<forall> y. preimg f domain\<^sub>f (\<psi> g y) = (\<phi> g) ` (preimg f domain\<^sub>f y)"
proof (safe)
  interpret grp_act: group_action G X \<phi>
    using grp_act
    by simp
  interpret grp_act_results: group_action G UNIV \<psi>
    using grp_act_res
    by simp 
  have grp_el_inv: "(inv \<^bsub>G\<^esub> g) \<in> carrier G"
    using group.inv_closed group_hom.axioms(1) grp_act.group_hom grp_el
    by metis
  fix
    y :: "'y" and
    x :: "'x"
  assume preimg_el: "x \<in> preimg f domain\<^sub>f (\<psi> g y)"
  obtain x' where
    img: "x' = \<phi> (inv \<^bsub>G\<^esub> g) x"
    by simp
  have domain: "x \<in> domain\<^sub>f \<and> x \<in> X"
    using preimg_el \<open>domain\<^sub>f \<subseteq> X\<close>
    by auto
  hence "x' \<in> X"
    using dom_in_X grp_act grp_el_inv preimg_el img grp_act.element_image 
    by auto
  hence "(x, x') \<in> (rel_induced_by_action (carrier G) X \<phi>) \<inter> (domain\<^sub>f \<times> X)"
    using img preimg_el domain grp_el_inv
    by auto
  hence "x' \<in> ((rel_induced_by_action (carrier G) X \<phi>) \<inter> (domain\<^sub>f \<times> X)) `` domain\<^sub>f"
    using img preimg_el domain grp_el_inv
    by auto
  hence domain': "x' \<in> domain\<^sub>f"
    using closed_domain
    by auto
  moreover have "(\<phi> (inv \<^bsub>G\<^esub> g), \<psi> (inv \<^bsub>G\<^esub> g)) \<in> {(\<phi> g, \<psi> g) | g. g \<in> carrier G}"
    using grp_el_inv
    by auto
  ultimately have "f x' = \<psi> (inv \<^bsub>G\<^esub> g) (f x)"
    using domain equivar_f img
    unfolding equivar_prop_def equivar_ind_by_act_def
    by simp
  also have "f x = \<psi> g y"
    using preimg_el
    by simp
  also have "\<psi> (inv \<^bsub>G\<^esub> g) (\<psi> g y) = y"
    using grp_act_results.group_hom grp_act_results.orbit_sym_aux grp_el
    by simp
  finally have "f x' = y"
    by simp
  hence "x' \<in> preimg f domain\<^sub>f y"
    using domain'
    by simp
  moreover have "x = \<phi> g x'"
    using group_hom.axioms(1) grp_act.group_hom grp_act.orbit_sym_aux
          img domain domain' grp_el grp_el_inv group.inv_inv
    by metis
  ultimately show "x \<in> (\<phi> g) ` (preimg f domain\<^sub>f y)"
    by simp
next
  fix
    y :: "'y" and
    x :: "'x"
  assume preimg_el: "x \<in> preimg f domain\<^sub>f y"
  hence domain: "f x = y \<and> x \<in> domain\<^sub>f \<and> x \<in> X"
    using dom_in_X
    by auto
  hence "\<phi> g x \<in> X"
    using grp_el group_action.element_image grp_act
    by metis
  hence "(x, \<phi> g x) \<in> (rel_induced_by_action (carrier G) X \<phi>) \<inter> (domain\<^sub>f \<times> X) \<inter> domain\<^sub>f \<times> X"
    using grp_el domain
    by auto
  hence "\<phi> g x \<in> domain\<^sub>f"
    using closed_domain
    by auto
  moreover have "(\<phi> g, \<psi> g) \<in> {(\<phi> g, \<psi> g) | g. g \<in> carrier G}"
    using grp_el
    by blast
  ultimately show "\<phi> g x \<in> preimg f domain\<^sub>f (\<psi> g y)"
    using equivar_f domain
    unfolding equivar_prop_def equivar_ind_by_act_def
    by simp
qed

subsubsection \<open>Invariance and Equivariance Function Composition\<close>

lemma invar_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    rel :: "'x rel"
  assumes "satisfies f (Invariance rel)"
  shows "satisfies (g \<circ> f) (Invariance rel)"
  using assms
  by simp

lemma equivar_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    X :: "'x set" and
    Y :: "'y set" and
    Act_f :: "(('x \<Rightarrow> 'x) \<times> ('y \<Rightarrow> 'y)) set" and
    Act_g :: "(('y \<Rightarrow> 'y) \<times> ('z \<Rightarrow> 'z)) set"
  defines
    "transitive_acts \<equiv>
      {(\<phi>, \<psi>). \<exists> \<psi>' :: 'y \<Rightarrow> 'y. (\<phi>, \<psi>') \<in> Act_f \<and> (\<psi>', \<psi>) \<in> Act_g \<and> \<psi>' ` f ` X \<subseteq> Y}"
  assumes
    "f ` X \<subseteq> Y" and
    "satisfies f (Equivariance X Act_f)" and
    "satisfies g (Equivariance Y Act_g)"
  shows "satisfies (g \<circ> f) (Equivariance X transitive_acts)"
proof (unfold transitive_acts_def, simp, safe)
  fix
    \<phi> :: "'x \<Rightarrow> 'x" and
    \<psi>' :: "'y \<Rightarrow> 'y" and
    \<psi> :: "'z \<Rightarrow> 'z" and
    x :: "'x"
  assume
    x_in_X: "x \<in> X" and
    \<phi>_x_in_X: "\<phi> x \<in> X" and
    "\<psi>' ` f ` X \<subseteq> Y" and
    act_f: "(\<phi>, \<psi>') \<in> Act_f" and
    act_g: "(\<psi>', \<psi>) \<in> Act_g"
  hence "f x \<in> Y \<and> \<psi>' (f x) \<in> Y"
    using assms
    by blast
  hence "\<psi> (g (f x)) = g (\<psi>' (f x))"
    using act_g assms
    by fastforce
  also have "g (f (\<phi> x)) = g (\<psi>' (f x))"
    using assms act_f x_in_X \<phi>_x_in_X
    by fastforce
  finally show "g (f (\<phi> x)) = \<psi> (g (f x))"
    by simp
qed

lemma equivar_ind_by_act_comp:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    g :: "'y \<Rightarrow> 'z" and
    G :: "'w set" and
    X :: "'x set" and
    Y :: "'y set" and
    \<phi> :: "('w, 'x) binary_fun" and
    \<psi>' :: "('w, 'y) binary_fun" and
    \<psi> :: "('w, 'z) binary_fun"
  assumes
    "f ` X \<subseteq> Y" and
    "\<forall> g \<in> G. \<psi>' g ` f ` X \<subseteq> Y" and
    "satisfies f (equivar_ind_by_act G X \<phi> \<psi>')" and
    "satisfies g (equivar_ind_by_act G Y \<psi>' \<psi>)"
  shows "satisfies (g \<circ> f) (equivar_ind_by_act G X \<phi> \<psi>)"
proof -
  let ?Act_f = "{(\<phi> g, \<psi>' g) | g. g \<in> G}" and
      ?Act_g = "{(\<psi>' g, \<psi> g) | g. g \<in> G}"
  have "\<forall> g \<in> G. (\<phi> g, \<psi>' g) \<in> {(\<phi> g, \<psi>' g) |g. g \<in> G} \<and>
                  (\<psi>' g, \<psi> g) \<in> {(\<psi>' g, \<psi> g) |g. g \<in> G} \<and> \<psi>' g ` f ` X \<subseteq> Y"
    using assms
    by blast
  hence "{(\<phi> g, \<psi> g) | g. g \<in> G} \<subseteq>
          {(\<phi>, \<psi>). \<exists>\<psi>'. (\<phi>, \<psi>') \<in> ?Act_f \<and> (\<psi>', \<psi>) \<in> ?Act_g \<and> \<psi>' ` f ` X \<subseteq> Y}"
    by blast
  hence "satisfies (g \<circ> f) (Equivariance X {(\<phi> g, \<psi> g) | g. g \<in> G})"
    using assms equivar_comp[of f X Y ?Act_f g ?Act_g] equivar_under_subset'
    unfolding equivar_ind_by_act_def
    by (metis (no_types, lifting))
  thus ?thesis
    unfolding equivar_ind_by_act_def
    by blast
qed

lemma equivar_set_minus:
  fixes
    f :: "'x \<Rightarrow> 'y set" and
    h :: "'x \<Rightarrow> 'y set" and
    G :: "'z set" and
    X :: "'x set" and
    \<phi> :: "('z, 'x) binary_fun" and
    \<psi> :: "('z, 'y) binary_fun"
  assumes
    "satisfies f (equivar_ind_by_act G X \<phi> (set_action \<psi>))" and 
    "satisfies h (equivar_ind_by_act G X \<phi> (set_action \<psi>))" and
    "\<forall> g \<in> G. bij (\<psi> g)"
  shows "satisfies (\<lambda> x. f x - h x) (equivar_ind_by_act G X \<phi> (set_action \<psi>))"
proof -
  have "\<forall> g \<in> G. \<forall> x \<in> X. \<phi> g x \<in> X \<longrightarrow> f (\<phi> g x) = \<psi> g ` (f x)"
    using assms
    unfolding rewrite_equivar_ind_by_act
    by simp
  moreover have "\<forall> g \<in> G. \<forall> x \<in> X. \<phi> g x \<in> X \<longrightarrow> h (\<phi> g x) = \<psi> g ` (h x)"
    using assms
    unfolding rewrite_equivar_ind_by_act
    by simp
  ultimately have
    "\<forall> g \<in> G. \<forall> x \<in> X. \<phi> g x \<in> X \<longrightarrow> f (\<phi> g x) - h (\<phi> g x) = \<psi> g ` (f x) - \<psi> g ` (h x)"
    by blast
  moreover have "\<forall> g \<in> G. \<forall> A B. \<psi> g ` A - \<psi> g ` B = \<psi> g ` (A - B)"
    using assms image_set_diff
    unfolding bij_def
    by blast
  ultimately show ?thesis
    unfolding set_action.simps
    using rewrite_equivar_ind_by_act
    by fastforce
qed

lemma equivar_union_under_img_act:
  fixes
    f :: "'x \<Rightarrow> 'y" and
    G :: "'z set" and
    \<phi> :: "('z, 'x) binary_fun"
  shows
    "satisfies \<Union> (equivar_ind_by_act G UNIV
              (set_action (set_action \<phi>)) (set_action \<phi>))"
proof (unfold equivar_ind_by_act_def, clarsimp, safe)
  fix
    g :: "'z" and
    \<X> :: "'x set set" and
    X :: "'x set" and
    x :: "'x"
  assume
    x_in_X: "x \<in> X" and
    X_in_set_X: "X \<in> \<X>" and
    "g \<in> G"
  thus "\<phi> g x \<in> \<phi> g ` \<Union> \<X>"
    by blast
  have "\<phi> g ` X \<in> (`) (\<phi> g) ` \<X>"
    using X_in_set_X
    by simp
  thus "\<phi> g x \<in> \<Union> ((`) (\<phi> g) ` \<X>)"
    using x_in_X
    by blast
qed

end